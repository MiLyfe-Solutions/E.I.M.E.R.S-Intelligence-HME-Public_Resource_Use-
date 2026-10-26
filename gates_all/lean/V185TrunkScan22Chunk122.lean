import V185TrunkScan22Chunk121

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1091525 : List Nat := [1, 3, 1, 1, 1, 1, 1, 13]
def baseStart_1091525 : Nat := 118140960795 + 1091525 * 2 ^ 59
def prefixEnd_1091525 : Nat := 4983230072969 + 3 ^ 40 * 1091525 * 2
def baseEnd_1091525 : Nat := 41516812696218306453161

theorem tailTrace_1091525 : CollatzResearch.WordTrace tailWord_1091525 prefixEnd_1091525 41516812696218306453161 := by
  unfold tailWord_1091525
  simp only [CollatzResearch.WordTrace]
  refine ⟨39811187370598817473644029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26540791580399211649096019 39811187370598817473644029)
  ·
    refine ⟨14929195263974556552616511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39811187370598817473644029 14929195263974556552616511)
    ·
      refine ⟨22393792895961834828924767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14929195263974556552616511 22393792895961834828924767)
      ·
        refine ⟨33590689343942752243387151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22393792895961834828924767 33590689343942752243387151)
        ·
          refine ⟨50386034015914128365080727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33590689343942752243387151 50386034015914128365080727)
          ·
            refine ⟨75579051023871192547621091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50386034015914128365080727 75579051023871192547621091)
            ·
              refine ⟨113368576535806788821431637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75579051023871192547621091 113368576535806788821431637)
              ·
                refine ⟨41516812696218306453161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 113368576535806788821431637 41516812696218306453161)
                ·
                  rfl

theorem cell22_1091525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 13].length) (baseStart_1091525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091525 prefixEnd_1091525 := by exact prefixLift 1091525
  have htrace : WordTrace (prefixWord ++ tailWord_1091525) baseStart_1091525 baseEnd_1091525 := by
    simpa [prefixWord, tailWord_1091525, baseEnd_1091525] using wordTrace_append hprefix tailTrace_1091525
  have hstable : (prefixWord ++ tailWord_1091525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091525).length < 2 ^ (prefixWord ++ tailWord_1091525).sum := by decide
  have hdescent : baseEnd_1091525 < baseStart_1091525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091587 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 5]
def baseStart_1091587 : Nat := 118140960795 + 1091587 * 2 ^ 59
def prefixEnd_1091587 : Nat := 4983230072969 + 3 ^ 40 * 1091587 * 2
def baseEnd_1091587 : Nat := 124557512711005754342753

theorem tailTrace_1091587 : CollatzResearch.WordTrace tailWord_1091587 prefixEnd_1091587 124557512711005754342753 := by
  unfold tailWord_1091587
  simp only [CollatzResearch.WordTrace]
  refine ⟨39813448696374202062401015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26542299130916134708267343 39813448696374202062401015)
  ·
    refine ⟨59720173044561303093601523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39813448696374202062401015 59720173044561303093601523)
    ·
      refine ⟨89580259566841954640402285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59720173044561303093601523 89580259566841954640402285)
      ·
        refine ⟨33592597337565732990150857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89580259566841954640402285 33592597337565732990150857)
        ·
          refine ⟨25194448003174299742613143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33592597337565732990150857 25194448003174299742613143)
          ·
            refine ⟨37791672004761449613919715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25194448003174299742613143 37791672004761449613919715)
            ·
              refine ⟨56687508007142174420879573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37791672004761449613919715 56687508007142174420879573)
              ·
                refine ⟨1328613468917394712989365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56687508007142174420879573 1328613468917394712989365)
                ·
                  refine ⟨124557512711005754342753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1328613468917394712989365 124557512711005754342753)
                  ·
                    rfl

theorem cell22_1091587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 5].length) (baseStart_1091587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091587 prefixEnd_1091587 := by exact prefixLift 1091587
  have htrace : WordTrace (prefixWord ++ tailWord_1091587) baseStart_1091587 baseEnd_1091587 := by
    simpa [prefixWord, tailWord_1091587, baseEnd_1091587] using wordTrace_append hprefix tailTrace_1091587
  have hstable : (prefixWord ++ tailWord_1091587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091587).length < 2 ^ (prefixWord ++ tailWord_1091587).sum := by decide
  have hdescent : baseEnd_1091587 < baseStart_1091587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091713 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1091713 : Nat := 118140960795 + 1091713 * 2 ^ 59
def prefixEnd_1091713 : Nat := 4983230072969 + 3 ^ 40 * 1091713 * 2
def baseEnd_1091713 : Nat := 373715670507994934377873

theorem tailTrace_1091713 : CollatzResearch.WordTrace tailWord_1091713 prefixEnd_1091713 373715670507994934377873 := by
  unfold tailWord_1091713
  simp only [CollatzResearch.WordTrace]
  refine ⟨39818044293917725581487793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26545362862611817054325195 39818044293917725581487793)
  ·
    refine ⟨29863533220438294186115845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39818044293917725581487793 29863533220438294186115845)
    ·
      refine ⟨5599412478832180159896721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29863533220438294186115845 5599412478832180159896721)
      ·
        refine ⟨4199559359124135119922541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5599412478832180159896721 4199559359124135119922541)
        ·
          refine ⟨1574834759671550669970953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4199559359124135119922541 1574834759671550669970953)
          ·
            refine ⟨1181126069753663002478215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574834759671550669970953 1181126069753663002478215)
            ·
              refine ⟨1771689104630494503717323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181126069753663002478215 1771689104630494503717323)
              ·
                refine ⟨2657533656945741755575985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771689104630494503717323 2657533656945741755575985)
                ·
                  refine ⟨1993150242709306316681989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2657533656945741755575985 1993150242709306316681989)
                  ·
                    refine ⟨373715670507994934377873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993150242709306316681989 373715670507994934377873)
                    ·
                      rfl

theorem cell22_1091713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1091713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091713 prefixEnd_1091713 := by exact prefixLift 1091713
  have htrace : WordTrace (prefixWord ++ tailWord_1091713) baseStart_1091713 baseEnd_1091713 := by
    simpa [prefixWord, tailWord_1091713, baseEnd_1091713] using wordTrace_append hprefix tailTrace_1091713
  have hstable : (prefixWord ++ tailWord_1091713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091713).length < 2 ^ (prefixWord ++ tailWord_1091713).sum := by decide
  have hdescent : baseEnd_1091713 < baseStart_1091713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091732 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1091732 : Nat := 118140960795 + 1091732 * 2 ^ 59
def prefixEnd_1091732 : Nat := 4983230072969 + 3 ^ 40 * 1091732 * 2
def baseEnd_1091732 : Nat := 373722174596285218152815

theorem tailTrace_1091732 : CollatzResearch.WordTrace tailWord_1091732 prefixEnd_1091732 373722174596285218152815 := by
  unfold tailWord_1091732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19909368640424445913214725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26545824853899261217619633 19909368640424445913214725)
  ·
    refine ⟨3733006620079583608727761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19909368640424445913214725 3733006620079583608727761)
    ·
      refine ⟨2799754965059687706545821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3733006620079583608727761 2799754965059687706545821)
      ·
        refine ⟨1049908111897382889954683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2799754965059687706545821 1049908111897382889954683)
        ·
          refine ⟨1574862167846074334932025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049908111897382889954683 1574862167846074334932025)
          ·
            refine ⟨1181146625884555751199019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574862167846074334932025 1181146625884555751199019)
            ·
              refine ⟨1771719938826833626798529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181146625884555751199019 1771719938826833626798529)
              ·
                refine ⟨1328789954120125220098897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771719938826833626798529 1328789954120125220098897)
                ·
                  refine ⟨996592465590093915074173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328789954120125220098897 996592465590093915074173)
                  ·
                    refine ⟨373722174596285218152815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 996592465590093915074173 373722174596285218152815)
                    ·
                      rfl

theorem cell22_1091732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1091732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091732 prefixEnd_1091732 := by exact prefixLift 1091732
  have htrace : WordTrace (prefixWord ++ tailWord_1091732) baseStart_1091732 baseEnd_1091732 := by
    simpa [prefixWord, tailWord_1091732, baseEnd_1091732] using wordTrace_append hprefix tailTrace_1091732
  have hstable : (prefixWord ++ tailWord_1091732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091732).length < 2 ^ (prefixWord ++ tailWord_1091732).sum := by decide
  have hdescent : baseEnd_1091732 < baseStart_1091732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091743 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 3, 3]
def baseStart_1091743 : Nat := 118140960795 + 1091743 * 2 ^ 59
def prefixEnd_1091743 : Nat := 4983230072969 + 3 ^ 40 * 1091743 * 2
def baseEnd_1091743 : Nat := 373725940121084856127781

theorem tailTrace_1091743 : CollatzResearch.WordTrace tailWord_1091743 prefixEnd_1091743 373725940121084856127781 := by
  unfold tailWord_1091743
  simp only [CollatzResearch.WordTrace]
  refine ⟨39819138483809040705079883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26546092322539360470053255 39819138483809040705079883)
  ·
    refine ⟨59728707725713561057619825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39819138483809040705079883 59728707725713561057619825)
    ·
      refine ⟨44796530794285170793214869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59728707725713561057619825 44796530794285170793214869)
      ·
        refine ⟨2099837380982117380931947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44796530794285170793214869 2099837380982117380931947)
        ·
          refine ⟨3149756071473176071397921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099837380982117380931947 3149756071473176071397921)
          ·
            refine ⟨2362317053604882053548441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149756071473176071397921 2362317053604882053548441)
            ·
              refine ⟨1771737790203661540161331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2362317053604882053548441 1771737790203661540161331)
              ·
                refine ⟨2657606685305492310241997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771737790203661540161331 2657606685305492310241997)
                ·
                  refine ⟨996602506989559616340749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2657606685305492310241997 996602506989559616340749)
                  ·
                    refine ⟨373725940121084856127781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 996602506989559616340749 373725940121084856127781)
                    ·
                      rfl

theorem cell22_1091743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_1091743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091743 prefixEnd_1091743 := by exact prefixLift 1091743
  have htrace : WordTrace (prefixWord ++ tailWord_1091743) baseStart_1091743 baseEnd_1091743 := by
    simpa [prefixWord, tailWord_1091743, baseEnd_1091743] using wordTrace_append hprefix tailTrace_1091743
  have hstable : (prefixWord ++ tailWord_1091743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091743).length < 2 ^ (prefixWord ++ tailWord_1091743).sum := by decide
  have hdescent : baseEnd_1091743 < baseStart_1091743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091786 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_1091786 : Nat := 118140960795 + 1091786 * 2 ^ 59
def prefixEnd_1091786 : Nat := 4983230072969 + 3 ^ 40 * 1091786 * 2
def baseEnd_1091786 : Nat := 373740659899847077302649

theorem tailTrace_1091786 : CollatzResearch.WordTrace tailWord_1091786 prefixEnd_1091786 373740659899847077302649 := by
  unfold tailWord_1091786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955176705663314762223803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26547137881768839365930141 9955176705663314762223803)
  ·
    refine ⟨14932765058494972143335705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9955176705663314762223803 14932765058494972143335705)
    ·
      refine ⟨11199573793871229107501779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14932765058494972143335705 11199573793871229107501779)
      ·
        refine ⟨16799360690806843661252669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11199573793871229107501779 16799360690806843661252669)
        ·
          refine ⟨6299760259052566372969751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16799360690806843661252669 6299760259052566372969751)
          ·
            refine ⟨9449640388578849559454627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6299760259052566372969751 9449640388578849559454627)
            ·
              refine ⟨14174460582868274339181941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9449640388578849559454627 14174460582868274339181941)
              ·
                refine ⟨1328855679643900719298307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14174460582868274339181941 1328855679643900719298307)
                ·
                  refine ⟨1993283519465851078947461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328855679643900719298307 1993283519465851078947461)
                  ·
                    refine ⟨373740659899847077302649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993283519465851078947461 373740659899847077302649)
                    ·
                      rfl

theorem cell22_1091786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_1091786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091786 prefixEnd_1091786 := by exact prefixLift 1091786
  have htrace : WordTrace (prefixWord ++ tailWord_1091786) baseStart_1091786 baseEnd_1091786 := by
    simpa [prefixWord, tailWord_1091786, baseEnd_1091786] using wordTrace_append hprefix tailTrace_1091786
  have hstable : (prefixWord ++ tailWord_1091786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091786).length < 2 ^ (prefixWord ++ tailWord_1091786).sum := by decide
  have hdescent : baseEnd_1091786 < baseStart_1091786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091801 : List Nat := [1, 2, 1, 2, 3, 1, 2, 6, 4]
def baseStart_1091801 : Nat := 118140960795 + 1091801 * 2 ^ 59
def prefixEnd_1091801 : Nat := 4983230072969 + 3 ^ 40 * 1091801 * 2
def baseEnd_1091801 : Nat := 124581931568797346059201

theorem tailTrace_1091801 : CollatzResearch.WordTrace tailWord_1091801 prefixEnd_1091801 124581931568797346059201 := by
  unfold tailWord_1091801
  simp only [CollatzResearch.WordTrace]
  refine ⟨39821253917598916610691257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26547502611732611073794171 39821253917598916610691257)
  ·
    refine ⟨29865940438199187458018443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39821253917598916610691257 29865940438199187458018443)
    ·
      refine ⟨44798910657298781187027665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29865940438199187458018443 44798910657298781187027665)
      ·
        refine ⟨33599182992974085890270749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44798910657298781187027665 33599182992974085890270749)
        ·
          refine ⟨12599693622365282208851531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33599182992974085890270749 12599693622365282208851531)
          ·
            refine ⟨18899540433547923313277297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12599693622365282208851531 18899540433547923313277297)
            ·
              refine ⟨14174655325160942484957973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18899540433547923313277297 14174655325160942484957973)
              ·
                refine ⟨664436968366919178982405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14174655325160942484957973 664436968366919178982405)
                ·
                  refine ⟨124581931568797346059201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664436968366919178982405 124581931568797346059201)
                  ·
                    rfl

theorem cell22_1091801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_1091801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091801 prefixEnd_1091801 := by exact prefixLift 1091801
  have htrace : WordTrace (prefixWord ++ tailWord_1091801) baseStart_1091801 baseEnd_1091801 := by
    simpa [prefixWord, tailWord_1091801, baseEnd_1091801] using wordTrace_append hprefix tailTrace_1091801
  have hstable : (prefixWord ++ tailWord_1091801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091801).length < 2 ^ (prefixWord ++ tailWord_1091801).sum := by decide
  have hdescent : baseEnd_1091801 < baseStart_1091801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091882 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1091882 : Nat := 118140960795 + 1091882 * 2 ^ 59
def prefixEnd_1091882 : Nat := 4983230072969 + 3 ^ 40 * 1091882 * 2
def baseEnd_1091882 : Nat := 373773522661734826902355

theorem tailTrace_1091882 : CollatzResearch.WordTrace tailWord_1091882 prefixEnd_1091882 373773522661734826902355 := by
  unfold tailWord_1091882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956052057576366861097475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26549472153536978296259933 9956052057576366861097475)
  ·
    refine ⟨14934078086364550291646213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9956052057576366861097475 14934078086364550291646213)
    ·
      refine ⟨2800139641193353179683665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14934078086364550291646213 2800139641193353179683665)
      ·
        refine ⟨2100104730895014884762749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2800139641193353179683665 2100104730895014884762749)
        ·
          refine ⟨787539274085630581786031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2100104730895014884762749 787539274085630581786031)
          ·
            refine ⟨1181308911128445872679047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787539274085630581786031 1181308911128445872679047)
            ·
              refine ⟨1771963366692668809018571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181308911128445872679047 1771963366692668809018571)
              ·
                refine ⟨2657945050039003213527857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771963366692668809018571 2657945050039003213527857)
                ·
                  refine ⟨1993458787529252410145893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2657945050039003213527857 1993458787529252410145893)
                  ·
                    refine ⟨373773522661734826902355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993458787529252410145893 373773522661734826902355)
                    ·
                      rfl

theorem cell22_1091882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1091882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091882 prefixEnd_1091882 := by exact prefixLift 1091882
  have htrace : WordTrace (prefixWord ++ tailWord_1091882) baseStart_1091882 baseEnd_1091882 := by
    simpa [prefixWord, tailWord_1091882, baseEnd_1091882] using wordTrace_append hprefix tailTrace_1091882
  have hstable : (prefixWord ++ tailWord_1091882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091882).length < 2 ^ (prefixWord ++ tailWord_1091882).sum := by decide
  have hdescent : baseEnd_1091882 < baseStart_1091882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091925 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 5]
def baseStart_1091925 : Nat := 118140960795 + 1091925 * 2 ^ 59
def prefixEnd_1091925 : Nat := 4983230072969 + 3 ^ 40 * 1091925 * 2
def baseEnd_1091925 : Nat := 124596080813499016025741

theorem tailTrace_1091925 : CollatzResearch.WordTrace tailWord_1091925 prefixEnd_1091925 124596080813499016025741 := by
  unfold tailWord_1091925
  simp only [CollatzResearch.WordTrace]
  refine ⟨39825776569149685788205229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26550517712766457192136819 39825776569149685788205229)
  ·
    refine ⟨14934666213431132170576961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39825776569149685788205229 14934666213431132170576961)
    ·
      refine ⟨11200999660073349127932721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14934666213431132170576961 11200999660073349127932721)
      ·
        refine ⟨8400749745055011845949541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11200999660073349127932721 8400749745055011845949541)
        ·
          refine ⟨1575140577197814721115539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8400749745055011845949541 1575140577197814721115539)
          ·
            refine ⟨2362710865796722081673309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575140577197814721115539 2362710865796722081673309)
            ·
              refine ⟨886016574673770780627491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2362710865796722081673309 886016574673770780627491)
              ·
                refine ⟨1329024862010656170941237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886016574673770780627491 1329024862010656170941237)
                ·
                  refine ⟨124596080813499016025741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329024862010656170941237 124596080813499016025741)
                  ·
                    rfl

theorem cell22_1091925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_1091925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1091925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1091925 prefixEnd_1091925 := by exact prefixLift 1091925
  have htrace : WordTrace (prefixWord ++ tailWord_1091925) baseStart_1091925 baseEnd_1091925 := by
    simpa [prefixWord, tailWord_1091925, baseEnd_1091925] using wordTrace_append hprefix tailTrace_1091925
  have hstable : (prefixWord ++ tailWord_1091925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091925).length < 2 ^ (prefixWord ++ tailWord_1091925).sum := by decide
  have hdescent : baseEnd_1091925 < baseStart_1091925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092026 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_1092026 : Nat := 118140960795 + 1092026 * 2 ^ 59
def prefixEnd_1092026 : Nat := 4983230072969 + 3 ^ 40 * 1092026 * 2
def baseEnd_1092026 : Nat := 124607605601522150433971

theorem tailTrace_1092026 : CollatzResearch.WordTrace tailWord_1092026 prefixEnd_1092026 124607605601522150433971 := by
  unfold tailWord_1092026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9957365085445945009407983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26552973561189186691754621 9957365085445945009407983)
  ·
    refine ⟨14936047628168917514111975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9957365085445945009407983 14936047628168917514111975)
    ·
      refine ⟨22404071442253376271167963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14936047628168917514111975 22404071442253376271167963)
      ·
        refine ⟨33606107163380064406751945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22404071442253376271167963 33606107163380064406751945)
        ·
          refine ⟨25204580372535048305063959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33606107163380064406751945 25204580372535048305063959)
          ·
            refine ⟨37806870558802572457595939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25204580372535048305063959 37806870558802572457595939)
            ·
              refine ⟨56710305838203858686393909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37806870558802572457595939 56710305838203858686393909)
              ·
                refine ⟨5316591172331611751849429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56710305838203858686393909 5316591172331611751849429)
                ·
                  refine ⟨124607605601522150433971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5316591172331611751849429 124607605601522150433971)
                  ·
                    rfl

theorem cell22_1092026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_1092026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092026 prefixEnd_1092026 := by exact prefixLift 1092026
  have htrace : WordTrace (prefixWord ++ tailWord_1092026) baseStart_1092026 baseEnd_1092026 := by
    simpa [prefixWord, tailWord_1092026, baseEnd_1092026] using wordTrace_append hprefix tailTrace_1092026
  have hstable : (prefixWord ++ tailWord_1092026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092026).length < 2 ^ (prefixWord ++ tailWord_1092026).sum := by decide
  have hdescent : baseEnd_1092026 < baseStart_1092026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092028 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1092028 : Nat := 118140960795 + 1092028 * 2 ^ 59
def prefixEnd_1092028 : Nat := 4983230072969 + 3 ^ 40 * 1092028 * 2
def baseEnd_1092028 : Nat := 373823501445439112751907

theorem tailTrace_1092028 : CollatzResearch.WordTrace tailWord_1092028 prefixEnd_1092028 373823501445439112751907 := by
  unfold tailWord_1092028
  simp only [CollatzResearch.WordTrace]
  refine ⟨19914766643888267189602369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26553022191851022919469825 19914766643888267189602369)
  ·
    refine ⟨14936074982916200392201777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19914766643888267189602369 14936074982916200392201777)
    ·
      refine ⟨11202056237187150294151333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14936074982916200392201777 11202056237187150294151333)
      ·
        refine ⟨2100385544472590680153375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11202056237187150294151333 2100385544472590680153375)
        ·
          refine ⟨3150578316708886020230063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2100385544472590680153375 3150578316708886020230063)
          ·
            refine ⟨4725867475063329030345095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150578316708886020230063 4725867475063329030345095)
            ·
              refine ⟨7088801212594993545517643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4725867475063329030345095 7088801212594993545517643)
              ·
                refine ⟨10633201818892490318276465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7088801212594993545517643 10633201818892490318276465)
                ·
                  refine ⟨7974901364169367738707349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10633201818892490318276465 7974901364169367738707349)
                  ·
                    refine ⟨373823501445439112751907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7974901364169367738707349 373823501445439112751907)
                    ·
                      rfl

theorem cell22_1092028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1092028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092028 prefixEnd_1092028 := by exact prefixLift 1092028
  have htrace : WordTrace (prefixWord ++ tailWord_1092028) baseStart_1092028 baseEnd_1092028 := by
    simpa [prefixWord, tailWord_1092028, baseEnd_1092028] using wordTrace_append hprefix tailTrace_1092028
  have hstable : (prefixWord ++ tailWord_1092028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092028).length < 2 ^ (prefixWord ++ tailWord_1092028).sum := by decide
  have hdescent : baseEnd_1092028 < baseStart_1092028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092041 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_1092041 : Nat := 118140960795 + 1092041 * 2 ^ 59
def prefixEnd_1092041 : Nat := 4983230072969 + 3 ^ 40 * 1092041 * 2
def baseEnd_1092041 : Nat := 373827951611111412176867

theorem tailTrace_1092041 : CollatzResearch.WordTrace tailWord_1092041 prefixEnd_1092041 373827951611111412176867 := by
  unfold tailWord_1092041
  simp only [CollatzResearch.WordTrace]
  refine ⟨39830007436729437599427977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26553338291152958399618651 39830007436729437599427977)
  ·
    refine ⟨29872505577547078199570983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39830007436729437599427977 29872505577547078199570983)
    ·
      refine ⟨44808758366320617299356475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29872505577547078199570983 44808758366320617299356475)
      ·
        refine ⟨67213137549480925949034713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44808758366320617299356475 67213137549480925949034713)
        ·
          refine ⟨50409853162110694461776035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67213137549480925949034713 50409853162110694461776035)
          ·
            refine ⟨75614779743166041692664053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50409853162110694461776035 75614779743166041692664053)
            ·
              refine ⟨7088885600921816408687255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75614779743166041692664053 7088885600921816408687255)
              ·
                refine ⟨10633328401382724613030883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7088885600921816408687255 10633328401382724613030883)
                ·
                  refine ⟨15949992602074086919546325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10633328401382724613030883 15949992602074086919546325)
                  ·
                    refine ⟨373827951611111412176867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15949992602074086919546325 373827951611111412176867)
                    ·
                      rfl

theorem cell22_1092041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_1092041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092041 prefixEnd_1092041 := by exact prefixLift 1092041
  have htrace : WordTrace (prefixWord ++ tailWord_1092041) baseStart_1092041 baseEnd_1092041 := by
    simpa [prefixWord, tailWord_1092041, baseEnd_1092041] using wordTrace_append hprefix tailTrace_1092041
  have hstable : (prefixWord ++ tailWord_1092041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092041).length < 2 ^ (prefixWord ++ tailWord_1092041).sum := by decide
  have hdescent : baseEnd_1092041 < baseStart_1092041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092077 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 5]
def baseStart_1092077 : Nat := 118140960795 + 1092077 * 2 ^ 59
def prefixEnd_1092077 : Nat := 4983230072969 + 3 ^ 40 * 1092077 * 2
def baseEnd_1092077 : Nat := 124613425048939772758919

theorem tailTrace_1092077 : CollatzResearch.WordTrace tailWord_1092077 prefixEnd_1092077 124613425048939772758919 := by
  unfold tailWord_1092077
  simp only [CollatzResearch.WordTrace]
  refine ⟨39831320464599015747738485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26554213643066010498492323 39831320464599015747738485)
  ·
    refine ⟨3734186293556157726350483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39831320464599015747738485 3734186293556157726350483)
    ·
      refine ⟨5601279440334236589525725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734186293556157726350483 5601279440334236589525725)
      ·
        refine ⟨2100479790125338721072147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5601279440334236589525725 2100479790125338721072147)
        ·
          refine ⟨3150719685188008081608221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2100479790125338721072147 3150719685188008081608221)
          ·
            refine ⟨1181519881945503030603083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3150719685188008081608221 1181519881945503030603083)
            ·
              refine ⟨1772279822918254545904625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181519881945503030603083 1772279822918254545904625)
              ·
                refine ⟨1329209867188690909428469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772279822918254545904625 1329209867188690909428469)
                ·
                  refine ⟨124613425048939772758919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329209867188690909428469 124613425048939772758919)
                  ·
                    rfl

theorem cell22_1092077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_1092077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092077 prefixEnd_1092077 := by exact prefixLift 1092077
  have htrace : WordTrace (prefixWord ++ tailWord_1092077) baseStart_1092077 baseEnd_1092077 := by
    simpa [prefixWord, tailWord_1092077, baseEnd_1092077] using wordTrace_append hprefix tailTrace_1092077
  have hstable : (prefixWord ++ tailWord_1092077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092077).length < 2 ^ (prefixWord ++ tailWord_1092077).sum := by decide
  have hdescent : baseEnd_1092077 < baseStart_1092077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092088 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 6]
def baseStart_1092088 : Nat := 118140960795 + 1092088 * 2 ^ 59
def prefixEnd_1092088 : Nat := 4983230072969 + 3 ^ 40 * 1092088 * 2
def baseEnd_1092088 : Nat := 124614680223872985417241

theorem tailTrace_1092088 : CollatzResearch.WordTrace tailWord_1092088 prefixEnd_1092088 124614680223872985417241 := by
  unfold tailWord_1092088
  simp only [CollatzResearch.WordTrace]
  refine ⟨19915860833779582313194459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26554481111706109750925945 19915860833779582313194459)
  ·
    refine ⟨29873791250669373469791689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19915860833779582313194459 29873791250669373469791689)
    ·
      refine ⟨22405343438002030102343767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29873791250669373469791689 22405343438002030102343767)
      ·
        refine ⟨33608015157003045153515651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22405343438002030102343767 33608015157003045153515651)
        ·
          refine ⟨50412022735504567730273477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33608015157003045153515651 50412022735504567730273477)
          ·
            refine ⟨9452254262907106449426277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50412022735504567730273477 9452254262907106449426277)
            ·
              refine ⟨1772297674295082459267427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9452254262907106449426277 1772297674295082459267427)
              ·
                refine ⟨2658446511442623688901141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772297674295082459267427 2658446511442623688901141)
                ·
                  refine ⟨124614680223872985417241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2658446511442623688901141 124614680223872985417241)
                  ·
                    rfl

theorem cell22_1092088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_1092088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092088 prefixEnd_1092088 := by exact prefixLift 1092088
  have htrace : WordTrace (prefixWord ++ tailWord_1092088) baseStart_1092088 baseEnd_1092088 := by
    simpa [prefixWord, tailWord_1092088, baseEnd_1092088] using wordTrace_append hprefix tailTrace_1092088
  have hstable : (prefixWord ++ tailWord_1092088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092088).length < 2 ^ (prefixWord ++ tailWord_1092088).sum := by decide
  have hdescent : baseEnd_1092088 < baseStart_1092088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092120 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 4, 3]
def baseStart_1092120 : Nat := 118140960795 + 1092120 * 2 ^ 59
def prefixEnd_1092120 : Nat := 4983230072969 + 3 ^ 40 * 1092120 * 2
def baseEnd_1092120 : Nat := 373854994925581539451625

theorem tailTrace_1092120 : CollatzResearch.WordTrace tailWord_1092120 prefixEnd_1092120 373854994925581539451625 := by
  unfold tailWord_1092120
  simp only [CollatzResearch.WordTrace]
  refine ⟨19916444401721617045776907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26555259202295489394369209 19916444401721617045776907)
  ·
    refine ⟨29874666602582425568665361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19916444401721617045776907 29874666602582425568665361)
    ·
      refine ⟨22405999951936819176499021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29874666602582425568665361 22405999951936819176499021)
      ·
        refine ⟨8402249981976307191187133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22405999951936819176499021 8402249981976307191187133)
        ·
          refine ⟨3150843743241115196695175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8402249981976307191187133 3150843743241115196695175)
          ·
            refine ⟨4726265614861672795042763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150843743241115196695175 4726265614861672795042763)
            ·
              refine ⟨7089398422292509192564145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726265614861672795042763 7089398422292509192564145)
              ·
                refine ⟨5317048816719381894423109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7089398422292509192564145 5317048816719381894423109)
                ·
                  refine ⟨996946653134884105204333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5317048816719381894423109 996946653134884105204333)
                  ·
                    refine ⟨373854994925581539451625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 996946653134884105204333 373854994925581539451625)
                    ·
                      rfl

theorem cell22_1092120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_1092120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092120 prefixEnd_1092120 := by exact prefixLift 1092120
  have htrace : WordTrace (prefixWord ++ tailWord_1092120) baseStart_1092120 baseEnd_1092120 := by
    simpa [prefixWord, tailWord_1092120, baseEnd_1092120] using wordTrace_append hprefix tailTrace_1092120
  have hstable : (prefixWord ++ tailWord_1092120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092120).length < 2 ^ (prefixWord ++ tailWord_1092120).sum := by decide
  have hdescent : baseEnd_1092120 < baseStart_1092120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092150 : List Nat := [5, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1092150 : Nat := 118140960795 + 1092150 * 2 ^ 59
def prefixEnd_1092150 : Nat := 4983230072969 + 3 ^ 40 * 1092150 * 2
def baseEnd_1092150 : Nat := 41540584948741273466837

theorem tailTrace_1092150 : CollatzResearch.WordTrace tailWord_1092150 prefixEnd_1092150 41540584948741273466837 := by
  unfold tailWord_1092150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489623937083409325946619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26555988662223032810097269 2489623937083409325946619)
  ·
    refine ⟨3734435905625113988919929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2489623937083409325946619 3734435905625113988919929)
    ·
      refine ⟨2800826929218835491689947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3734435905625113988919929 2800826929218835491689947)
      ·
        refine ⟨4201240393828253237534921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2800826929218835491689947 4201240393828253237534921)
        ·
          refine ⟨3150930295371189928151191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4201240393828253237534921 3150930295371189928151191)
          ·
            refine ⟨4726395443056784892226787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150930295371189928151191 4726395443056784892226787)
            ·
              refine ⟨7089593164585177338340181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726395443056784892226787 7089593164585177338340181)
              ·
                refine ⟨41540584948741273466837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7089593164585177338340181 41540584948741273466837)
                ·
                  rfl

theorem cell22_1092150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1092150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092150 prefixEnd_1092150 := by exact prefixLift 1092150
  have htrace : WordTrace (prefixWord ++ tailWord_1092150) baseStart_1092150 baseEnd_1092150 := by
    simpa [prefixWord, tailWord_1092150, baseEnd_1092150] using wordTrace_append hprefix tailTrace_1092150
  have hstable : (prefixWord ++ tailWord_1092150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092150).length < 2 ^ (prefixWord ++ tailWord_1092150).sum := by decide
  have hdescent : baseEnd_1092150 < baseStart_1092150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092154 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_1092154 : Nat := 118140960795 + 1092154 * 2 ^ 59
def prefixEnd_1092154 : Nat := 4983230072969 + 3 ^ 40 * 1092154 * 2
def baseEnd_1092154 : Nat := 373866633820416784101521

theorem tailTrace_1092154 : CollatzResearch.WordTrace tailWord_1092154 prefixEnd_1092154 373866633820416784101521 := by
  unfold tailWord_1092154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9958532221330014474572879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26556085923546705265527677 9958532221330014474572879)
  ·
    refine ⟨14937798331995021711859319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9958532221330014474572879 14937798331995021711859319)
    ·
      refine ⟨22406697497992532567788979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14937798331995021711859319 22406697497992532567788979)
      ·
        refine ⟨33610046246988798851683469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22406697497992532567788979 33610046246988798851683469)
        ·
          refine ⟨12603767342620799569381301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33610046246988798851683469 12603767342620799569381301)
          ·
            refine ⟨1181603188370699959629497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12603767342620799569381301 1181603188370699959629497)
            ·
              refine ⟨886202391278024969722123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181603188370699959629497 886202391278024969722123)
              ·
                refine ⟨1329303586917037454583185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886202391278024969722123 1329303586917037454583185)
                ·
                  refine ⟨996977690187778090937389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329303586917037454583185 996977690187778090937389)
                  ·
                    refine ⟨373866633820416784101521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 996977690187778090937389 373866633820416784101521)
                    ·
                      rfl

theorem cell22_1092154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_1092154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092154 prefixEnd_1092154 := by exact prefixLift 1092154
  have htrace : WordTrace (prefixWord ++ tailWord_1092154) baseStart_1092154 baseEnd_1092154 := by
    simpa [prefixWord, tailWord_1092154, baseEnd_1092154] using wordTrace_append hprefix tailTrace_1092154
  have hstable : (prefixWord ++ tailWord_1092154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092154).length < 2 ^ (prefixWord ++ tailWord_1092154).sum := by decide
  have hdescent : baseEnd_1092154 < baseStart_1092154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092190 : List Nat := [4, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1092190 : Nat := 118140960795 + 1092190 * 2 ^ 59
def prefixEnd_1092190 : Nat := 4983230072969 + 3 ^ 40 * 1092190 * 2
def baseEnd_1092190 : Nat := 124626319118708230067137

theorem tailTrace_1092190 : CollatzResearch.WordTrace tailWord_1092190 prefixEnd_1092190 124626319118708230067137 := by
  unfold tailWord_1092190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979430239148704505825253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26556961275459757364401349 4979430239148704505825253)
  ·
    refine ⟨933643169840382094842235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4979430239148704505825253 933643169840382094842235)
    ·
      refine ⟨1400464754760573142263353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933643169840382094842235 1400464754760573142263353)
      ·
        refine ⟨1050348566070429856697515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1400464754760573142263353 1050348566070429856697515)
        ·
          refine ⟨1575522849105644785046273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050348566070429856697515 1575522849105644785046273)
          ·
            refine ⟨1181642136829233588784705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575522849105644785046273 1181642136829233588784705)
            ·
              refine ⟨886231602621925191588529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181642136829233588784705 886231602621925191588529)
              ·
                refine ⟨664673701966443893691397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886231602621925191588529 664673701966443893691397)
                ·
                  refine ⟨124626319118708230067137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664673701966443893691397 124626319118708230067137)
                  ·
                    rfl

theorem cell22_1092190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1092190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092190 prefixEnd_1092190 := by exact prefixLift 1092190
  have htrace : WordTrace (prefixWord ++ tailWord_1092190) baseStart_1092190 baseEnd_1092190 := by
    simpa [prefixWord, tailWord_1092190, baseEnd_1092190] using wordTrace_append hprefix tailTrace_1092190
  have hstable : (prefixWord ++ tailWord_1092190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092190).length < 2 ^ (prefixWord ++ tailWord_1092190).sum := by decide
  have hdescent : baseEnd_1092190 < baseStart_1092190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092195 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 5]
def baseStart_1092195 : Nat := 118140960795 + 1092195 * 2 ^ 59
def prefixEnd_1092195 : Nat := 4983230072969 + 3 ^ 40 * 1092195 * 2
def baseEnd_1092195 : Nat := 124626889652768781275465

theorem tailTrace_1092195 : CollatzResearch.WordTrace tailWord_1092195 prefixEnd_1092195 124626889652768781275465 := by
  unfold tailWord_1092195
  simp only [CollatzResearch.WordTrace]
  refine ⟨39835624278171521900534039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26557082852114347933689359 39835624278171521900534039)
  ·
    refine ⟨59753436417257282850801059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39835624278171521900534039 59753436417257282850801059)
    ·
      refine ⟨89630154625885924276201589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59753436417257282850801059 89630154625885924276201589)
      ·
        refine ⟨8402826996176805400893899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89630154625885924276201589 8402826996176805400893899)
        ·
          refine ⟨12604240494265208101340849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8402826996176805400893899 12604240494265208101340849)
          ·
            refine ⟨9453180370698906076005637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12604240494265208101340849 9453180370698906076005637)
            ·
              refine ⟨1772471319506044889251057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9453180370698906076005637 1772471319506044889251057)
              ·
                refine ⟨1329353489629533666938293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772471319506044889251057 1329353489629533666938293)
                ·
                  refine ⟨124626889652768781275465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329353489629533666938293 124626889652768781275465)
                  ·
                    rfl

theorem cell22_1092195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 5].length) (baseStart_1092195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092195 prefixEnd_1092195 := by exact prefixLift 1092195
  have htrace : WordTrace (prefixWord ++ tailWord_1092195) baseStart_1092195 baseEnd_1092195 := by
    simpa [prefixWord, tailWord_1092195, baseEnd_1092195] using wordTrace_append hprefix tailTrace_1092195
  have hstable : (prefixWord ++ tailWord_1092195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092195).length < 2 ^ (prefixWord ++ tailWord_1092195).sum := by decide
  have hdescent : baseEnd_1092195 < baseStart_1092195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092225 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1092225 : Nat := 118140960795 + 1092225 * 2 ^ 59
def prefixEnd_1092225 : Nat := 4983230072969 + 3 ^ 40 * 1092225 * 2
def baseEnd_1092225 : Nat := 373890938571396265576303

theorem tailTrace_1092225 : CollatzResearch.WordTrace tailWord_1092225 prefixEnd_1092225 373890938571396265576303 := by
  unfold tailWord_1092225
  simp only [CollatzResearch.WordTrace]
  refine ⟨39836718468062837024126129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26557812312041891349417419 39836718468062837024126129)
  ·
    refine ⟨29877538851047127768094597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39836718468062837024126129 29877538851047127768094597)
    ·
      refine ⟨5602038534571336456517737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29877538851047127768094597 5602038534571336456517737)
      ·
        refine ⟨4201528900928502342388303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5602038534571336456517737 4201528900928502342388303)
        ·
          refine ⟨6302293351392753513582455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201528900928502342388303 6302293351392753513582455)
          ·
            refine ⟨9453440027089130270373683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6302293351392753513582455 9453440027089130270373683)
            ·
              refine ⟨14180160040633695405560525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9453440027089130270373683 14180160040633695405560525)
              ·
                refine ⟨5317560015237635777085197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14180160040633695405560525 5317560015237635777085197)
                ·
                  refine ⟨1994085005714113416406949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5317560015237635777085197 1994085005714113416406949)
                  ·
                    refine ⟨373890938571396265576303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1994085005714113416406949 373890938571396265576303)
                    ·
                      rfl

theorem cell22_1092225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1092225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092225 prefixEnd_1092225 := by exact prefixLift 1092225
  have htrace : WordTrace (prefixWord ++ tailWord_1092225) baseStart_1092225 baseEnd_1092225 := by
    simpa [prefixWord, tailWord_1092225, baseEnd_1092225] using wordTrace_append hprefix tailTrace_1092225
  have hstable : (prefixWord ++ tailWord_1092225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092225).length < 2 ^ (prefixWord ++ tailWord_1092225).sum := by decide
  have hdescent : baseEnd_1092225 < baseStart_1092225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092257 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 6]
def baseStart_1092257 : Nat := 118140960795 + 1092257 * 2 ^ 59
def prefixEnd_1092257 : Nat := 4983230072969 + 3 ^ 40 * 1092257 * 2
def baseEnd_1092257 : Nat := 124633964275119616258735

theorem tailTrace_1092257 : CollatzResearch.WordTrace tailWord_1092257 prefixEnd_1092257 124633964275119616258735 := by
  unfold tailWord_1092257
  simp only [CollatzResearch.WordTrace]
  refine ⟨39837885603946906489291025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26558590402631270992860683 39837885603946906489291025)
  ·
    refine ⟨29878414202960179866968269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39837885603946906489291025 29878414202960179866968269)
    ·
      refine ⟨11204405326110067450113101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29878414202960179866968269 11204405326110067450113101)
      ·
        refine ⟨4201651997291275293792413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11204405326110067450113101 4201651997291275293792413)
        ·
          refine ⟨1575619498984228235172155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4201651997291275293792413 1575619498984228235172155)
          ·
            refine ⟨2363429248476342352758233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575619498984228235172155 2363429248476342352758233)
            ·
              refine ⟨1772571936357256764568675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2363429248476342352758233 1772571936357256764568675)
              ·
                refine ⟨2658857904535885146853013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772571936357256764568675 2658857904535885146853013)
                ·
                  refine ⟨124633964275119616258735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2658857904535885146853013 124633964275119616258735)
                  ·
                    rfl

theorem cell22_1092257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_1092257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092257 prefixEnd_1092257 := by exact prefixLift 1092257
  have htrace : WordTrace (prefixWord ++ tailWord_1092257) baseStart_1092257 baseEnd_1092257 := by
    simpa [prefixWord, tailWord_1092257, baseEnd_1092257] using wordTrace_append hprefix tailTrace_1092257
  have hstable : (prefixWord ++ tailWord_1092257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092257).length < 2 ^ (prefixWord ++ tailWord_1092257).sum := by decide
  have hdescent : baseEnd_1092257 < baseStart_1092257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092285 : List Nat := [1, 4, 1, 2, 1, 4, 1, 8]
def baseStart_1092285 : Nat := 118140960795 + 1092285 * 2 ^ 59
def prefixEnd_1092285 : Nat := 4983230072969 + 3 ^ 40 * 1092285 * 2
def baseEnd_1092285 : Nat := 41545719755286234341791

theorem tailTrace_1092285 : CollatzResearch.WordTrace tailWord_1092285 prefixEnd_1092285 41545719755286234341791 := by
  unfold tailWord_1092285
  simp only [CollatzResearch.WordTrace]
  refine ⟨39838906847845467271310309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26559271231896978180873539 39838906847845467271310309)
  ·
    refine ⟨7469795033971025113370683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39838906847845467271310309 7469795033971025113370683)
    ·
      refine ⟨11204692550956537670056025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7469795033971025113370683 11204692550956537670056025)
      ·
        refine ⟨8403519413217403252542019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11204692550956537670056025 8403519413217403252542019)
        ·
          refine ⟨12605279119826104878813029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403519413217403252542019 12605279119826104878813029)
          ·
            refine ⟨2363489834967394664777443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12605279119826104878813029 2363489834967394664777443)
            ·
              refine ⟨3545234752451091997166165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363489834967394664777443 3545234752451091997166165)
              ·
                refine ⟨41545719755286234341791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3545234752451091997166165 41545719755286234341791)
                ·
                  rfl

theorem cell22_1092285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 8].length) (baseStart_1092285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092285 prefixEnd_1092285 := by exact prefixLift 1092285
  have htrace : WordTrace (prefixWord ++ tailWord_1092285) baseStart_1092285 baseEnd_1092285 := by
    simpa [prefixWord, tailWord_1092285, baseEnd_1092285] using wordTrace_append hprefix tailTrace_1092285
  have hstable : (prefixWord ++ tailWord_1092285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092285).length < 2 ^ (prefixWord ++ tailWord_1092285).sum := by decide
  have hdescent : baseEnd_1092285 < baseStart_1092285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092392 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 6]
def baseStart_1092392 : Nat := 118140960795 + 1092392 * 2 ^ 59
def prefixEnd_1092392 : Nat := 4983230072969 + 3 ^ 40 * 1092392 * 2
def baseEnd_1092392 : Nat := 124649368694754498883597

theorem tailTrace_1092392 : CollatzResearch.WordTrace tailWord_1092392 prefixEnd_1092392 124649368694754498883597 := by
  unfold tailWord_1092392
  simp only [CollatzResearch.WordTrace]
  refine ⟨19921404729228912272727715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26561872972305216363636953 19921404729228912272727715)
  ·
    refine ⟨29882107093843368409091573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19921404729228912272727715 29882107093843368409091573)
    ·
      refine ⟨2801447540047815788352335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29882107093843368409091573 2801447540047815788352335)
      ·
        refine ⟨4202171310071723682528503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801447540047815788352335 4202171310071723682528503)
        ·
          refine ⟨6303256965107585523792755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4202171310071723682528503 6303256965107585523792755)
          ·
            refine ⟨9454885447661378285689133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6303256965107585523792755 9454885447661378285689133)
            ·
              refine ⟨3545582042873016857133425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9454885447661378285689133 3545582042873016857133425)
              ·
                refine ⟨2659186532154762642850069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545582042873016857133425 2659186532154762642850069)
                ·
                  refine ⟨124649368694754498883597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2659186532154762642850069 124649368694754498883597)
                  ·
                    rfl

theorem cell22_1092392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_1092392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092392 prefixEnd_1092392 := by exact prefixLift 1092392
  have htrace : WordTrace (prefixWord ++ tailWord_1092392) baseStart_1092392 baseEnd_1092392 := by
    simpa [prefixWord, tailWord_1092392, baseEnd_1092392] using wordTrace_append hprefix tailTrace_1092392
  have hstable : (prefixWord ++ tailWord_1092392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092392).length < 2 ^ (prefixWord ++ tailWord_1092392).sum := by decide
  have hdescent : baseEnd_1092392 < baseStart_1092392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092407 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 4, 3]
def baseStart_1092407 : Nat := 118140960795 + 1092407 * 2 ^ 59
def prefixEnd_1092407 : Nat := 4983230072969 + 3 ^ 40 * 1092407 * 2
def baseEnd_1092407 : Nat := 373953240890808457525745

theorem tailTrace_1092407 : CollatzResearch.WordTrace tailWord_1092407 prefixEnd_1092407 373953240890808457525745 := by
  unfold tailWord_1092407
  simp only [CollatzResearch.WordTrace]
  refine ⟨39843356553403482107251475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26562237702268988071500983 39843356553403482107251475)
  ·
    refine ⟨59765034830105223160877213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39843356553403482107251475 59765034830105223160877213)
    ·
      refine ⟨22411888061289458685328955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59765034830105223160877213 22411888061289458685328955)
      ·
        refine ⟨33617832091934188027993433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22411888061289458685328955 33617832091934188027993433)
        ·
          refine ⟨25213374068950641020995075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33617832091934188027993433 25213374068950641020995075)
          ·
            refine ⟨37820061103425961531492613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25213374068950641020995075 37820061103425961531492613)
            ·
              refine ⟨7091261456892367787154865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37820061103425961531492613 7091261456892367787154865)
              ·
                refine ⟨5318446092669275840366149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7091261456892367787154865 5318446092669275840366149)
                ·
                  refine ⟨997208642375489220068653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5318446092669275840366149 997208642375489220068653)
                  ·
                    refine ⟨373953240890808457525745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 997208642375489220068653 373953240890808457525745)
                    ·
                      rfl

theorem cell22_1092407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_1092407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092407 prefixEnd_1092407 := by exact prefixLift 1092407
  have htrace : WordTrace (prefixWord ++ tailWord_1092407) baseStart_1092407 baseEnd_1092407 := by
    simpa [prefixWord, tailWord_1092407, baseEnd_1092407] using wordTrace_append hprefix tailTrace_1092407
  have hstable : (prefixWord ++ tailWord_1092407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092407).length < 2 ^ (prefixWord ++ tailWord_1092407).sum := by decide
  have hdescent : baseEnd_1092407 < baseStart_1092407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092441 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 2, 3]
def baseStart_1092441 : Nat := 118140960795 + 1092441 * 2 ^ 59
def prefixEnd_1092441 : Nat := 4983230072969 + 3 ^ 40 * 1092441 * 2
def baseEnd_1092441 : Nat := 373964879785643702175641

theorem tailTrace_1092441 : CollatzResearch.WordTrace tailWord_1092441 prefixEnd_1092441 373964879785643702175641 := by
  unfold tailWord_1092441
  simp only [CollatzResearch.WordTrace]
  refine ⟨39844596635280305913989177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26563064423520203942659451 39844596635280305913989177)
  ·
    refine ⟨29883447476460229435491883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39844596635280305913989177 29883447476460229435491883)
    ·
      refine ⟨44825171214690344153237825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29883447476460229435491883 44825171214690344153237825)
      ·
        refine ⟨33618878411017758114928369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44825171214690344153237825 33618878411017758114928369)
        ·
          refine ⟨25214158808263318586196277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33618878411017758114928369 25214158808263318586196277)
          ·
            refine ⟨2363827388274686117455901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25214158808263318586196277 2363827388274686117455901)
            ·
              refine ⟨886435270603007294045963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2363827388274686117455901 886435270603007294045963)
              ·
                refine ⟨1329652905904510941068945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886435270603007294045963 1329652905904510941068945)
                ·
                  refine ⟨997239679428383205801709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329652905904510941068945 997239679428383205801709)
                  ·
                    refine ⟨373964879785643702175641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 997239679428383205801709 373964879785643702175641)
                    ·
                      rfl

theorem cell22_1092441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_1092441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092441 prefixEnd_1092441 := by exact prefixLift 1092441
  have htrace : WordTrace (prefixWord ++ tailWord_1092441) baseStart_1092441 baseEnd_1092441 := by
    simpa [prefixWord, tailWord_1092441, baseEnd_1092441] using wordTrace_append hprefix tailTrace_1092441
  have hstable : (prefixWord ++ tailWord_1092441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092441).length < 2 ^ (prefixWord ++ tailWord_1092441).sum := by decide
  have hdescent : baseEnd_1092441 < baseStart_1092441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092559 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 1, 5]
def baseStart_1092559 : Nat := 118140960795 + 1092559 * 2 ^ 59
def prefixEnd_1092559 : Nat := 4983230072969 + 3 ^ 40 * 1092559 * 2
def baseEnd_1092559 : Nat := 374005273597130727725279

theorem tailTrace_1092559 : CollatzResearch.WordTrace tailWord_1092559 prefixEnd_1092559 374005273597130727725279 := by
  unfold tailWord_1092559
  simp only [CollatzResearch.WordTrace]
  refine ⟨39848900448852812066784731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26565933632568541377856487 39848900448852812066784731)
  ·
    refine ⟨59773350673279218100177097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39848900448852812066784731 59773350673279218100177097)
    ·
      refine ⟨44830013004959413575132823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59773350673279218100177097 44830013004959413575132823)
      ·
        refine ⟨67245019507439120362699235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44830013004959413575132823 67245019507439120362699235)
        ·
          refine ⟨100867529261158680544048853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67245019507439120362699235 100867529261158680544048853)
          ·
            refine ⟨2364082717058406575251145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 100867529261158680544048853 2364082717058406575251145)
            ·
              refine ⟨1773062037793804931438359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364082717058406575251145 1773062037793804931438359)
              ·
                refine ⟨2659593056690707397157539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773062037793804931438359 2659593056690707397157539)
                ·
                  refine ⟨3989389585036061095736309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659593056690707397157539 3989389585036061095736309)
                  ·
                    refine ⟨374005273597130727725279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3989389585036061095736309 374005273597130727725279)
                    ·
                      rfl

theorem cell22_1092559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_1092559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092559 prefixEnd_1092559 := by exact prefixLift 1092559
  have htrace : WordTrace (prefixWord ++ tailWord_1092559) baseStart_1092559 baseEnd_1092559 := by
    simpa [prefixWord, tailWord_1092559, baseEnd_1092559] using wordTrace_append hprefix tailTrace_1092559
  have hstable : (prefixWord ++ tailWord_1092559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092559).length < 2 ^ (prefixWord ++ tailWord_1092559).sum := by decide
  have hdescent : baseEnd_1092559 < baseStart_1092559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092578 : List Nat := [3, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1092578 : Nat := 118140960795 + 1092578 * 2 ^ 59
def prefixEnd_1092578 : Nat := 4983230072969 + 3 ^ 40 * 1092578 * 2
def baseEnd_1092578 : Nat := 124670592561807003833407

theorem tailTrace_1092578 : CollatzResearch.WordTrace tailWord_1092578 prefixEnd_1092578 124670592561807003833407 := by
  unfold tailWord_1092578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9962398358945994577931597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26566395623855985541150925 9962398358945994577931597)
  ·
    refine ⟨3735899384604747966724349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9962398358945994577931597 3735899384604747966724349)
    ·
      refine ⟨1400962269226780487521631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3735899384604747966724349 1400962269226780487521631)
      ·
        refine ⟨2101443403840170731282447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1400962269226780487521631 2101443403840170731282447)
        ·
          refine ⟨3152165105760256096923671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101443403840170731282447 3152165105760256096923671)
          ·
            refine ⟨4728247658640384145385507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152165105760256096923671 4728247658640384145385507)
            ·
              refine ⟨7092371487960576218078261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728247658640384145385507 7092371487960576218078261)
              ·
                refine ⟨664909826996304020444837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7092371487960576218078261 664909826996304020444837)
                ·
                  refine ⟨124670592561807003833407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664909826996304020444837 124670592561807003833407)
                  ·
                    rfl

theorem cell22_1092578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1092578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092578 prefixEnd_1092578 := by exact prefixLift 1092578
  have htrace : WordTrace (prefixWord ++ tailWord_1092578) baseStart_1092578 baseEnd_1092578 := by
    simpa [prefixWord, tailWord_1092578, baseEnd_1092578] using wordTrace_append hprefix tailTrace_1092578
  have hstable : (prefixWord ++ tailWord_1092578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092578).length < 2 ^ (prefixWord ++ tailWord_1092578).sum := by decide
  have hdescent : baseEnd_1092578 < baseStart_1092578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092593 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 2, 3]
def baseStart_1092593 : Nat := 118140960795 + 1092593 * 2 ^ 59
def prefixEnd_1092593 : Nat := 4983230072969 + 3 ^ 40 * 1092593 * 2
def baseEnd_1092593 : Nat := 374016912491965972375175

theorem tailTrace_1092593 : CollatzResearch.WordTrace tailWord_1092593 prefixEnd_1092593 374016912491965972375175 := by
  unfold tailWord_1092593
  simp only [CollatzResearch.WordTrace]
  refine ⟨39850140530729635873522433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26566760353819757249014955 39850140530729635873522433)
  ·
    refine ⟨29887605398047226905141825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39850140530729635873522433 29887605398047226905141825)
    ·
      refine ⟨22415704048535420178856369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29887605398047226905141825 22415704048535420178856369)
      ·
        refine ⟨16811778036401565134142277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22415704048535420178856369 16811778036401565134142277)
        ·
          refine ⟨3152208381825293462651677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16811778036401565134142277 3152208381825293462651677)
          ·
            refine ⟨1182078143184485048494379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3152208381825293462651677 1182078143184485048494379)
            ·
              refine ⟨1773117214776727572741569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182078143184485048494379 1773117214776727572741569)
              ·
                refine ⟨1329837911082545679556177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773117214776727572741569 1329837911082545679556177)
                ·
                  refine ⟨997378433311909259667133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1329837911082545679556177 997378433311909259667133)
                  ·
                    refine ⟨374016912491965972375175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 997378433311909259667133 374016912491965972375175)
                    ·
                      rfl

theorem cell22_1092593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_1092593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092593 prefixEnd_1092593 := by exact prefixLift 1092593
  have htrace : WordTrace (prefixWord ++ tailWord_1092593) baseStart_1092593 baseEnd_1092593 := by
    simpa [prefixWord, tailWord_1092593, baseEnd_1092593] using wordTrace_append hprefix tailTrace_1092593
  have hstable : (prefixWord ++ tailWord_1092593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092593).length < 2 ^ (prefixWord ++ tailWord_1092593).sum := by decide
  have hdescent : baseEnd_1092593 < baseStart_1092593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092602 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_1092602 : Nat := 118140960795 + 1092602 * 2 ^ 59
def prefixEnd_1092602 : Nat := 4983230072969 + 3 ^ 40 * 1092602 * 2
def baseEnd_1092602 : Nat := 374019993375892948900147

theorem tailTrace_1092602 : CollatzResearch.WordTrace tailWord_1092602 prefixEnd_1092602 374019993375892948900147 := by
  unfold tailWord_1092602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9962617196924257602650015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26566979191798020273733373 9962617196924257602650015)
  ·
    refine ⟨14943925795386386403975023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9962617196924257602650015 14943925795386386403975023)
    ·
      refine ⟨22415888693079579605962535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14943925795386386403975023 22415888693079579605962535)
      ·
        refine ⟨33623833039619369408943803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22415888693079579605962535 33623833039619369408943803)
        ·
          refine ⟨50435749559429054113415705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33623833039619369408943803 50435749559429054113415705)
          ·
            refine ⟨37826812169571790585061779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50435749559429054113415705 37826812169571790585061779)
            ·
              refine ⟨56740218254357685877592669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37826812169571790585061779 56740218254357685877592669)
              ·
                refine ⟨21277581845384132204097251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56740218254357685877592669 21277581845384132204097251)
                ·
                  refine ⟨31916372768076198306145877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21277581845384132204097251 31916372768076198306145877)
                  ·
                    refine ⟨374019993375892948900147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31916372768076198306145877 374019993375892948900147)
                    ·
                      rfl

theorem cell22_1092602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_1092602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092602 prefixEnd_1092602 := by exact prefixLift 1092602
  have htrace : WordTrace (prefixWord ++ tailWord_1092602) baseStart_1092602 baseEnd_1092602 := by
    simpa [prefixWord, tailWord_1092602, baseEnd_1092602] using wordTrace_append hprefix tailTrace_1092602
  have hstable : (prefixWord ++ tailWord_1092602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092602).length < 2 ^ (prefixWord ++ tailWord_1092602).sum := by decide
  have hdescent : baseEnd_1092602 < baseStart_1092602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092610 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1092610 : Nat := 118140960795 + 1092610 * 2 ^ 59
def prefixEnd_1092610 : Nat := 4983230072969 + 3 ^ 40 * 1092610 * 2
def baseEnd_1092610 : Nat := 374022731939383594700123

theorem tailTrace_1092610 : CollatzResearch.WordTrace tailWord_1092610 prefixEnd_1092610 374022731939383594700123 := by
  unfold tailWord_1092610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9962690142917011944222821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26567173714445365184594189 9962690142917011944222821)
  ·
    refine ⟨1868004401796939739541779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9962690142917011944222821 1868004401796939739541779)
    ·
      refine ⟨2802006602695409609312669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868004401796939739541779 2802006602695409609312669)
      ·
        refine ⟨1050752476010778603492251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2802006602695409609312669 1050752476010778603492251)
        ·
          refine ⟨1576128714016167905238377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050752476010778603492251 1576128714016167905238377)
          ·
            refine ⟨1182096535512125928928783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1576128714016167905238377 1182096535512125928928783)
            ·
              refine ⟨1773144803268188893393175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182096535512125928928783 1773144803268188893393175)
              ·
                refine ⟨2659717204902283340089763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773144803268188893393175 2659717204902283340089763)
                ·
                  refine ⟨3989575807353425010134645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659717204902283340089763 3989575807353425010134645)
                  ·
                    refine ⟨374022731939383594700123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3989575807353425010134645 374022731939383594700123)
                    ·
                      rfl

theorem cell22_1092610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1092610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092610 prefixEnd_1092610 := by exact prefixLift 1092610
  have htrace : WordTrace (prefixWord ++ tailWord_1092610) baseStart_1092610 baseEnd_1092610 := by
    simpa [prefixWord, tailWord_1092610, baseEnd_1092610] using wordTrace_append hprefix tailTrace_1092610
  have hstable : (prefixWord ++ tailWord_1092610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092610).length < 2 ^ (prefixWord ++ tailWord_1092610).sum := by decide
  have hdescent : baseEnd_1092610 < baseStart_1092610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092668 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 5]
def baseStart_1092668 : Nat := 118140960795 + 1092668 * 2 ^ 59
def prefixEnd_1092668 : Nat := 4983230072969 + 3 ^ 40 * 1092668 * 2
def baseEnd_1092668 : Nat := 124680862174896925583315

theorem tailTrace_1092668 : CollatzResearch.WordTrace tailWord_1092668 prefixEnd_1092668 124680862174896925583315 := by
  unfold tailWord_1092668
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926438002728961841251329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26568584003638615788335105 19926438002728961841251329)
  ·
    refine ⟨14944828502046721380938497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19926438002728961841251329 14944828502046721380938497)
    ·
      refine ⟨11208621376535041035703873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14944828502046721380938497 11208621376535041035703873)
      ·
        refine ⟨8406466032401280776777905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11208621376535041035703873 8406466032401280776777905)
        ·
          refine ⟨6304849524300960582583429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8406466032401280776777905 6304849524300960582583429)
          ·
            refine ⟨1182159285806430109234393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6304849524300960582583429 1182159285806430109234393)
            ·
              refine ⟨886619464354822581925795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182159285806430109234393 886619464354822581925795)
              ·
                refine ⟨1329929196532233872888693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886619464354822581925795 1329929196532233872888693)
                ·
                  refine ⟨124680862174896925583315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329929196532233872888693 124680862174896925583315)
                  ·
                    rfl

theorem cell22_1092668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_1092668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092668 prefixEnd_1092668 := by exact prefixLift 1092668
  have htrace : WordTrace (prefixWord ++ tailWord_1092668) baseStart_1092668 baseEnd_1092668 := by
    simpa [prefixWord, tailWord_1092668, baseEnd_1092668] using wordTrace_append hprefix tailTrace_1092668
  have hstable : (prefixWord ++ tailWord_1092668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092668).length < 2 ^ (prefixWord ++ tailWord_1092668).sum := by decide
  have hdescent : baseEnd_1092668 < baseStart_1092668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092696 : List Nat := [2, 1, 2, 2, 1, 3, 2, 5, 4]
def baseStart_1092696 : Nat := 118140960795 + 1092696 * 2 ^ 59
def prefixEnd_1092696 : Nat := 4983230072969 + 3 ^ 40 * 1092696 * 2
def baseEnd_1092696 : Nat := 124684057165636012349953

theorem tailTrace_1092696 : CollatzResearch.WordTrace tailWord_1092696 prefixEnd_1092696 124684057165636012349953 := by
  unfold tailWord_1092696
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926948624678242232260971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26569264832904322976347961 19926948624678242232260971)
  ·
    refine ⟨29890422937017363348391457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19926948624678242232260971 29890422937017363348391457)
    ·
      refine ⟨22417817202763022511293593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29890422937017363348391457 22417817202763022511293593)
      ·
        refine ⟨16813362902072266883470195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22417817202763022511293593 16813362902072266883470195)
        ·
          refine ⟨25220044353108400325205293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16813362902072266883470195 25220044353108400325205293)
          ·
            refine ⟨9457516632415650121951985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25220044353108400325205293 9457516632415650121951985)
            ·
              refine ⟨7093137474311737591463989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9457516632415650121951985 7093137474311737591463989)
              ·
                refine ⟨664981638216725399199749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7093137474311737591463989 664981638216725399199749)
                ·
                  refine ⟨124684057165636012349953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664981638216725399199749 124684057165636012349953)
                  ·
                    rfl

theorem cell22_1092696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_1092696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092696 prefixEnd_1092696 := by exact prefixLift 1092696
  have htrace : WordTrace (prefixWord ++ tailWord_1092696) baseStart_1092696 baseEnd_1092696 := by
    simpa [prefixWord, tailWord_1092696, baseEnd_1092696] using wordTrace_append hprefix tailTrace_1092696
  have hstable : (prefixWord ++ tailWord_1092696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092696).length < 2 ^ (prefixWord ++ tailWord_1092696).sum := by decide
  have hdescent : baseEnd_1092696 < baseStart_1092696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092713 : List Nat := [1, 2, 1, 1, 1, 6, 4, 2, 4]
def baseStart_1092713 : Nat := 118140960795 + 1092713 * 2 ^ 59
def prefixEnd_1092713 : Nat := 4983230072969 + 3 ^ 40 * 1092713 * 2
def baseEnd_1092713 : Nat := 124685996981441886458269

theorem tailTrace_1092713 : CollatzResearch.WordTrace tailWord_1092713 prefixEnd_1092713 124685996981441886458269 := by
  unfold tailWord_1092713
  simp only [CollatzResearch.WordTrace]
  refine ⟨39854517290294896367890793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26569678193529930911927195 39854517290294896367890793)
  ·
    refine ⟨29890887967721172275918095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39854517290294896367890793 29890887967721172275918095)
    ·
      refine ⟨44836331951581758413877143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29890887967721172275918095 44836331951581758413877143)
      ·
        refine ⟨67254497927372637620815715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44836331951581758413877143 67254497927372637620815715)
        ·
          refine ⟨100881746891058956431223573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67254497927372637620815715 100881746891058956431223573)
          ·
            refine ⟨4728831885518388582713605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100881746891058956431223573 4728831885518388582713605)
            ·
              refine ⟨886655978534697859258801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4728831885518388582713605 886655978534697859258801)
              ·
                refine ⟨664991983901023394444101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 886655978534697859258801 664991983901023394444101)
                ·
                  refine ⟨124685996981441886458269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664991983901023394444101 124685996981441886458269)
                  ·
                    rfl

theorem cell22_1092713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_1092713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092713 prefixEnd_1092713 := by exact prefixLift 1092713
  have htrace : WordTrace (prefixWord ++ tailWord_1092713) baseStart_1092713 baseEnd_1092713 := by
    simpa [prefixWord, tailWord_1092713, baseEnd_1092713] using wordTrace_append hprefix tailTrace_1092713
  have hstable : (prefixWord ++ tailWord_1092713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092713).length < 2 ^ (prefixWord ++ tailWord_1092713).sum := by decide
  have hdescent : baseEnd_1092713 < baseStart_1092713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092726 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1092726 : Nat := 118140960795 + 1092726 * 2 ^ 59
def prefixEnd_1092726 : Nat := 4983230072969 + 3 ^ 40 * 1092726 * 2
def baseEnd_1092726 : Nat := 374062441109997958799767

theorem tailTrace_1092726 : CollatzResearch.WordTrace tailWord_1092726 prefixEnd_1092726 374062441109997958799767 := by
  unfold tailWord_1092726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490936964952987474257127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26569994292831866392076021 2490936964952987474257127)
  ·
    refine ⟨3736405447429481211385691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2490936964952987474257127 3736405447429481211385691)
    ·
      refine ⟨5604608171144221817078537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3736405447429481211385691 5604608171144221817078537)
      ·
        refine ⟨4203456128358166362808903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5604608171144221817078537 4203456128358166362808903)
        ·
          refine ⟨6305184192537249544213355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203456128358166362808903 6305184192537249544213355)
          ·
            refine ⟨9457776288805874316320033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6305184192537249544213355 9457776288805874316320033)
            ·
              refine ⟨7093332216604405737240025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9457776288805874316320033 7093332216604405737240025)
              ·
                refine ⟨5319999162453304302930019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7093332216604405737240025 5319999162453304302930019)
                ·
                  refine ⟨7979998743679956454395029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5319999162453304302930019 7979998743679956454395029)
                  ·
                    refine ⟨374062441109997958799767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7979998743679956454395029 374062441109997958799767)
                    ·
                      rfl

theorem cell22_1092726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1092726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092726 prefixEnd_1092726 := by exact prefixLift 1092726
  have htrace : WordTrace (prefixWord ++ tailWord_1092726) baseStart_1092726 baseEnd_1092726 := by
    simpa [prefixWord, tailWord_1092726, baseEnd_1092726] using wordTrace_append hprefix tailTrace_1092726
  have hstable : (prefixWord ++ tailWord_1092726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092726).length < 2 ^ (prefixWord ++ tailWord_1092726).sum := by decide
  have hdescent : baseEnd_1092726 < baseStart_1092726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092773 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_1092773 : Nat := 118140960795 + 1092773 * 2 ^ 59
def prefixEnd_1092773 : Nat := 4983230072969 + 3 ^ 40 * 1092773 * 2
def baseEnd_1092773 : Nat := 374078530170505502874623

theorem tailTrace_1092773 : CollatzResearch.WordTrace tailWord_1092773 prefixEnd_1092773 374078530170505502874623 := by
  unfold tailWord_1092773
  simp only [CollatzResearch.WordTrace]
  refine ⟨39856705670077526615074973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26571137113385017743383315 39856705670077526615074973)
  ·
    refine ⟨14946264626279072480653115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39856705670077526615074973 14946264626279072480653115)
    ·
      refine ⟨22419396939418608720979673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14946264626279072480653115 22419396939418608720979673)
      ·
        refine ⟨16814547704563956540734755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22419396939418608720979673 16814547704563956540734755)
        ·
          refine ⟨25221821556845934811102133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16814547704563956540734755 25221821556845934811102133)
          ·
            refine ⟨2364545770954306388540825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25221821556845934811102133 2364545770954306388540825)
            ·
              refine ⟨1773409328215729791405619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364545770954306388540825 1773409328215729791405619)
              ·
                refine ⟨2660113992323594687108429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773409328215729791405619 2660113992323594687108429)
                ·
                  refine ⟨997542747121348007665661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2660113992323594687108429 997542747121348007665661)
                  ·
                    refine ⟨374078530170505502874623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 997542747121348007665661 374078530170505502874623)
                    ·
                      rfl

theorem cell22_1092773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_1092773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092773 prefixEnd_1092773 := by exact prefixLift 1092773
  have htrace : WordTrace (prefixWord ++ tailWord_1092773) baseStart_1092773 baseEnd_1092773 := by
    simpa [prefixWord, tailWord_1092773, baseEnd_1092773] using wordTrace_append hprefix tailTrace_1092773
  have hstable : (prefixWord ++ tailWord_1092773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092773).length < 2 ^ (prefixWord ++ tailWord_1092773).sum := by decide
  have hdescent : baseEnd_1092773 < baseStart_1092773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092831 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 6]
def baseStart_1092831 : Nat := 118140960795 + 1092831 * 2 ^ 59
def prefixEnd_1092831 : Nat := 4983230072969 + 3 ^ 40 * 1092831 * 2
def baseEnd_1092831 : Nat := 124699461585270894974815

theorem tailTrace_1092831 : CollatzResearch.WordTrace tailWord_1092831 prefixEnd_1092831 124699461585270894974815 := by
  unfold tailWord_1092831
  simp only [CollatzResearch.WordTrace]
  refine ⟨39858821103867402520686347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26572547402578268347124231 39858821103867402520686347)
  ·
    refine ⟨59788231655801103781029521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39858821103867402520686347 59788231655801103781029521)
    ·
      refine ⟨44841173741850827835772141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59788231655801103781029521 44841173741850827835772141)
      ·
        refine ⟨16815440153194060438414553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44841173741850827835772141 16815440153194060438414553)
        ·
          refine ⟨12611580114895545328810915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16815440153194060438414553 12611580114895545328810915)
          ·
            refine ⟨18917370172343317993216373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12611580114895545328810915 18917370172343317993216373)
            ·
              refine ⟨1773503453657186061864035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18917370172343317993216373 1773503453657186061864035)
              ·
                refine ⟨2660255180485779092796053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773503453657186061864035 2660255180485779092796053)
                ·
                  refine ⟨124699461585270894974815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2660255180485779092796053 124699461585270894974815)
                  ·
                    rfl

theorem cell22_1092831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 6].length) (baseStart_1092831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092831 prefixEnd_1092831 := by exact prefixLift 1092831
  have htrace : WordTrace (prefixWord ++ tailWord_1092831) baseStart_1092831 baseEnd_1092831 := by
    simpa [prefixWord, tailWord_1092831, baseEnd_1092831] using wordTrace_append hprefix tailTrace_1092831
  have hstable : (prefixWord ++ tailWord_1092831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092831).length < 2 ^ (prefixWord ++ tailWord_1092831).sum := by decide
  have hdescent : baseEnd_1092831 < baseStart_1092831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092837 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 5]
def baseStart_1092837 : Nat := 118140960795 + 1092837 * 2 ^ 59
def prefixEnd_1092837 : Nat := 4983230072969 + 3 ^ 40 * 1092837 * 2
def baseEnd_1092837 : Nat := 124700146226143556424809

theorem tailTrace_1092837 : CollatzResearch.WordTrace tailWord_1092837 prefixEnd_1092837 124700146226143556424809 := by
  unfold tailWord_1092837
  simp only [CollatzResearch.WordTrace]
  refine ⟨39859039941845665545404765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26572693294563777030269843 39859039941845665545404765)
  ·
    refine ⟨14947139978192124579526787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39859039941845665545404765 14947139978192124579526787)
    ·
      refine ⟨22420709967288186869290181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14947139978192124579526787 22420709967288186869290181)
      ·
        refine ⟨4203883118866535037991909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22420709967288186869290181 4203883118866535037991909)
        ·
          refine ⟨788228084787475319623483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4203883118866535037991909 788228084787475319623483)
          ·
            refine ⟨1182342127181212979435225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788228084787475319623483 1182342127181212979435225)
            ·
              refine ⟨886756595385909734576419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182342127181212979435225 886756595385909734576419)
              ·
                refine ⟨1330134893078864601864629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886756595385909734576419 1330134893078864601864629)
                ·
                  refine ⟨124700146226143556424809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330134893078864601864629 124700146226143556424809)
                  ·
                    rfl

theorem cell22_1092837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_1092837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092837 prefixEnd_1092837 := by exact prefixLift 1092837
  have htrace : WordTrace (prefixWord ++ tailWord_1092837) baseStart_1092837 baseEnd_1092837 := by
    simpa [prefixWord, tailWord_1092837, baseEnd_1092837] using wordTrace_append hprefix tailTrace_1092837
  have hstable : (prefixWord ++ tailWord_1092837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092837).length < 2 ^ (prefixWord ++ tailWord_1092837).sum := by decide
  have hdescent : baseEnd_1092837 < baseStart_1092837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092878 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1092878 : Nat := 118140960795 + 1092878 * 2 ^ 59
def prefixEnd_1092878 : Nat := 4983230072969 + 3 ^ 40 * 1092878 * 2
def baseEnd_1092878 : Nat := 374114473816320228999301

theorem tailTrace_1092878 : CollatzResearch.WordTrace tailWord_1092878 prefixEnd_1092878 374114473816320228999301 := by
  unfold tailWord_1092878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982566916837141193455911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26573690223131419698431525 4982566916837141193455911)
  ·
    refine ⟨7473850375255711790183867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4982566916837141193455911 7473850375255711790183867)
    ·
      refine ⟨11210775562883567685275801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7473850375255711790183867 11210775562883567685275801)
      ·
        refine ⟨8408081672162675763956851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11210775562883567685275801 8408081672162675763956851)
        ·
          refine ⟨12612122508244013645935277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408081672162675763956851 12612122508244013645935277)
          ·
            refine ⟨4729545940591505117225729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12612122508244013645935277 4729545940591505117225729)
            ·
              refine ⟨3547159455443628837919297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4729545940591505117225729 3547159455443628837919297)
              ·
                refine ⟨2660369591582721628439473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547159455443628837919297 2660369591582721628439473)
                ·
                  refine ⟨1995277193687041221329605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2660369591582721628439473 1995277193687041221329605)
                  ·
                    refine ⟨374114473816320228999301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1995277193687041221329605 374114473816320228999301)
                    ·
                      rfl

theorem cell22_1092878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1092878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092878 prefixEnd_1092878 := by exact prefixLift 1092878
  have htrace : WordTrace (prefixWord ++ tailWord_1092878) baseStart_1092878 baseEnd_1092878 := by
    simpa [prefixWord, tailWord_1092878, baseEnd_1092878] using wordTrace_append hprefix tailTrace_1092878
  have hstable : (prefixWord ++ tailWord_1092878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092878).length < 2 ^ (prefixWord ++ tailWord_1092878).sum := by decide
  have hdescent : baseEnd_1092878 < baseStart_1092878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092893 : List Nat := [1, 4, 2, 3, 1, 1, 3, 7]
def baseStart_1092893 : Nat := 118140960795 + 1092893 * 2 ^ 59
def prefixEnd_1092893 : Nat := 4983230072969 + 3 ^ 40 * 1092893 * 2
def baseEnd_1092893 : Nat := 41568845402540576652695

theorem tailTrace_1092893 : CollatzResearch.WordTrace tailWord_1092893 prefixEnd_1092893 41568845402540576652695 := by
  unfold tailWord_1092893
  simp only [CollatzResearch.WordTrace]
  refine ⟨39861082429642787109443333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26574054953095191406295555 39861082429642787109443333)
  ·
    refine ⟨7473952955558022583020625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39861082429642787109443333 7473952955558022583020625)
    ·
      refine ⟨5605464716668516937265469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7473952955558022583020625 5605464716668516937265469)
      ·
        refine ⟨2102049268750693851474551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5605464716668516937265469 2102049268750693851474551)
        ·
          refine ⟨3153073903126040777211827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102049268750693851474551 3153073903126040777211827)
          ·
            refine ⟨4729610854689061165817741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153073903126040777211827 4729610854689061165817741)
            ·
              refine ⟨1773604070508397937181653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4729610854689061165817741 1773604070508397937181653)
              ·
                refine ⟨41568845402540576652695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1773604070508397937181653 41568845402540576652695)
                ·
                  rfl

theorem cell22_1092893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 7].length) (baseStart_1092893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1092893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1092893 prefixEnd_1092893 := by exact prefixLift 1092893
  have htrace : WordTrace (prefixWord ++ tailWord_1092893) baseStart_1092893 baseEnd_1092893 := by
    simpa [prefixWord, tailWord_1092893, baseEnd_1092893] using wordTrace_append hprefix tailTrace_1092893
  have hstable : (prefixWord ++ tailWord_1092893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092893).length < 2 ^ (prefixWord ++ tailWord_1092893).sum := by decide
  have hdescent : baseEnd_1092893 < baseStart_1092893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093000 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 6]
def baseStart_1093000 : Nat := 118140960795 + 1093000 * 2 ^ 59
def prefixEnd_1093000 : Nat := 4983230072969 + 3 ^ 40 * 1093000 * 2
def baseEnd_1093000 : Nat := 124718745636517525816309

theorem tailTrace_1093000 : CollatzResearch.WordTrace tailWord_1093000 prefixEnd_1093000 124718745636517525816309 := by
  unfold tailWord_1093000
  simp only [CollatzResearch.WordTrace]
  refine ⟨19932492520127572191794227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26576656693503429589058969 19932492520127572191794227)
  ·
    refine ⟨29898738780191358287691341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19932492520127572191794227 29898738780191358287691341)
    ·
      refine ⟨11212027042571759357884253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29898738780191358287691341 11212027042571759357884253)
      ·
        refine ⟨4204510140964409759206595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11212027042571759357884253 4204510140964409759206595)
        ·
          refine ⟨6306765211446614638809893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204510140964409759206595 6306765211446614638809893)
          ·
            refine ⟨1182518477146240244776855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6306765211446614638809893 1182518477146240244776855)
            ·
              refine ⟨1773777715719360367165283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182518477146240244776855 1773777715719360367165283)
              ·
                refine ⟨2660666573579040550747925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773777715719360367165283 2660666573579040550747925)
                ·
                  refine ⟨124718745636517525816309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2660666573579040550747925 124718745636517525816309)
                  ·
                    rfl

theorem cell22_1093000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_1093000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093000 prefixEnd_1093000 := by exact prefixLift 1093000
  have htrace : WordTrace (prefixWord ++ tailWord_1093000) baseStart_1093000 baseEnd_1093000 := by
    simpa [prefixWord, tailWord_1093000, baseEnd_1093000] using wordTrace_append hprefix tailTrace_1093000
  have hstable : (prefixWord ++ tailWord_1093000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093000).length < 2 ^ (prefixWord ++ tailWord_1093000).sum := by decide
  have hdescent : baseEnd_1093000 < baseStart_1093000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093032 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1093032 : Nat := 118140960795 + 1093032 * 2 ^ 59
def prefixEnd_1093032 : Nat := 4983230072969 + 3 ^ 40 * 1093032 * 2
def baseEnd_1093032 : Nat := 374167191163515160648829

theorem tailTrace_1093032 : CollatzResearch.WordTrace tailWord_1093032 prefixEnd_1093032 374167191163515160648829 := by
  unfold tailWord_1093032
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933076088069606924376675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26577434784092809232502233 19933076088069606924376675)
  ·
    refine ⟨29899614132104410386565013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19933076088069606924376675 29899614132104410386565013)
    ·
      refine ⟨1401544412442394236870235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29899614132104410386565013 1401544412442394236870235)
      ·
        refine ⟨2102316618663591355305353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401544412442394236870235 2102316618663591355305353)
        ·
          refine ⟨1576737463997693516479015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2102316618663591355305353 1576737463997693516479015)
          ·
            refine ⟨2365106195996540274718523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576737463997693516479015 2365106195996540274718523)
            ·
              refine ⟨3547659293994810412077785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365106195996540274718523 3547659293994810412077785)
              ·
                refine ⟨2660744470496107809058339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547659293994810412077785 2660744470496107809058339)
                ·
                  refine ⟨3991116705744161713587509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660744470496107809058339 3991116705744161713587509)
                  ·
                    refine ⟨374167191163515160648829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3991116705744161713587509 374167191163515160648829)
                    ·
                      rfl

theorem cell22_1093032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1093032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093032 prefixEnd_1093032 := by exact prefixLift 1093032
  have htrace : WordTrace (prefixWord ++ tailWord_1093032) baseStart_1093032 baseEnd_1093032 := by
    simpa [prefixWord, tailWord_1093032, baseEnd_1093032] using wordTrace_append hprefix tailTrace_1093032
  have hstable : (prefixWord ++ tailWord_1093032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093032).length < 2 ^ (prefixWord ++ tailWord_1093032).sum := by decide
  have hdescent : baseEnd_1093032 < baseStart_1093032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093122 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1093122 : Nat := 118140960795 + 1093122 * 2 ^ 59
def prefixEnd_1093122 : Nat := 4983230072969 + 3 ^ 40 * 1093122 * 2
def baseEnd_1093122 : Nat := 374198000002784925898553

theorem tailTrace_1093122 : CollatzResearch.WordTrace tailWord_1093122 prefixEnd_1093122 374198000002784925898553 := by
  unfold tailWord_1093122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967358686453289804882405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26579623163875439479686413 9967358686453289804882405)
  ·
    refine ⟨1868879753709991838415451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9967358686453289804882405 1868879753709991838415451)
    ·
      refine ⟨2803319630564987757623177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868879753709991838415451 2803319630564987757623177)
      ·
        refine ⟨2102489722923740818217383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2803319630564987757623177 2102489722923740818217383)
        ·
          refine ⟨3153734584385611227326075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102489722923740818217383 3153734584385611227326075)
          ·
            refine ⟨4730601876578416840989113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153734584385611227326075 4730601876578416840989113)
            ·
              refine ⟨3547951407433812630741835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730601876578416840989113 3547951407433812630741835)
              ·
                refine ⟨5321927111150718946112753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547951407433812630741835 5321927111150718946112753)
                ·
                  refine ⟨3991445333363039209584565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5321927111150718946112753 3991445333363039209584565)
                  ·
                    refine ⟨374198000002784925898553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3991445333363039209584565 374198000002784925898553)
                    ·
                      rfl

theorem cell22_1093122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1093122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093122 prefixEnd_1093122 := by exact prefixLift 1093122
  have htrace : WordTrace (prefixWord ++ tailWord_1093122) baseStart_1093122 baseEnd_1093122 := by
    simpa [prefixWord, tailWord_1093122, baseEnd_1093122] using wordTrace_append hprefix tailTrace_1093122
  have hstable : (prefixWord ++ tailWord_1093122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093122).length < 2 ^ (prefixWord ++ tailWord_1093122).sum := by decide
  have hdescent : baseEnd_1093122 < baseStart_1093122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093124 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 5]
def baseStart_1093124 : Nat := 118140960795 + 1093124 * 2 ^ 59
def prefixEnd_1093124 : Nat := 4983230072969 + 3 ^ 40 * 1093124 * 2
def baseEnd_1093124 : Nat := 124732894881219195782849

theorem tailTrace_1093124 : CollatzResearch.WordTrace tailWord_1093124 prefixEnd_1093124 124732894881219195782849 := by
  unfold tailWord_1093124
  simp only [CollatzResearch.WordTrace]
  refine ⟨19934753845902956780551213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26579671794537275707401617 19934753845902956780551213)
  ·
    refine ⟨7475532692213608792706705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19934753845902956780551213 7475532692213608792706705)
    ·
      refine ⟨5606649519160206594530029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7475532692213608792706705 5606649519160206594530029)
      ·
        refine ⟨2102493569685077472948761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5606649519160206594530029 2102493569685077472948761)
        ·
          refine ⟨1576870177263808104711571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2102493569685077472948761 1576870177263808104711571)
          ·
            refine ⟨2365305265895712157067357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576870177263808104711571 2365305265895712157067357)
            ·
              refine ⟨886989474710892058900259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2365305265895712157067357 886989474710892058900259)
              ·
                refine ⟨1330484212066338088350389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886989474710892058900259 1330484212066338088350389)
                ·
                  refine ⟨124732894881219195782849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330484212066338088350389 124732894881219195782849)
                  ·
                    rfl

theorem cell22_1093124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_1093124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093124 prefixEnd_1093124 := by exact prefixLift 1093124
  have htrace : WordTrace (prefixWord ++ tailWord_1093124) baseStart_1093124 baseEnd_1093124 := by
    simpa [prefixWord, tailWord_1093124, baseEnd_1093124] using wordTrace_append hprefix tailTrace_1093124
  have hstable : (prefixWord ++ tailWord_1093124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093124).length < 2 ^ (prefixWord ++ tailWord_1093124).sum := by decide
  have hdescent : baseEnd_1093124 < baseStart_1093124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093195 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 5, 3]
def baseStart_1093195 : Nat := 118140960795 + 1093195 * 2 ^ 59
def prefixEnd_1093195 : Nat := 4983230072969 + 3 ^ 40 * 1093195 * 2
def baseEnd_1093195 : Nat := 374222989394637068823329

theorem tailTrace_1093195 : CollatzResearch.WordTrace tailWord_1093195 prefixEnd_1093195 374222989394637068823329 := by
  unfold tailWord_1093195
  simp only [CollatzResearch.WordTrace]
  refine ⟨39872097274548692686937039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26581398183032461791291359 39872097274548692686937039)
  ·
    refine ⟨59808145911823039030405559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39872097274548692686937039 59808145911823039030405559)
    ·
      refine ⟨89712218867734558545608339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59808145911823039030405559 89712218867734558545608339)
      ·
        refine ⟨134568328301601837818412509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89712218867734558545608339 134568328301601837818412509)
        ·
          refine ⟨50463123113100689181904691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134568328301601837818412509 50463123113100689181904691)
          ·
            refine ⟨75694684669651033772857037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50463123113100689181904691 75694684669651033772857037)
            ·
              refine ⟨28385506751119137664821389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75694684669651033772857037 28385506751119137664821389)
              ·
                refine ⟨10644565031669676624308021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28385506751119137664821389 10644565031669676624308021)
                ·
                  refine ⟨997927971719032183528877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10644565031669676624308021 997927971719032183528877)
                  ·
                    refine ⟨374222989394637068823329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 997927971719032183528877 374222989394637068823329)
                    ·
                      rfl

theorem cell22_1093195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 3].length) (baseStart_1093195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093195 prefixEnd_1093195 := by exact prefixLift 1093195
  have htrace : WordTrace (prefixWord ++ tailWord_1093195) baseStart_1093195 baseEnd_1093195 := by
    simpa [prefixWord, tailWord_1093195, baseEnd_1093195] using wordTrace_append hprefix tailTrace_1093195
  have hstable : (prefixWord ++ tailWord_1093195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093195).length < 2 ^ (prefixWord ++ tailWord_1093195).sum := by decide
  have hdescent : baseEnd_1093195 < baseStart_1093195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093225 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 5]
def baseStart_1093225 : Nat := 118140960795 + 1093225 * 2 ^ 59
def prefixEnd_1093225 : Nat := 4983230072969 + 3 ^ 40 * 1093225 * 2
def baseEnd_1093225 : Nat := 124744419669242330191079

theorem tailTrace_1093225 : CollatzResearch.WordTrace tailWord_1093225 prefixEnd_1093225 124744419669242330191079 := by
  unfold tailWord_1093225
  simp only [CollatzResearch.WordTrace]
  refine ⟨39873191464440007810529129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26582127642960005207019419 39873191464440007810529129)
  ·
    refine ⟨29904893598330005857896847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39873191464440007810529129 29904893598330005857896847)
    ·
      refine ⟨44857340397495008786845271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29904893598330005857896847 44857340397495008786845271)
      ·
        refine ⟨67286010596242513180267907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44857340397495008786845271 67286010596242513180267907)
        ·
          refine ⟨100929015894363769770401861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67286010596242513180267907 100929015894363769770401861)
          ·
            refine ⟨18924190480193206831950349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100929015894363769770401861 18924190480193206831950349)
            ·
              refine ⟨7096571430072452561981381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18924190480193206831950349 7096571430072452561981381)
              ·
                refine ⟨1330607143138584855371509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7096571430072452561981381 1330607143138584855371509)
                ·
                  refine ⟨124744419669242330191079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330607143138584855371509 124744419669242330191079)
                  ·
                    rfl

theorem cell22_1093225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_1093225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093225 prefixEnd_1093225 := by exact prefixLift 1093225
  have htrace : WordTrace (prefixWord ++ tailWord_1093225) baseStart_1093225 baseEnd_1093225 := by
    simpa [prefixWord, tailWord_1093225, baseEnd_1093225] using wordTrace_append hprefix tailTrace_1093225
  have hstable : (prefixWord ++ tailWord_1093225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093225).length < 2 ^ (prefixWord ++ tailWord_1093225).sum := by decide
  have hdescent : baseEnd_1093225 < baseStart_1093225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093276 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 5]
def baseStart_1093276 : Nat := 118140960795 + 1093276 * 2 ^ 59
def prefixEnd_1093276 : Nat := 4983230072969 + 3 ^ 40 * 1093276 * 2
def baseEnd_1093276 : Nat := 124750239116659952516027

theorem tailTrace_1093276 : CollatzResearch.WordTrace tailWord_1093276 prefixEnd_1093276 124750239116659952516027 := by
  unfold tailWord_1093276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19937525793627621760317841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26583367724836829013757121 19937525793627621760317841)
  ·
    refine ⟨14953144345220716320238381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19937525793627621760317841 14953144345220716320238381)
    ·
      refine ⟨5607429129457768620089393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14953144345220716320238381 5607429129457768620089393)
      ·
        refine ⟨4205571847093326465067045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5607429129457768620089393 4205571847093326465067045)
        ·
          refine ⟨788544721329998712200071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4205571847093326465067045 788544721329998712200071)
          ·
            refine ⟨1182817081994998068300107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788544721329998712200071 1182817081994998068300107)
            ·
              refine ⟨1774225622992497102450161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182817081994998068300107 1774225622992497102450161)
              ·
                refine ⟨1330669217244372826837621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1774225622992497102450161 1330669217244372826837621)
                ·
                  refine ⟨124750239116659952516027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330669217244372826837621 124750239116659952516027)
                  ·
                    rfl

theorem cell22_1093276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_1093276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093276 prefixEnd_1093276 := by exact prefixLift 1093276
  have htrace : WordTrace (prefixWord ++ tailWord_1093276) baseStart_1093276 baseEnd_1093276 := by
    simpa [prefixWord, tailWord_1093276, baseEnd_1093276] using wordTrace_append hprefix tailTrace_1093276
  have hstable : (prefixWord ++ tailWord_1093276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093276).length < 2 ^ (prefixWord ++ tailWord_1093276).sum := by decide
  have hdescent : baseEnd_1093276 < baseStart_1093276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093285 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1093285 : Nat := 118140960795 + 1093285 * 2 ^ 59
def prefixEnd_1093285 : Nat := 4983230072969 + 3 ^ 40 * 1093285 * 2
def baseEnd_1093285 : Nat := 374253798233906834073053

theorem tailTrace_1093285 : CollatzResearch.WordTrace tailWord_1093285 prefixEnd_1093285 374253798233906834073053 := by
  unfold tailWord_1093285
  simp only [CollatzResearch.WordTrace]
  refine ⟨39875379844222638057713309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26583586562815092038475539 39875379844222638057713309)
  ·
    refine ⟨14953267441583489271642491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39875379844222638057713309 14953267441583489271642491)
    ·
      refine ⟨22429901162375233907463737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14953267441583489271642491 22429901162375233907463737)
      ·
        refine ⟨16822425871781425430597803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22429901162375233907463737 16822425871781425430597803)
        ·
          refine ⟨25233638807672138145896705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16822425871781425430597803 25233638807672138145896705)
          ·
            refine ⟨18925229105754103609422529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25233638807672138145896705 18925229105754103609422529)
            ·
              refine ⟨14193921829315577707066897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18925229105754103609422529 14193921829315577707066897)
              ·
                refine ⟨10645441371986683280300173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14193921829315577707066897 10645441371986683280300173)
                ·
                  refine ⟨3992040514495006230112565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10645441371986683280300173 3992040514495006230112565)
                  ·
                    refine ⟨374253798233906834073053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3992040514495006230112565 374253798233906834073053)
                    ·
                      rfl

theorem cell22_1093285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1093285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093285 prefixEnd_1093285 := by exact prefixLift 1093285
  have htrace : WordTrace (prefixWord ++ tailWord_1093285) baseStart_1093285 baseEnd_1093285 := by
    simpa [prefixWord, tailWord_1093285, baseEnd_1093285] using wordTrace_append hprefix tailTrace_1093285
  have hstable : (prefixWord ++ tailWord_1093285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093285).length < 2 ^ (prefixWord ++ tailWord_1093285).sum := by decide
  have hdescent : baseEnd_1093285 < baseStart_1093285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093314 : List Nat := [3, 5, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1093314 : Nat := 118140960795 + 1093314 * 2 ^ 59
def prefixEnd_1093314 : Nat := 4983230072969 + 3 ^ 40 * 1093314 * 2
def baseEnd_1093314 : Nat := 374263725526560425097965

theorem tailTrace_1093314 : CollatzResearch.WordTrace tailWord_1093314 prefixEnd_1093314 374263725526560425097965 := by
  unfold tailWord_1093314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9969109390279394002629749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26584291707411717340345997 9969109390279394002629749)
  ·
    refine ⟨934604005338693187746539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9969109390279394002629749 934604005338693187746539)
    ·
      refine ⟨1401906008008039781619809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934604005338693187746539 1401906008008039781619809)
      ·
        refine ⟨1051429506006029836214857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1401906008008039781619809 1051429506006029836214857)
        ·
          refine ⟨788572129504522377161143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1051429506006029836214857 788572129504522377161143)
          ·
            refine ⟨1182858194256783565741715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788572129504522377161143 1182858194256783565741715)
            ·
              refine ⟨1774287291385175348612573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182858194256783565741715 1774287291385175348612573)
              ·
                refine ⟨665357734269440755729715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1774287291385175348612573 665357734269440755729715)
                ·
                  refine ⟨998036601404161133594573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665357734269440755729715 998036601404161133594573)
                  ·
                    refine ⟨374263725526560425097965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 998036601404161133594573 374263725526560425097965)
                    ·
                      rfl

theorem cell22_1093314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1093314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093314 prefixEnd_1093314 := by exact prefixLift 1093314
  have htrace : WordTrace (prefixWord ++ tailWord_1093314) baseStart_1093314 baseEnd_1093314 := by
    simpa [prefixWord, tailWord_1093314, baseEnd_1093314] using wordTrace_append hprefix tailTrace_1093314
  have hstable : (prefixWord ++ tailWord_1093314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093314).length < 2 ^ (prefixWord ++ tailWord_1093314).sum := by decide
  have hdescent : baseEnd_1093314 < baseStart_1093314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093332 : List Nat := [2, 4, 1, 3, 1, 1, 10]
def baseStart_1093332 : Nat := 118140960795 + 1093332 * 2 ^ 59
def prefixEnd_1093332 : Nat := 4983230072969 + 3 ^ 40 * 1093332 * 2
def baseEnd_1093332 : Nat := 13861847677570902894367

theorem tailTrace_1093332 : CollatzResearch.WordTrace tailWord_1093332 prefixEnd_1093332 13861847677570902894367 := by
  unfold tailWord_1093332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19938547037526182542337125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26584729383368243389782833 19938547037526182542337125)
  ·
    refine ⟨3738477569536159226688211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19938547037526182542337125 3738477569536159226688211)
    ·
      refine ⟨5607716354304238840032317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3738477569536159226688211 5607716354304238840032317)
      ·
        refine ⟨2102893632864089565012119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5607716354304238840032317 2102893632864089565012119)
        ·
          refine ⟨3154340449296134347518179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102893632864089565012119 3154340449296134347518179)
          ·
            refine ⟨4731510673944201521277269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154340449296134347518179 4731510673944201521277269)
            ·
              refine ⟨13861847677570902894367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4731510673944201521277269 13861847677570902894367)
              ·
                rfl

theorem cell22_1093332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 10].length) (baseStart_1093332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093332 prefixEnd_1093332 := by exact prefixLift 1093332
  have htrace : WordTrace (prefixWord ++ tailWord_1093332) baseStart_1093332 baseEnd_1093332 := by
    simpa [prefixWord, tailWord_1093332, baseEnd_1093332] using wordTrace_append hprefix tailTrace_1093332
  have hstable : (prefixWord ++ tailWord_1093332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093332).length < 2 ^ (prefixWord ++ tailWord_1093332).sum := by decide
  have hdescent : baseEnd_1093332 < baseStart_1093332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093360 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 9]
def baseStart_1093360 : Nat := 118140960795 + 1093360 * 2 ^ 59
def prefixEnd_1093360 : Nat := 4983230072969 + 3 ^ 40 * 1093360 * 2
def baseEnd_1093360 : Nat := 124759824088877212815941

theorem tailTrace_1093360 : CollatzResearch.WordTrace tailWord_1093360 prefixEnd_1093360 124759824088877212815941 := by
  unfold tailWord_1093360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19939057659475462933346767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26585410212633950577795689 19939057659475462933346767)
  ·
    refine ⟨29908586489213194400020151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19939057659475462933346767 29908586489213194400020151)
    ·
      refine ⟨44862879733819791600030227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29908586489213194400020151 44862879733819791600030227)
      ·
        refine ⟨67294319600729687400045341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44862879733819791600030227 67294319600729687400045341)
        ·
          refine ⟨25235369850273632775017003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67294319600729687400045341 25235369850273632775017003)
          ·
            refine ⟨37853054775410449162525505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25235369850273632775017003 37853054775410449162525505)
            ·
              refine ⟨28389791081557836871894129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37853054775410449162525505 28389791081557836871894129)
              ·
                refine ⟨21292343311168377653920597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28389791081557836871894129 21292343311168377653920597)
                ·
                  refine ⟨124759824088877212815941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21292343311168377653920597 124759824088877212815941)
                  ·
                    rfl

theorem cell22_1093360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_1093360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093360 prefixEnd_1093360 := by exact prefixLift 1093360
  have htrace : WordTrace (prefixWord ++ tailWord_1093360) baseStart_1093360 baseEnd_1093360 := by
    simpa [prefixWord, tailWord_1093360, baseEnd_1093360] using wordTrace_append hprefix tailTrace_1093360
  have hstable : (prefixWord ++ tailWord_1093360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093360).length < 2 ^ (prefixWord ++ tailWord_1093360).sum := by decide
  have hdescent : baseEnd_1093360 < baseStart_1093360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093389 : List Nat := [1, 7, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1093389 : Nat := 118140960795 + 1093389 * 2 ^ 59
def prefixEnd_1093389 : Nat := 4983230072969 + 3 ^ 40 * 1093389 * 2
def baseEnd_1093389 : Nat := 124763133186428409824245

theorem tailTrace_1093389 : CollatzResearch.WordTrace tailWord_1093389 prefixEnd_1093389 124763133186428409824245 := by
  unfold tailWord_1093389
  simp only [CollatzResearch.WordTrace]
  refine ⟨39879173035845863819499221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26586115357230575879666147 39879173035845863819499221)
  ·
    refine ⟨934668118027637433269513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39879173035845863819499221 934668118027637433269513)
    ·
      refine ⟨701001088520728074952135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 934668118027637433269513 701001088520728074952135)
      ·
        refine ⟨1051501632781092112428203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701001088520728074952135 1051501632781092112428203)
        ·
          refine ⟨1577252449171638168642305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051501632781092112428203 1577252449171638168642305)
          ·
            refine ⟨1182939336878728626481729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577252449171638168642305 1182939336878728626481729)
            ·
              refine ⟨887204502659046469861297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182939336878728626481729 887204502659046469861297)
              ·
                refine ⟨665403376994284852395973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887204502659046469861297 665403376994284852395973)
                ·
                  refine ⟨124763133186428409824245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 665403376994284852395973 124763133186428409824245)
                  ·
                    rfl

theorem cell22_1093389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1093389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093389 prefixEnd_1093389 := by exact prefixLift 1093389
  have htrace : WordTrace (prefixWord ++ tailWord_1093389) baseStart_1093389 baseEnd_1093389 := by
    simpa [prefixWord, tailWord_1093389, baseEnd_1093389] using wordTrace_append hprefix tailTrace_1093389
  have hstable : (prefixWord ++ tailWord_1093389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093389).length < 2 ^ (prefixWord ++ tailWord_1093389).sum := by decide
  have hdescent : baseEnd_1093389 < baseStart_1093389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093407 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 5, 4]
def baseStart_1093407 : Nat := 118140960795 + 1093407 * 2 ^ 59
def prefixEnd_1093407 : Nat := 4983230072969 + 3 ^ 40 * 1093407 * 2
def baseEnd_1093407 : Nat := 374295561327139182522679

theorem tailTrace_1093407 : CollatzResearch.WordTrace tailWord_1093407 prefixEnd_1093407 374295561327139182522679 := by
  unfold tailWord_1093407
  simp only [CollatzResearch.WordTrace]
  refine ⟨39879829549780652893654475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26586553033187101929102983 39879829549780652893654475)
  ·
    refine ⟨59819744324670979340481713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39879829549780652893654475 59819744324670979340481713)
    ·
      refine ⟨44864808243503234505361285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59819744324670979340481713 44864808243503234505361285)
      ·
        refine ⟨8412151545656856469755241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44864808243503234505361285 8412151545656856469755241)
        ·
          refine ⟨6309113659242642352316431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8412151545656856469755241 6309113659242642352316431)
          ·
            refine ⟨9463670488863963528474647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309113659242642352316431 9463670488863963528474647)
            ·
              refine ⟨14195505733295945292711971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9463670488863963528474647 14195505733295945292711971)
              ·
                refine ⟨21293258599943917939067957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14195505733295945292711971 21293258599943917939067957)
                ·
                  refine ⟨1996242993744742306787621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21293258599943917939067957 1996242993744742306787621)
                  ·
                    refine ⟨374295561327139182522679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1996242993744742306787621 374295561327139182522679)
                    ·
                      rfl

theorem cell22_1093407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_1093407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093407 prefixEnd_1093407 := by exact prefixLift 1093407
  have htrace : WordTrace (prefixWord ++ tailWord_1093407) baseStart_1093407 baseEnd_1093407 := by
    simpa [prefixWord, tailWord_1093407, baseEnd_1093407] using wordTrace_append hprefix tailTrace_1093407
  have hstable : (prefixWord ++ tailWord_1093407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093407).length < 2 ^ (prefixWord ++ tailWord_1093407).sum := by decide
  have hdescent : baseEnd_1093407 < baseStart_1093407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093484 : List Nat := [2, 2, 1, 1, 4, 2, 4, 6]
def baseStart_1093484 : Nat := 118140960795 + 1093484 * 2 ^ 59
def prefixEnd_1093484 : Nat := 4983230072969 + 3 ^ 40 * 1093484 * 2
def baseEnd_1093484 : Nat := 41591324444526294260827

theorem tailTrace_1093484 : CollatzResearch.WordTrace tailWord_1093484 prefixEnd_1093484 41591324444526294260827 := by
  unfold tailWord_1093484
  simp only [CollatzResearch.WordTrace]
  refine ⟨19941318985250847522103753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26588425313667796696138337 19941318985250847522103753)
  ·
    refine ⟨14955989238938135641577815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19941318985250847522103753 14955989238938135641577815)
    ·
      refine ⟨22433983858407203462366723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14955989238938135641577815 22433983858407203462366723)
      ·
        refine ⟨33650975787610805193550085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22433983858407203462366723 33650975787610805193550085)
        ·
          refine ⟨6309557960177025973790641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33650975787610805193550085 6309557960177025973790641)
          ·
            refine ⟨4732168470132769480342981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6309557960177025973790641 4732168470132769480342981)
            ·
              refine ⟨887281588149894277564309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4732168470132769480342981 887281588149894277564309)
              ·
                refine ⟨41591324444526294260827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 887281588149894277564309 41591324444526294260827)
                ·
                  rfl

theorem cell22_1093484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 6].length) (baseStart_1093484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093484 prefixEnd_1093484 := by exact prefixLift 1093484
  have htrace : WordTrace (prefixWord ++ tailWord_1093484) baseStart_1093484 baseEnd_1093484 := by
    simpa [prefixWord, tailWord_1093484, baseEnd_1093484] using wordTrace_append hprefix tailTrace_1093484
  have hstable : (prefixWord ++ tailWord_1093484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093484).length < 2 ^ (prefixWord ++ tailWord_1093484).sum := by decide
  have hdescent : baseEnd_1093484 < baseStart_1093484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093604 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1093604 : Nat := 118140960795 + 1093604 * 2 ^ 59
def prefixEnd_1093604 : Nat := 4983230072969 + 3 ^ 40 * 1093604 * 2
def baseEnd_1093604 : Nat := 374362998453096335347075

theorem tailTrace_1093604 : CollatzResearch.WordTrace tailWord_1093604 prefixEnd_1093604 374362998453096335347075 := by
  unfold tailWord_1093604
  simp only [CollatzResearch.WordTrace]
  refine ⟨19943507365033477769287933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26591343153377970359050577 19943507365033477769287933)
  ·
    refine ⟨7478815261887554163482975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19943507365033477769287933 7478815261887554163482975)
    ·
      refine ⟨11218222892831331245224463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7478815261887554163482975 11218222892831331245224463)
      ·
        refine ⟨16827334339246996867836695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11218222892831331245224463 16827334339246996867836695)
        ·
          refine ⟨25241001508870495301755043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16827334339246996867836695 25241001508870495301755043)
          ·
            refine ⟨37861502263305742952632565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25241001508870495301755043 37861502263305742952632565)
            ·
              refine ⟨3549515837184913401809303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37861502263305742952632565 3549515837184913401809303)
              ·
                refine ⟨5324273755777370102713955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549515837184913401809303 5324273755777370102713955)
                ·
                  refine ⟨7986410633666055154070933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5324273755777370102713955 7986410633666055154070933)
                  ·
                    refine ⟨374362998453096335347075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7986410633666055154070933 374362998453096335347075)
                    ·
                      rfl

theorem cell22_1093604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1093604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093604 prefixEnd_1093604 := by exact prefixLift 1093604
  have htrace : WordTrace (prefixWord ++ tailWord_1093604) baseStart_1093604 baseEnd_1093604 := by
    simpa [prefixWord, tailWord_1093604, baseEnd_1093604] using wordTrace_append hprefix tailTrace_1093604
  have hstable : (prefixWord ++ tailWord_1093604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093604).length < 2 ^ (prefixWord ++ tailWord_1093604).sum := by decide
  have hdescent : baseEnd_1093604 < baseStart_1093604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093651 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 3, 3]
def baseStart_1093651 : Nat := 118140960795 + 1093651 * 2 ^ 59
def prefixEnd_1093651 : Nat := 4983230072969 + 3 ^ 40 * 1093651 * 2
def baseEnd_1093651 : Nat := 374379087513603879421931

theorem tailTrace_1093651 : CollatzResearch.WordTrace tailWord_1093651 prefixEnd_1093651 374379087513603879421931 := by
  unfold tailWord_1093651
  simp only [CollatzResearch.WordTrace]
  refine ⟨39888728960896682565536807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26592485973931121710357871 39888728960896682565536807)
  ·
    refine ⟨59833093441345023848305211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39888728960896682565536807 59833093441345023848305211)
    ·
      refine ⟨89749640162017535772457817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59833093441345023848305211 89749640162017535772457817)
      ·
        refine ⟨67312230121513151829343363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89749640162017535772457817 67312230121513151829343363)
        ·
          refine ⟨100968345182269727744015045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67312230121513151829343363 100968345182269727744015045)
          ·
            refine ⟨18931564721675573952002821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100968345182269727744015045 18931564721675573952002821)
            ·
              refine ⟨3549668385314170116000529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18931564721675573952002821 3549668385314170116000529)
              ·
                refine ⟨2662251288985627587000397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3549668385314170116000529 2662251288985627587000397)
                ·
                  refine ⟨998344233369610345125149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2662251288985627587000397 998344233369610345125149)
                  ·
                    refine ⟨374379087513603879421931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 998344233369610345125149 374379087513603879421931)
                    ·
                      rfl

theorem cell22_1093651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 3].length) (baseStart_1093651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093651 prefixEnd_1093651 := by exact prefixLift 1093651
  have htrace : WordTrace (prefixWord ++ tailWord_1093651) baseStart_1093651 baseEnd_1093651 := by
    simpa [prefixWord, tailWord_1093651, baseEnd_1093651] using wordTrace_append hprefix tailTrace_1093651
  have hstable : (prefixWord ++ tailWord_1093651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093651).length < 2 ^ (prefixWord ++ tailWord_1093651).sum := by decide
  have hdescent : baseEnd_1093651 < baseStart_1093651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093653 : List Nat := [1, 3, 2, 1, 5, 2, 2, 6]
def baseStart_1093653 : Nat := 118140960795 + 1093653 * 2 ^ 59
def prefixEnd_1093653 : Nat := 4983230072969 + 3 ^ 40 * 1093653 * 2
def baseEnd_1093653 : Nat := 41597752461608504541325

theorem tailTrace_1093653 : CollatzResearch.WordTrace tailWord_1093653 prefixEnd_1093653 41597752461608504541325 := by
  unfold tailWord_1093653
  simp only [CollatzResearch.WordTrace]
  refine ⟨39888801906889436907109613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26592534604592957938073075 39888801906889436907109613)
  ·
    refine ⟨14958300715083538840166105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39888801906889436907109613 14958300715083538840166105)
    ·
      refine ⟨11218725536312654130124579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14958300715083538840166105 11218725536312654130124579)
      ·
        refine ⟨16828088304468981195186869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11218725536312654130124579 16828088304468981195186869)
        ·
          refine ⟨1577633278543966987048769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16828088304468981195186869 1577633278543966987048769)
          ·
            refine ⟨1183224958907975240286577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577633278543966987048769 1183224958907975240286577)
            ·
              refine ⟨887418719180981430214933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183224958907975240286577 887418719180981430214933)
              ·
                refine ⟨41597752461608504541325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 887418719180981430214933 41597752461608504541325)
                ·
                  rfl

theorem cell22_1093653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 6].length) (baseStart_1093653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093653 prefixEnd_1093653 := by exact prefixLift 1093653
  have htrace : WordTrace (prefixWord ++ tailWord_1093653) baseStart_1093653 baseEnd_1093653 := by
    simpa [prefixWord, tailWord_1093653, baseEnd_1093653] using wordTrace_append hprefix tailTrace_1093653
  have hstable : (prefixWord ++ tailWord_1093653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093653).length < 2 ^ (prefixWord ++ tailWord_1093653).sum := by decide
  have hdescent : baseEnd_1093653 < baseStart_1093653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093679 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 2, 5]
def baseStart_1093679 : Nat := 118140960795 + 1093679 * 2 ^ 59
def prefixEnd_1093679 : Nat := 4983230072969 + 3 ^ 40 * 1093679 * 2
def baseEnd_1093679 : Nat := 374388672485821139721845

theorem tailTrace_1093679 : CollatzResearch.WordTrace tailWord_1093679 prefixEnd_1093679 374388672485821139721845 := by
  unfold tailWord_1093679
  simp only [CollatzResearch.WordTrace]
  refine ⟨39889750204795243347556091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26593166803196828898370727 39889750204795243347556091)
  ·
    refine ⟨59834625307192865021334137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39889750204795243347556091 59834625307192865021334137)
    ·
      refine ⟨44875968980394648766000603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59834625307192865021334137 44875968980394648766000603)
      ·
        refine ⟨67313953470591973149000905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44875968980394648766000603 67313953470591973149000905)
        ·
          refine ⟨50485465102943979861750679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67313953470591973149000905 50485465102943979861750679)
          ·
            refine ⟨75728197654415969792626019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50485465102943979861750679 75728197654415969792626019)
            ·
              refine ⟨113592296481623954688939029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75728197654415969792626019 113592296481623954688939029)
              ·
                refine ⟨5324638897576122876044017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113592296481623954688939029 5324638897576122876044017)
                ·
                  refine ⟨3993479173182092157033013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5324638897576122876044017 3993479173182092157033013)
                  ·
                    refine ⟨374388672485821139721845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3993479173182092157033013 374388672485821139721845)
                    ·
                      rfl

theorem cell22_1093679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_1093679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093679 prefixEnd_1093679 := by exact prefixLift 1093679
  have htrace : WordTrace (prefixWord ++ tailWord_1093679) baseStart_1093679 baseEnd_1093679 := by
    simpa [prefixWord, tailWord_1093679, baseEnd_1093679] using wordTrace_append hprefix tailTrace_1093679
  have hstable : (prefixWord ++ tailWord_1093679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093679).length < 2 ^ (prefixWord ++ tailWord_1093679).sum := by decide
  have hdescent : baseEnd_1093679 < baseStart_1093679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093741 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1093741 : Nat := 118140960795 + 1093741 * 2 ^ 59
def prefixEnd_1093741 : Nat := 4983230072969 + 3 ^ 40 * 1093741 * 2
def baseEnd_1093741 : Nat := 374409896352873644671655

theorem tailTrace_1093741 : CollatzResearch.WordTrace tailWord_1093741 prefixEnd_1093741 374409896352873644671655 := by
  unfold tailWord_1093741
  simp only [CollatzResearch.WordTrace]
  refine ⟨39892011530570627936313077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26594674353713751957542051 39892011530570627936313077)
  ·
    refine ⟨3739876080990996369029351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39892011530570627936313077 3739876080990996369029351)
    ·
      refine ⟨5609814121486494553544027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3739876080990996369029351 5609814121486494553544027)
      ·
        refine ⟨8414721182229741830316041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5609814121486494553544027 8414721182229741830316041)
        ·
          refine ⟨6311040886672306372737031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8414721182229741830316041 6311040886672306372737031)
          ·
            refine ⟨9466561330008459559105547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6311040886672306372737031 9466561330008459559105547)
            ·
              refine ⟨14199841995012689338658321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9466561330008459559105547 14199841995012689338658321)
              ·
                refine ⟨10649881496259517003993741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14199841995012689338658321 10649881496259517003993741)
                ·
                  refine ⟨3993705561097318876497653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10649881496259517003993741 3993705561097318876497653)
                  ·
                    refine ⟨374409896352873644671655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3993705561097318876497653 374409896352873644671655)
                    ·
                      rfl

theorem cell22_1093741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1093741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093741 prefixEnd_1093741 := by exact prefixLift 1093741
  have htrace : WordTrace (prefixWord ++ tailWord_1093741) baseStart_1093741 baseEnd_1093741 := by
    simpa [prefixWord, tailWord_1093741, baseEnd_1093741] using wordTrace_append hprefix tailTrace_1093741
  have hstable : (prefixWord ++ tailWord_1093741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093741).length < 2 ^ (prefixWord ++ tailWord_1093741).sum := by decide
  have hdescent : baseEnd_1093741 < baseStart_1093741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093743 : List Nat := [1, 1, 2, 1, 3, 5, 1, 4, 4]
def baseStart_1093743 : Nat := 118140960795 + 1093743 * 2 ^ 59
def prefixEnd_1093743 : Nat := 4983230072969 + 3 ^ 40 * 1093743 * 2
def baseEnd_1093743 : Nat := 124803526997915435373883

theorem tailTrace_1093743 : CollatzResearch.WordTrace tailWord_1093743 prefixEnd_1093743 124803526997915435373883 := by
  unfold tailWord_1093743
  simp only [CollatzResearch.WordTrace]
  refine ⟨39892084476563382277885883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26594722984375588185257255 39892084476563382277885883)
  ·
    refine ⟨59838126714845073416828825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39892084476563382277885883 59838126714845073416828825)
    ·
      refine ⟨44878595036133805062621619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59838126714845073416828825 44878595036133805062621619)
      ·
        refine ⟨67317892554200707593932429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44878595036133805062621619 67317892554200707593932429)
        ·
          refine ⟨25244209707825265347724661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67317892554200707593932429 25244209707825265347724661)
          ·
            refine ⟨2366644660108618626349187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25244209707825265347724661 2366644660108618626349187)
            ·
              refine ⟨3549966990162927939523781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366644660108618626349187 3549966990162927939523781)
              ·
                refine ⟨665618810655548988660709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3549966990162927939523781 665618810655548988660709)
                ·
                  refine ⟨124803526997915435373883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 665618810655548988660709 124803526997915435373883)
                  ·
                    rfl

theorem cell22_1093743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 4].length) (baseStart_1093743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093743 prefixEnd_1093743 := by exact prefixLift 1093743
  have htrace : WordTrace (prefixWord ++ tailWord_1093743) baseStart_1093743 baseEnd_1093743 := by
    simpa [prefixWord, tailWord_1093743, baseEnd_1093743] using wordTrace_append hprefix tailTrace_1093743
  have hstable : (prefixWord ++ tailWord_1093743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093743).length < 2 ^ (prefixWord ++ tailWord_1093743).sum := by decide
  have hdescent : baseEnd_1093743 < baseStart_1093743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093822 : List Nat := [4, 2, 1, 1, 5, 1, 2, 6]
def baseStart_1093822 : Nat := 118140960795 + 1093822 * 2 ^ 59
def prefixEnd_1093822 : Nat := 4983230072969 + 3 ^ 40 * 1093822 * 2
def baseEnd_1093822 : Nat := 41604180478690714821823

theorem tailTrace_1093822 : CollatzResearch.WordTrace tailWord_1093822 prefixEnd_1093822 41604180478690714821823 := by
  unfold tailWord_1093822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986870730409647346251465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26596643895518119180007813 4986870730409647346251465)
  ·
    refine ⟨3740153047807235509688599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4986870730409647346251465 3740153047807235509688599)
    ·
      refine ⟨5610229571710853264532899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740153047807235509688599 5610229571710853264532899)
      ·
        refine ⟨8415344357566279896799349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610229571710853264532899 8415344357566279896799349)
        ·
          refine ⟨788938533521838740324939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8415344357566279896799349 788938533521838740324939)
          ·
            refine ⟨1183407800282758110487409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788938533521838740324939 1183407800282758110487409)
            ·
              refine ⟨887555850212068582865557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183407800282758110487409 887555850212068582865557)
              ·
                refine ⟨41604180478690714821823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 887555850212068582865557 41604180478690714821823)
                ·
                  rfl

theorem cell22_1093822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_1093822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093822 prefixEnd_1093822 := by exact prefixLift 1093822
  have htrace : WordTrace (prefixWord ++ tailWord_1093822) baseStart_1093822 baseEnd_1093822 := by
    simpa [prefixWord, tailWord_1093822, baseEnd_1093822] using wordTrace_append hprefix tailTrace_1093822
  have hstable : (prefixWord ++ tailWord_1093822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093822).length < 2 ^ (prefixWord ++ tailWord_1093822).sum := by decide
  have hdescent : baseEnd_1093822 < baseStart_1093822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093878 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1093878 : Nat := 118140960795 + 1093878 * 2 ^ 59
def prefixEnd_1093878 : Nat := 4983230072969 + 3 ^ 40 * 1093878 * 2
def baseEnd_1093878 : Nat := 124818931417550317998745

theorem tailTrace_1093878 : CollatzResearch.WordTrace tailWord_1093878 prefixEnd_1093878 124818931417550317998745 := by
  unfold tailWord_1093878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493563020692143770878143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26598005554049533556033525 2493563020692143770878143)
  ·
    refine ⟨3740344531038215656317215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2493563020692143770878143 3740344531038215656317215)
    ·
      refine ⟨5610516796557323484475823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740344531038215656317215 5610516796557323484475823)
      ·
        refine ⟨8415775194835985226713735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610516796557323484475823 8415775194835985226713735)
        ·
          refine ⟨12623662792253977840070603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8415775194835985226713735 12623662792253977840070603)
          ·
            refine ⟨18935494188380966760105905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12623662792253977840070603 18935494188380966760105905)
            ·
              refine ⟨14201620641285725070079429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18935494188380966760105905 14201620641285725070079429)
              ·
                refine ⟨2662803870241073450639893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14201620641285725070079429 2662803870241073450639893)
                ·
                  refine ⟨124818931417550317998745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2662803870241073450639893 124818931417550317998745)
                  ·
                    rfl

theorem cell22_1093878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1093878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093878 prefixEnd_1093878 := by exact prefixLift 1093878
  have htrace : WordTrace (prefixWord ++ tailWord_1093878) baseStart_1093878 baseEnd_1093878 := by
    simpa [prefixWord, tailWord_1093878, baseEnd_1093878] using wordTrace_append hprefix tailTrace_1093878
  have hstable : (prefixWord ++ tailWord_1093878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093878).length < 2 ^ (prefixWord ++ tailWord_1093878).sum := by decide
  have hdescent : baseEnd_1093878 < baseStart_1093878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093893 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_1093893 : Nat := 118140960795 + 1093893 * 2 ^ 59
def prefixEnd_1093893 : Nat := 4983230072969 + 3 ^ 40 * 1093893 * 2
def baseEnd_1093893 : Nat := 374461929059195914871189

theorem tailTrace_1093893 : CollatzResearch.WordTrace tailWord_1093893 prefixEnd_1093893 374461929059195914871189 := by
  unfold tailWord_1093893
  simp only [CollatzResearch.WordTrace]
  refine ⟨39897555426019957895846333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26598370284013305263897555 39897555426019957895846333)
  ·
    refine ⟨14961583284757484210942375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39897555426019957895846333 14961583284757484210942375)
    ·
      refine ⟨22442374927136226316413563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14961583284757484210942375 22442374927136226316413563)
      ·
        refine ⟨33663562390704339474620345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22442374927136226316413563 33663562390704339474620345)
        ·
          refine ⟨25247671793028254605965259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33663562390704339474620345 25247671793028254605965259)
          ·
            refine ⟨37871507689542381908947889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25247671793028254605965259 37871507689542381908947889)
            ·
              refine ⟨28403630767156786431710917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37871507689542381908947889 28403630767156786431710917)
              ·
                refine ⟨5325680768841897455945797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28403630767156786431710917 5325680768841897455945797)
                ·
                  refine ⟨998565144157855772989837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5325680768841897455945797 998565144157855772989837)
                  ·
                    refine ⟨374461929059195914871189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 998565144157855772989837 374461929059195914871189)
                    ·
                      rfl

theorem cell22_1093893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_1093893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093893 prefixEnd_1093893 := by exact prefixLift 1093893
  have htrace : WordTrace (prefixWord ++ tailWord_1093893) baseStart_1093893 baseEnd_1093893 := by
    simpa [prefixWord, tailWord_1093893, baseEnd_1093893] using wordTrace_append hprefix tailTrace_1093893
  have hstable : (prefixWord ++ tailWord_1093893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093893).length < 2 ^ (prefixWord ++ tailWord_1093893).sum := by decide
  have hdescent : baseEnd_1093893 < baseStart_1093893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093968 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 7]
def baseStart_1093968 : Nat := 118140960795 + 1093968 * 2 ^ 59
def prefixEnd_1093968 : Nat := 4983230072969 + 3 ^ 40 * 1093968 * 2
def baseEnd_1093968 : Nat := 124829201030640239748653

theorem tailTrace_1093968 : CollatzResearch.WordTrace tailWord_1093968 prefixEnd_1093968 124829201030640239748653 := by
  unfold tailWord_1093968
  simp only [CollatzResearch.WordTrace]
  refine ⟨19950145450374122852413279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26600193933832163803217705 19950145450374122852413279)
  ·
    refine ⟨29925218175561184278619919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19950145450374122852413279 29925218175561184278619919)
    ·
      refine ⟨44887827263341776417929879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29925218175561184278619919 44887827263341776417929879)
      ·
        refine ⟨67331740895012664626894819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44887827263341776417929879 67331740895012664626894819)
        ·
          refine ⟨100997611342518996940342229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67331740895012664626894819 100997611342518996940342229)
          ·
            refine ⟨2367131515840288990789271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 100997611342518996940342229 2367131515840288990789271)
            ·
              refine ⟨3550697273760433486183907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367131515840288990789271 3550697273760433486183907)
              ·
                refine ⟨5326045910640650229275861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550697273760433486183907 5326045910640650229275861)
                ·
                  refine ⟨124829201030640239748653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5326045910640650229275861 124829201030640239748653)
                  ·
                    rfl

theorem cell22_1093968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_1093968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093968 prefixEnd_1093968 := by exact prefixLift 1093968
  have htrace : WordTrace (prefixWord ++ tailWord_1093968) baseStart_1093968 baseEnd_1093968 := by
    simpa [prefixWord, tailWord_1093968, baseEnd_1093968] using wordTrace_append hprefix tailTrace_1093968
  have hstable : (prefixWord ++ tailWord_1093968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093968).length < 2 ^ (prefixWord ++ tailWord_1093968).sum := by decide
  have hdescent : baseEnd_1093968 < baseStart_1093968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093972 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1093972 : Nat := 118140960795 + 1093972 * 2 ^ 59
def prefixEnd_1093972 : Nat := 4983230072969 + 3 ^ 40 * 1093972 * 2
def baseEnd_1093972 : Nat := 374488972373666042145947

theorem tailTrace_1093972 : CollatzResearch.WordTrace tailWord_1093972 prefixEnd_1093972 374488972373666042145947 := by
  unfold tailWord_1093972
  simp only [CollatzResearch.WordTrace]
  refine ⟨19950218396366877193986085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26600291195155836258648113 19950218396366877193986085)
  ·
    refine ⟨3740665949318789473872391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19950218396366877193986085 3740665949318789473872391)
    ·
      refine ⟨5610998923978184210808587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740665949318789473872391 5610998923978184210808587)
      ·
        refine ⟨8416498385967276316212881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610998923978184210808587 8416498385967276316212881)
        ·
          refine ⟨6312373789475457237159661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8416498385967276316212881 6312373789475457237159661)
          ·
            refine ⟨2367140171053296463934873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6312373789475457237159661 2367140171053296463934873)
            ·
              refine ⟨1775355128289972347951155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2367140171053296463934873 1775355128289972347951155)
              ·
                refine ⟨2663032692434958521926733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775355128289972347951155 2663032692434958521926733)
                ·
                  refine ⟨998637259663109445722525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2663032692434958521926733 998637259663109445722525)
                  ·
                    refine ⟨374488972373666042145947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 998637259663109445722525 374488972373666042145947)
                    ·
                      rfl

theorem cell22_1093972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1093972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093972 prefixEnd_1093972 := by exact prefixLift 1093972
  have htrace : WordTrace (prefixWord ++ tailWord_1093972) baseStart_1093972 baseEnd_1093972 := by
    simpa [prefixWord, tailWord_1093972, baseEnd_1093972] using wordTrace_append hprefix tailTrace_1093972
  have hstable : (prefixWord ++ tailWord_1093972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093972).length < 2 ^ (prefixWord ++ tailWord_1093972).sum := by decide
  have hdescent : baseEnd_1093972 < baseStart_1093972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1093983 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 2, 5]
def baseStart_1093983 : Nat := 118140960795 + 1093983 * 2 ^ 59
def prefixEnd_1093983 : Nat := 4983230072969 + 3 ^ 40 * 1093983 * 2
def baseEnd_1093983 : Nat := 374492737898465680120913

theorem tailTrace_1093983 : CollatzResearch.WordTrace tailWord_1093983 prefixEnd_1093983 374492737898465680120913 := by
  unfold tailWord_1093983
  simp only [CollatzResearch.WordTrace]
  refine ⟨39900837995693903266622603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26600558663795935511081735 39900837995693903266622603)
  ·
    refine ⟨59851256993540854899933905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39900837995693903266622603 59851256993540854899933905)
    ·
      refine ⟨44888442745155641174950429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59851256993540854899933905 44888442745155641174950429)
      ·
        refine ⟨16833166029433365440606411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44888442745155641174950429 16833166029433365440606411)
        ·
          refine ⟨25249749044150048160909617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16833166029433365440606411 25249749044150048160909617)
          ·
            refine ⟨18937311783112536120682213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25249749044150048160909617 18937311783112536120682213)
            ·
              refine ⟨3550745959333600522627915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18937311783112536120682213 3550745959333600522627915)
              ·
                refine ⟨5326118939000400783941873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550745959333600522627915 5326118939000400783941873)
                ·
                  refine ⟨3994589204250300587956405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5326118939000400783941873 3994589204250300587956405)
                  ·
                    refine ⟨374492737898465680120913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3994589204250300587956405 374492737898465680120913)
                    ·
                      rfl

theorem cell22_1093983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_1093983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1093983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1093983 prefixEnd_1093983 := by exact prefixLift 1093983
  have htrace : WordTrace (prefixWord ++ tailWord_1093983) baseStart_1093983 baseEnd_1093983 := by
    simpa [prefixWord, tailWord_1093983, baseEnd_1093983] using wordTrace_append hprefix tailTrace_1093983
  have hstable : (prefixWord ++ tailWord_1093983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1093983).length < 2 ^ (prefixWord ++ tailWord_1093983).sum := by decide
  have hdescent : baseEnd_1093983 < baseStart_1093983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1093983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094036 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1094036 : Nat := 118140960795 + 1094036 * 2 ^ 59
def prefixEnd_1094036 : Nat := 4983230072969 + 3 ^ 40 * 1094036 * 2
def baseEnd_1094036 : Nat := 124836960293863736181917

theorem tailTrace_1094036 : CollatzResearch.WordTrace tailWord_1094036 prefixEnd_1094036 124836960293863736181917 := by
  unfold tailWord_1094036
  simp only [CollatzResearch.WordTrace]
  refine ⟨19951385532250946659150981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26601847376334595545534641 19951385532250946659150981)
  ·
    refine ⟨3740884787297052498590809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19951385532250946659150981 3740884787297052498590809)
    ·
      refine ⟨2805663590472789373943107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3740884787297052498590809 2805663590472789373943107)
      ·
        refine ⟨4208495385709184060914661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2805663590472789373943107 4208495385709184060914661)
        ·
          refine ⟨789092884820472011421499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4208495385709184060914661 789092884820472011421499)
          ·
            refine ⟨1183639327230708017132249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789092884820472011421499 1183639327230708017132249)
            ·
              refine ⟨887729495423031012849187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183639327230708017132249 887729495423031012849187)
              ·
                refine ⟨1331594243134546519273781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887729495423031012849187 1331594243134546519273781)
                ·
                  refine ⟨124836960293863736181917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1331594243134546519273781 124836960293863736181917)
                  ·
                    rfl

theorem cell22_1094036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1094036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094036 prefixEnd_1094036 := by exact prefixLift 1094036
  have htrace : WordTrace (prefixWord ++ tailWord_1094036) baseStart_1094036 baseEnd_1094036 := by
    simpa [prefixWord, tailWord_1094036, baseEnd_1094036] using wordTrace_append hprefix tailTrace_1094036
  have hstable : (prefixWord ++ tailWord_1094036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094036).length < 2 ^ (prefixWord ++ tailWord_1094036).sum := by decide
  have hdescent : baseEnd_1094036 < baseStart_1094036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094092 : List Nat := [2, 2, 1, 4, 3, 2, 1, 7]
def baseStart_1094092 : Nat := 118140960795 + 1094092 * 2 ^ 59
def prefixEnd_1094092 : Nat := 4983230072969 + 3 ^ 40 * 1094092 * 2
def baseEnd_1094092 : Nat := 41614450091780636571731

theorem tailTrace_1094092 : CollatzResearch.WordTrace tailWord_1094092 prefixEnd_1094092 41614450091780636571731 := by
  unfold tailWord_1094092
  simp only [CollatzResearch.WordTrace]
  refine ⟨19952406776149507441170265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26603209034866009921560353 19952406776149507441170265)
  ·
    refine ⟨14964305082112130580877699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19952406776149507441170265 14964305082112130580877699)
    ·
      refine ⟨22446457623168195871316549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14964305082112130580877699 22446457623168195871316549)
      ·
        refine ⟨4208710804344036725871853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22446457623168195871316549 4208710804344036725871853)
        ·
          refine ⟨1578266551629013772201945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4208710804344036725871853 1578266551629013772201945)
          ·
            refine ⟨1183699913721760329151459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578266551629013772201945 1183699913721760329151459)
            ·
              refine ⟨1775549870582640493727189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183699913721760329151459 1775549870582640493727189)
              ·
                refine ⟨41614450091780636571731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1775549870582640493727189 41614450091780636571731)
                ·
                  rfl

theorem cell22_1094092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 7].length) (baseStart_1094092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094092 prefixEnd_1094092 := by exact prefixLift 1094092
  have htrace : WordTrace (prefixWord ++ tailWord_1094092) baseStart_1094092 baseEnd_1094092 := by
    simpa [prefixWord, tailWord_1094092, baseEnd_1094092] using wordTrace_append hprefix tailTrace_1094092
  have hstable : (prefixWord ++ tailWord_1094092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094092).length < 2 ^ (prefixWord ++ tailWord_1094092).sum := by decide
  have hdescent : baseEnd_1094092 < baseStart_1094092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094103 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 11]
def baseStart_1094103 : Nat := 118140960795 + 1094103 * 2 ^ 59
def prefixEnd_1094103 : Nat := 4983230072969 + 3 ^ 40 * 1094103 * 2
def baseEnd_1094103 : Nat := 124844605450275122373515

theorem tailTrace_1094103 : CollatzResearch.WordTrace tailWord_1094103 prefixEnd_1094103 124844605450275122373515 := by
  unfold tailWord_1094103
  simp only [CollatzResearch.WordTrace]
  refine ⟨39905214755259163760990963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26603476503506109173993975 39905214755259163760990963)
  ·
    refine ⟨59857822132888745641486445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39905214755259163760990963 59857822132888745641486445)
    ·
      refine ⟨22446683299833279615557417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59857822132888745641486445 22446683299833279615557417)
      ·
        refine ⟨16835012474874959711668063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22446683299833279615557417 16835012474874959711668063)
        ·
          refine ⟨25252518712312439567502095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16835012474874959711668063 25252518712312439567502095)
          ·
            refine ⟨37878778068468659351253143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25252518712312439567502095 37878778068468659351253143)
            ·
              refine ⟨56818167102702989026879715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37878778068468659351253143 56818167102702989026879715)
              ·
                refine ⟨85227250654054483540319573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56818167102702989026879715 85227250654054483540319573)
                ·
                  refine ⟨124844605450275122373515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 85227250654054483540319573 124844605450275122373515)
                  ·
                    rfl

theorem cell22_1094103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 11].length) (baseStart_1094103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094103 prefixEnd_1094103 := by exact prefixLift 1094103
  have htrace : WordTrace (prefixWord ++ tailWord_1094103) baseStart_1094103 baseEnd_1094103 := by
    simpa [prefixWord, tailWord_1094103, baseEnd_1094103] using wordTrace_append hprefix tailTrace_1094103
  have hstable : (prefixWord ++ tailWord_1094103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094103).length < 2 ^ (prefixWord ++ tailWord_1094103).sum := by decide
  have hdescent : baseEnd_1094103 < baseStart_1094103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094124 : List Nat := [2, 2, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_1094124 : Nat := 118140960795 + 1094124 * 2 ^ 59
def prefixEnd_1094124 : Nat := 4983230072969 + 3 ^ 40 * 1094124 * 2
def baseEnd_1094124 : Nat := 374541005079988312345481

theorem tailTrace_1094124 : CollatzResearch.WordTrace tailWord_1094124 prefixEnd_1094124 374541005079988312345481 := by
  unfold tailWord_1094124
  simp only [CollatzResearch.WordTrace]
  refine ⟨19952990344091542173752713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26603987125455389565003617 19952990344091542173752713)
  ·
    refine ⟨14964742758068656630314535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19952990344091542173752713 14964742758068656630314535)
    ·
      refine ⟨22447114137102984945471803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14964742758068656630314535 22447114137102984945471803)
      ·
        refine ⟨33670671205654477418207705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22447114137102984945471803 33670671205654477418207705)
        ·
          refine ⟨25253003404240858063655779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33670671205654477418207705 25253003404240858063655779)
          ·
            refine ⟨37879505106361287095483669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25253003404240858063655779 37879505106361287095483669)
            ·
              refine ⟨1775601801860685332600797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37879505106361287095483669 1775601801860685332600797)
              ·
                refine ⟨665850675697756999725299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775601801860685332600797 665850675697756999725299)
                ·
                  refine ⟨998776013546635499587949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665850675697756999725299 998776013546635499587949)
                  ·
                    refine ⟨374541005079988312345481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 998776013546635499587949 374541005079988312345481)
                    ·
                      rfl

theorem cell22_1094124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_1094124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094124 prefixEnd_1094124 := by exact prefixLift 1094124
  have htrace : WordTrace (prefixWord ++ tailWord_1094124) baseStart_1094124 baseEnd_1094124 := by
    simpa [prefixWord, tailWord_1094124, baseEnd_1094124] using wordTrace_append hprefix tailTrace_1094124
  have hstable : (prefixWord ++ tailWord_1094124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094124).length < 2 ^ (prefixWord ++ tailWord_1094124).sum := by decide
  have hdescent : baseEnd_1094124 < baseStart_1094124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094165 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 6]
def baseStart_1094165 : Nat := 118140960795 + 1094165 * 2 ^ 59
def prefixEnd_1094165 : Nat := 4983230072969 + 3 ^ 40 * 1094165 * 2
def baseEnd_1094165 : Nat := 124851680072625957356785

theorem tailTrace_1094165 : CollatzResearch.WordTrace tailWord_1094165 prefixEnd_1094165 124851680072625957356785 := by
  unfold tailWord_1094165
  simp only [CollatzResearch.WordTrace]
  refine ⟨39907476081034548349747949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26604984054023032233165299 39907476081034548349747949)
  ·
    refine ⟨14965303530387955631155481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39907476081034548349747949 14965303530387955631155481)
    ·
      refine ⟨11223977647790966723366611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14965303530387955631155481 11223977647790966723366611)
      ·
        refine ⟨16835966471686450085049917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11223977647790966723366611 16835966471686450085049917)
        ·
          refine ⟨6313487426882418781893719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16835966471686450085049917 6313487426882418781893719)
          ·
            refine ⟨9470231140323628172840579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6313487426882418781893719 9470231140323628172840579)
            ·
              refine ⟨14205346710485442259260869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9470231140323628172840579 14205346710485442259260869)
              ·
                refine ⟨2663502508216020423611413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14205346710485442259260869 2663502508216020423611413)
                ·
                  refine ⟨124851680072625957356785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2663502508216020423611413 124851680072625957356785)
                  ·
                    rfl

theorem cell22_1094165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_1094165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094165 prefixEnd_1094165 := by exact prefixLift 1094165
  have htrace : WordTrace (prefixWord ++ tailWord_1094165) baseStart_1094165 baseEnd_1094165 := by
    simpa [prefixWord, tailWord_1094165, baseEnd_1094165] using wordTrace_append hprefix tailTrace_1094165
  have hstable : (prefixWord ++ tailWord_1094165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094165).length < 2 ^ (prefixWord ++ tailWord_1094165).sum := by decide
  have hdescent : baseEnd_1094165 < baseStart_1094165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094184 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1094184 : Nat := 118140960795 + 1094184 * 2 ^ 59
def prefixEnd_1094184 : Nat := 4983230072969 + 3 ^ 40 * 1094184 * 2
def baseEnd_1094184 : Nat := 374561544306168155845297

theorem tailTrace_1094184 : CollatzResearch.WordTrace tailWord_1094184 prefixEnd_1094184 374561544306168155845297 := by
  unfold tailWord_1094184
  simp only [CollatzResearch.WordTrace]
  refine ⟨19954084533982857297344803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26605446045310476396459737 19954084533982857297344803)
  ·
    refine ⟨29931126800974285946017205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19954084533982857297344803 29931126800974285946017205)
    ·
      refine ⟨2806043137591339307439113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29931126800974285946017205 2806043137591339307439113)
      ·
        refine ⟨2104532353193504480579335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2806043137591339307439113 2104532353193504480579335)
        ·
          refine ⟨3156798529790256720869003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104532353193504480579335 3156798529790256720869003)
          ·
            refine ⟨4735197794685385081303505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156798529790256720869003 4735197794685385081303505)
            ·
              refine ⟨3551398346014038810977629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4735197794685385081303505 3551398346014038810977629)
              ·
                refine ⟨1331774379755264554116611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3551398346014038810977629 1331774379755264554116611)
                ·
                  refine ⟨1997661569632896831174917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331774379755264554116611 1997661569632896831174917)
                  ·
                    refine ⟨374561544306168155845297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1997661569632896831174917 374561544306168155845297)
                    ·
                      rfl

theorem cell22_1094184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1094184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094184 prefixEnd_1094184 := by exact prefixLift 1094184
  have htrace : WordTrace (prefixWord ++ tailWord_1094184) baseStart_1094184 baseEnd_1094184 := by
    simpa [prefixWord, tailWord_1094184, baseEnd_1094184] using wordTrace_append hprefix tailTrace_1094184
  have hstable : (prefixWord ++ tailWord_1094184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094184).length < 2 ^ (prefixWord ++ tailWord_1094184).sum := by decide
  have hdescent : baseEnd_1094184 < baseStart_1094184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094197 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1094197 : Nat := 118140960795 + 1094197 * 2 ^ 59
def prefixEnd_1094197 : Nat := 4983230072969 + 3 ^ 40 * 1094197 * 2
def baseEnd_1094197 : Nat := 374565994471840455270257

theorem tailTrace_1094197 : CollatzResearch.WordTrace tailWord_1094197 prefixEnd_1094197 374565994471840455270257 := by
  unfold tailWord_1094197
  simp only [CollatzResearch.WordTrace]
  refine ⟨39908643216918617814912845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26605762144612411876608563 39908643216918617814912845)
  ·
    refine ⟨14965741206344481680592317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39908643216918617814912845 14965741206344481680592317)
    ·
      refine ⟨5612152952379180630222119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14965741206344481680592317 5612152952379180630222119)
      ·
        refine ⟨8418229428568770945333179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5612152952379180630222119 8418229428568770945333179)
        ·
          refine ⟨12627344142853156417999769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8418229428568770945333179 12627344142853156417999769)
          ·
            refine ⟨9470508107139867313499827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12627344142853156417999769 9470508107139867313499827)
            ·
              refine ⟨14205762160709800970249741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9470508107139867313499827 14205762160709800970249741)
              ·
                refine ⟨5327160810266175363843653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14205762160709800970249741 5327160810266175363843653)
                ·
                  refine ⟨998842651924907880720685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5327160810266175363843653 998842651924907880720685)
                  ·
                    refine ⟨374565994471840455270257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 998842651924907880720685 374565994471840455270257)
                    ·
                      rfl

theorem cell22_1094197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1094197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094197 prefixEnd_1094197 := by exact prefixLift 1094197
  have htrace : WordTrace (prefixWord ++ tailWord_1094197) baseStart_1094197 baseEnd_1094197 := by
    simpa [prefixWord, tailWord_1094197, baseEnd_1094197] using wordTrace_append hprefix tailTrace_1094197
  have hstable : (prefixWord ++ tailWord_1094197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094197).length < 2 ^ (prefixWord ++ tailWord_1094197).sum := by decide
  have hdescent : baseEnd_1094197 < baseStart_1094197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094199 : List Nat := [1, 1, 3, 1, 2, 3, 5, 2, 4]
def baseStart_1094199 : Nat := 118140960795 + 1094199 * 2 ^ 59
def prefixEnd_1094199 : Nat := 4983230072969 + 3 ^ 40 * 1094199 * 2
def baseEnd_1094199 : Nat := 124855559704237705573417

theorem tailTrace_1094199 : CollatzResearch.WordTrace tailWord_1094199 prefixEnd_1094199 124855559704237705573417 := by
  unfold tailWord_1094199
  simp only [CollatzResearch.WordTrace]
  refine ⟨39908716162911372156485651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26605810775274248104323767 39908716162911372156485651)
  ·
    refine ⟨59863074244367058234728477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39908716162911372156485651 59863074244367058234728477)
    ·
      refine ⟨22448652841637646838023179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59863074244367058234728477 22448652841637646838023179)
      ·
        refine ⟨33672979262456470257034769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22448652841637646838023179 33672979262456470257034769)
        ·
          refine ⟨25254734446842352692776077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33672979262456470257034769 25254734446842352692776077)
          ·
            refine ⟨9470525417565882259791029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25254734446842352692776077 9470525417565882259791029)
            ·
              refine ⟨887861757896801461855409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9470525417565882259791029 887861757896801461855409)
              ·
                refine ⟨665896318422601096391557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887861757896801461855409 665896318422601096391557)
                ·
                  refine ⟨124855559704237705573417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 665896318422601096391557 124855559704237705573417)
                  ·
                    rfl

theorem cell22_1094199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 4].length) (baseStart_1094199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094199 prefixEnd_1094199 := by exact prefixLift 1094199
  have htrace : WordTrace (prefixWord ++ tailWord_1094199) baseStart_1094199 baseEnd_1094199 := by
    simpa [prefixWord, tailWord_1094199, baseEnd_1094199] using wordTrace_append hprefix tailTrace_1094199
  have hstable : (prefixWord ++ tailWord_1094199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094199).length < 2 ^ (prefixWord ++ tailWord_1094199).sum := by decide
  have hdescent : baseEnd_1094199 < baseStart_1094199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094255 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 7]
def baseStart_1094255 : Nat := 118140960795 + 1094255 * 2 ^ 59
def prefixEnd_1094255 : Nat := 4983230072969 + 3 ^ 40 * 1094255 * 2
def baseEnd_1094255 : Nat := 124861949685715879106693

theorem tailTrace_1094255 : CollatzResearch.WordTrace tailWord_1094255 prefixEnd_1094255 124861949685715879106693 := by
  unfold tailWord_1094255
  simp only [CollatzResearch.WordTrace]
  refine ⟨39910758650708493720524219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26607172433805662480349479 39910758650708493720524219)
  ·
    refine ⟨59866137976062740580786329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39910758650708493720524219 59866137976062740580786329)
    ·
      refine ⟨44899603482047055435589747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59866137976062740580786329 44899603482047055435589747)
      ·
        refine ⟨67349405223070583153384621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44899603482047055435589747 67349405223070583153384621)
        ·
          refine ⟨25256026958651468682519233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67349405223070583153384621 25256026958651468682519233)
          ·
            refine ⟨18942020218988601511889425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25256026958651468682519233 18942020218988601511889425)
            ·
              refine ⟨14206515164241451133917069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18942020218988601511889425 14206515164241451133917069)
              ·
                refine ⟨5327443186590544175218901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14206515164241451133917069 5327443186590544175218901)
                ·
                  refine ⟨124861949685715879106693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5327443186590544175218901 124861949685715879106693)
                  ·
                    rfl

theorem cell22_1094255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 7].length) (baseStart_1094255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094255 prefixEnd_1094255 := by exact prefixLift 1094255
  have htrace : WordTrace (prefixWord ++ tailWord_1094255) baseStart_1094255 baseEnd_1094255 := by
    simpa [prefixWord, tailWord_1094255, baseEnd_1094255] using wordTrace_append hprefix tailTrace_1094255
  have hstable : (prefixWord ++ tailWord_1094255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094255).length < 2 ^ (prefixWord ++ tailWord_1094255).sum := by decide
  have hdescent : baseEnd_1094255 < baseStart_1094255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094261 : List Nat := [1, 3, 4, 2, 3, 1, 1, 7]
def baseStart_1094261 : Nat := 118140960795 + 1094261 * 2 ^ 59
def prefixEnd_1094261 : Nat := 4983230072969 + 3 ^ 40 * 1094261 * 2
def baseEnd_1094261 : Nat := 41620878108862846852229

theorem tailTrace_1094261 : CollatzResearch.WordTrace tailWord_1094261 prefixEnd_1094261 41620878108862846852229 := by
  unfold tailWord_1094261
  simp only [CollatzResearch.WordTrace]
  refine ⟨39910977488686756745242637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26607318325791171163495091 39910977488686756745242637)
  ·
    refine ⟨14966616558257533779465989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39910977488686756745242637 14966616558257533779465989)
    ·
      refine ⟨2806240604673287583649873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14966616558257533779465989 2806240604673287583649873)
      ·
        refine ⟨2104680453504965687737405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2806240604673287583649873 2104680453504965687737405)
        ·
          refine ⟨789255170064362132901527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2104680453504965687737405 789255170064362132901527)
          ·
            refine ⟨1183882755096543199352291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789255170064362132901527 1183882755096543199352291)
            ·
              refine ⟨1775824132644814799028437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183882755096543199352291 1775824132644814799028437)
              ·
                refine ⟨41620878108862846852229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1775824132644814799028437 41620878108862846852229)
                ·
                  rfl

theorem cell22_1094261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 7].length) (baseStart_1094261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094261 prefixEnd_1094261 := by exact prefixLift 1094261
  have htrace : WordTrace (prefixWord ++ tailWord_1094261) baseStart_1094261 baseEnd_1094261 := by
    simpa [prefixWord, tailWord_1094261, baseEnd_1094261] using wordTrace_append hprefix tailTrace_1094261
  have hstable : (prefixWord ++ tailWord_1094261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094261).length < 2 ^ (prefixWord ++ tailWord_1094261).sum := by decide
  have hdescent : baseEnd_1094261 < baseStart_1094261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094272 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 5]
def baseStart_1094272 : Nat := 118140960795 + 1094272 * 2 ^ 59
def prefixEnd_1094272 : Nat := 4983230072969 + 3 ^ 40 * 1094272 * 2
def baseEnd_1094272 : Nat := 124863889501521753215009

theorem tailTrace_1094272 : CollatzResearch.WordTrace tailWord_1094272 prefixEnd_1094272 124863889501521753215009 := by
  unfold tailWord_1094272
  simp only [CollatzResearch.WordTrace]
  refine ⟨19955689345823452811946535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26607585794431270415928713 19955689345823452811946535)
  ·
    refine ⟨29933534018735179217919803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19955689345823452811946535 29933534018735179217919803)
    ·
      refine ⟨44900301028102768826879705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29933534018735179217919803 44900301028102768826879705)
      ·
        refine ⟨33675225771077076620159779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44900301028102768826879705 33675225771077076620159779)
        ·
          refine ⟨50512838656615614930239669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33675225771077076620159779 50512838656615614930239669)
          ·
            refine ⟨4735578624057713899709969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50512838656615614930239669 4735578624057713899709969)
            ·
              refine ⟨3551683968043285424782477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4735578624057713899709969 3551683968043285424782477)
              ·
                refine ⟨1331881488016232034293429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3551683968043285424782477 1331881488016232034293429)
                ·
                  refine ⟨124863889501521753215009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1331881488016232034293429 124863889501521753215009)
                  ·
                    rfl

theorem cell22_1094272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_1094272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094272 prefixEnd_1094272 := by exact prefixLift 1094272
  have htrace : WordTrace (prefixWord ++ tailWord_1094272) baseStart_1094272 baseEnd_1094272 := by
    simpa [prefixWord, tailWord_1094272, baseEnd_1094272] using wordTrace_append hprefix tailTrace_1094272
  have hstable : (prefixWord ++ tailWord_1094272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094272).length < 2 ^ (prefixWord ++ tailWord_1094272).sum := by decide
  have hdescent : baseEnd_1094272 < baseStart_1094272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094383 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 2, 3]
def baseStart_1094383 : Nat := 118140960795 + 1094383 * 2 ^ 59
def prefixEnd_1094383 : Nat := 4983230072969 + 3 ^ 40 * 1094383 * 2
def baseEnd_1094383 : Nat := 374629666072997970119687

theorem tailTrace_1094383 : CollatzResearch.WordTrace tailWord_1094383 prefixEnd_1094383 374629666072997970119687 := by
  unfold tailWord_1094383
  simp only [CollatzResearch.WordTrace]
  refine ⟨39915427194244771581183803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26610284796163181054122535 39915427194244771581183803)
  ·
    refine ⟨59873140791367157371775705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39915427194244771581183803 59873140791367157371775705)
    ·
      refine ⟨44904855593525368028831779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59873140791367157371775705 44904855593525368028831779)
      ·
        refine ⟨67357283390288052043247669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44904855593525368028831779 67357283390288052043247669)
        ·
          refine ⟨6314745317839504879054469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67357283390288052043247669 6314745317839504879054469)
          ·
            refine ⟨1184014747094907164822713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6314745317839504879054469 1184014747094907164822713)
            ·
              refine ⟨888011060321180373617035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184014747094907164822713 888011060321180373617035)
              ·
                refine ⟨1332016590481770560425553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888011060321180373617035 1332016590481770560425553)
                ·
                  refine ⟨999012442861327920319165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332016590481770560425553 999012442861327920319165)
                  ·
                    refine ⟨374629666072997970119687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999012442861327920319165 374629666072997970119687)
                    ·
                      rfl

theorem cell22_1094383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_1094383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094383 prefixEnd_1094383 := by exact prefixLift 1094383
  have htrace : WordTrace (prefixWord ++ tailWord_1094383) baseStart_1094383 baseEnd_1094383 := by
    simpa [prefixWord, tailWord_1094383, baseEnd_1094383] using wordTrace_append hprefix tailTrace_1094383
  have hstable : (prefixWord ++ tailWord_1094383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094383).length < 2 ^ (prefixWord ++ tailWord_1094383).sum := by decide
  have hdescent : baseEnd_1094383 < baseStart_1094383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094394 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_1094394 : Nat := 118140960795 + 1094394 * 2 ^ 59
def prefixEnd_1094394 : Nat := 4983230072969 + 3 ^ 40 * 1094394 * 2
def baseEnd_1094394 : Nat := 374633431597797608094653

theorem tailTrace_1094394 : CollatzResearch.WordTrace tailWord_1094394 prefixEnd_1094394 374633431597797608094653 := by
  unfold tailWord_1094394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9978957099301230114958559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26610552264803280306556157 9978957099301230114958559)
  ·
    refine ⟨14968435648951845172437839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9978957099301230114958559 14968435648951845172437839)
    ·
      refine ⟨22452653473427767758656759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14968435648951845172437839 22452653473427767758656759)
      ·
        refine ⟨33678980210141651637985139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22452653473427767758656759 33678980210141651637985139)
        ·
          refine ⟨50518470315212477456977709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33678980210141651637985139 50518470315212477456977709)
          ·
            refine ⟨18944426368204679046366641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50518470315212477456977709 18944426368204679046366641)
            ·
              refine ⟨14208319776153509284774981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18944426368204679046366641 14208319776153509284774981)
              ·
                refine ⟨2664059958028782990895309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14208319776153509284774981 2664059958028782990895309)
                ·
                  refine ⟨999022484260793621585741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2664059958028782990895309 999022484260793621585741)
                  ·
                    refine ⟨374633431597797608094653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999022484260793621585741 374633431597797608094653)
                    ·
                      rfl

theorem cell22_1094394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_1094394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094394 prefixEnd_1094394 := by exact prefixLift 1094394
  have htrace : WordTrace (prefixWord ++ tailWord_1094394) baseStart_1094394 baseEnd_1094394 := by
    simpa [prefixWord, tailWord_1094394, baseEnd_1094394] using wordTrace_append hprefix tailTrace_1094394
  have hstable : (prefixWord ++ tailWord_1094394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094394).length < 2 ^ (prefixWord ++ tailWord_1094394).sum := by decide
  have hdescent : baseEnd_1094394 < baseStart_1094394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094411 : List Nat := [1, 1, 1, 1, 5, 1, 1, 7, 1, 3]
def baseStart_1094411 : Nat := 118140960795 + 1094411 * 2 ^ 59
def prefixEnd_1094411 : Nat := 4983230072969 + 3 ^ 40 * 1094411 * 2
def baseEnd_1094411 : Nat := 374639251045215230419601

theorem tailTrace_1094411 : CollatzResearch.WordTrace tailWord_1094411 prefixEnd_1094411 374639251045215230419601 := by
  unfold tailWord_1094411
  simp only [CollatzResearch.WordTrace]
  refine ⟨39916448438143332363203087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26610965625428888242135391 39916448438143332363203087)
  ·
    refine ⟨59874672657214998544804631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39916448438143332363203087 59874672657214998544804631)
    ·
      refine ⟨89812008985822497817206947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59874672657214998544804631 89812008985822497817206947)
      ·
        refine ⟨134718013478733746725810421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89812008985822497817206947 134718013478733746725810421)
        ·
          refine ⟨12629813763631288755544727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134718013478733746725810421 12629813763631288755544727)
          ·
            refine ⟨18944720645446933133317091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12629813763631288755544727 18944720645446933133317091)
            ·
              refine ⟨28417080968170399699975637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18944720645446933133317091 28417080968170399699975637)
              ·
                refine ⟨666025335191493742968179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28417080968170399699975637 666025335191493742968179)
                ·
                  refine ⟨999038002787240614452269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666025335191493742968179 999038002787240614452269)
                  ·
                    refine ⟨374639251045215230419601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999038002787240614452269 374639251045215230419601)
                    ·
                      rfl

theorem cell22_1094411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 3].length) (baseStart_1094411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094411 prefixEnd_1094411 := by exact prefixLift 1094411
  have htrace : WordTrace (prefixWord ++ tailWord_1094411) baseStart_1094411 baseEnd_1094411 := by
    simpa [prefixWord, tailWord_1094411, baseEnd_1094411] using wordTrace_append hprefix tailTrace_1094411
  have hstable : (prefixWord ++ tailWord_1094411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094411).length < 2 ^ (prefixWord ++ tailWord_1094411).sum := by decide
  have hdescent : baseEnd_1094411 < baseStart_1094411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094428 : List Nat := [2, 2, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_1094428 : Nat := 118140960795 + 1094428 * 2 ^ 59
def prefixEnd_1094428 : Nat := 4983230072969 + 3 ^ 40 * 1094428 * 2
def baseEnd_1094428 : Nat := 374645070492632852744549

theorem tailTrace_1094428 : CollatzResearch.WordTrace tailWord_1094428 prefixEnd_1094428 374645070492632852744549 := by
  unfold tailWord_1094428
  simp only [CollatzResearch.WordTrace]
  refine ⟨19958534239540872133285969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26611378986054496177714625 19958534239540872133285969)
  ·
    refine ⟨14968900679655654099964477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19958534239540872133285969 14968900679655654099964477)
    ·
      refine ⟨5613337754870870287486679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14968900679655654099964477 5613337754870870287486679)
      ·
        refine ⟨8420006632306305431230019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613337754870870287486679 8420006632306305431230019)
        ·
          refine ⟨12630009948459458146845029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420006632306305431230019 12630009948459458146845029)
          ·
            refine ⟨2368126865336148402533443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12630009948459458146845029 2368126865336148402533443)
            ·
              refine ⟨3552190298004222603800165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368126865336148402533443 3552190298004222603800165)
              ·
                refine ⟨666035680875791738212531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3552190298004222603800165 666035680875791738212531)
                ·
                  refine ⟨999053521313687607318797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666035680875791738212531 999053521313687607318797)
                  ·
                    refine ⟨374645070492632852744549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999053521313687607318797 374645070492632852744549)
                    ·
                      rfl

theorem cell22_1094428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_1094428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094428 prefixEnd_1094428 := by exact prefixLift 1094428
  have htrace : WordTrace (prefixWord ++ tailWord_1094428) baseStart_1094428 baseEnd_1094428 := by
    simpa [prefixWord, tailWord_1094428, baseEnd_1094428] using wordTrace_append hprefix tailTrace_1094428
  have hstable : (prefixWord ++ tailWord_1094428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094428).length < 2 ^ (prefixWord ++ tailWord_1094428).sum := by decide
  have hdescent : baseEnd_1094428 < baseStart_1094428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094445 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1094445 : Nat := 118140960795 + 1094445 * 2 ^ 59
def prefixEnd_1094445 : Nat := 4983230072969 + 3 ^ 40 * 1094445 * 2
def baseEnd_1094445 : Nat := 374650889940050475069497

theorem tailTrace_1094445 : CollatzResearch.WordTrace tailWord_1094445 prefixEnd_1094445 374650889940050475069497 := by
  unfold tailWord_1094445
  simp only [CollatzResearch.WordTrace]
  refine ⟨39917688520020156169940789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26611792346680104113293859 39917688520020156169940789)
  ·
    refine ⟨3742283298751889640931949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39917688520020156169940789 3742283298751889640931949)
    ·
      refine ⟨1403356237031958615349481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3742283298751889640931949 1403356237031958615349481)
      ·
        refine ⟨1052517177773968961512111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1403356237031958615349481 1052517177773968961512111)
        ·
          refine ⟨1578775766660953442268167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052517177773968961512111 1578775766660953442268167)
          ·
            refine ⟨2368163649991430163402251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578775766660953442268167 2368163649991430163402251)
            ·
              refine ⟨3552245474987145245103377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368163649991430163402251 3552245474987145245103377)
              ·
                refine ⟨2664184106240358933827533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3552245474987145245103377 2664184106240358933827533)
                ·
                  refine ⟨999069039840134600185325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2664184106240358933827533 999069039840134600185325)
                  ·
                    refine ⟨374650889940050475069497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999069039840134600185325 374650889940050475069497)
                    ·
                      rfl

theorem cell22_1094445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1094445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094445 prefixEnd_1094445 := by exact prefixLift 1094445
  have htrace : WordTrace (prefixWord ++ tailWord_1094445) baseStart_1094445 baseEnd_1094445 := by
    simpa [prefixWord, tailWord_1094445, baseEnd_1094445] using wordTrace_append hprefix tailTrace_1094445
  have hstable : (prefixWord ++ tailWord_1094445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094445).length < 2 ^ (prefixWord ++ tailWord_1094445).sum := by decide
  have hdescent : baseEnd_1094445 < baseStart_1094445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094499 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 1, 6]
def baseStart_1094499 : Nat := 118140960795 + 1094499 * 2 ^ 59
def prefixEnd_1094499 : Nat := 4983230072969 + 3 ^ 40 * 1094499 * 2
def baseEnd_1094499 : Nat := 374669375243612334219331

theorem tailTrace_1094499 : CollatzResearch.WordTrace tailWord_1094499 prefixEnd_1094499 374669375243612334219331 := by
  unfold tailWord_1094499
  simp only [CollatzResearch.WordTrace]
  refine ⟨39919658061824523392406551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26613105374549682261604367 39919658061824523392406551)
  ·
    refine ⟨59879487092736785088609827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39919658061824523392406551 59879487092736785088609827)
    ·
      refine ⟨89819230639105177632914741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59879487092736785088609827 89819230639105177632914741)
      ·
        refine ⟨8420552872416110403085757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89819230639105177632914741 8420552872416110403085757)
        ·
          refine ⟨3157707327156041401157159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8420552872416110403085757 3157707327156041401157159)
          ·
            refine ⟨4736560990734062101735739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157707327156041401157159 4736560990734062101735739)
            ·
              refine ⟨7104841486101093152603609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736560990734062101735739 7104841486101093152603609)
              ·
                refine ⟨5328631114575819864452707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7104841486101093152603609 5328631114575819864452707)
                ·
                  refine ⟨7992946671863729796679061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5328631114575819864452707 7992946671863729796679061)
                  ·
                    refine ⟨374669375243612334219331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7992946671863729796679061 374669375243612334219331)
                    ·
                      rfl

theorem cell22_1094499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_1094499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094499 prefixEnd_1094499 := by exact prefixLift 1094499
  have htrace : WordTrace (prefixWord ++ tailWord_1094499) baseStart_1094499 baseEnd_1094499 := by
    simpa [prefixWord, tailWord_1094499, baseEnd_1094499] using wordTrace_append hprefix tailTrace_1094499
  have hstable : (prefixWord ++ tailWord_1094499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094499).length < 2 ^ (prefixWord ++ tailWord_1094499).sum := by decide
  have hdescent : baseEnd_1094499 < baseStart_1094499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094501 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_1094501 : Nat := 118140960795 + 1094501 * 2 ^ 59
def prefixEnd_1094501 : Nat := 4983230072969 + 3 ^ 40 * 1094501 * 2
def baseEnd_1094501 : Nat := 374670059884484995669325

theorem tailTrace_1094501 : CollatzResearch.WordTrace tailWord_1094501 prefixEnd_1094501 374670059884484995669325 := by
  unfold tailWord_1094501
  simp only [CollatzResearch.WordTrace]
  refine ⟨39919731007817277733979357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26613154005211518489319571 39919731007817277733979357)
  ·
    refine ⟨14969899127931479150242259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39919731007817277733979357 14969899127931479150242259)
    ·
      refine ⟨22454848691897218725363389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14969899127931479150242259 22454848691897218725363389)
      ·
        refine ⟨8420568259461457022011271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22454848691897218725363389 8420568259461457022011271)
        ·
          refine ⟨12630852389192185533016907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420568259461457022011271 12630852389192185533016907)
          ·
            refine ⟨18946278583788278299525361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12630852389192185533016907 18946278583788278299525361)
            ·
              refine ⟨14209708937841208724644021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18946278583788278299525361 14209708937841208724644021)
              ·
                refine ⟨1332160212922613317935377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14209708937841208724644021 1332160212922613317935377)
                ·
                  refine ⟨999120159691959988451533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332160212922613317935377 999120159691959988451533)
                  ·
                    refine ⟨374670059884484995669325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999120159691959988451533 374670059884484995669325)
                    ·
                      rfl

theorem cell22_1094501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_1094501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094501 prefixEnd_1094501 := by exact prefixLift 1094501
  have htrace : WordTrace (prefixWord ++ tailWord_1094501) baseStart_1094501 baseEnd_1094501 := by
    simpa [prefixWord, tailWord_1094501, baseEnd_1094501] using wordTrace_append hprefix tailTrace_1094501
  have hstable : (prefixWord ++ tailWord_1094501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094501).length < 2 ^ (prefixWord ++ tailWord_1094501).sum := by decide
  have hdescent : baseEnd_1094501 < baseStart_1094501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094518 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1094518 : Nat := 118140960795 + 1094518 * 2 ^ 59
def prefixEnd_1094518 : Nat := 4983230072969 + 3 ^ 40 * 1094518 * 2
def baseEnd_1094518 : Nat := 374675879331902617994273

theorem tailTrace_1094518 : CollatzResearch.WordTrace tailWord_1094518 prefixEnd_1094518 374675879331902617994273 := by
  unfold tailWord_1094518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495021940547230602334263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26613567365837126424898805 2495021940547230602334263)
  ·
    refine ⟨3742532910820845903501395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495021940547230602334263 3742532910820845903501395)
    ·
      refine ⟨5613799366231268855252093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742532910820845903501395 5613799366231268855252093)
      ·
        refine ⟨2105174762336725820719535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5613799366231268855252093 2105174762336725820719535)
        ·
          refine ⟨3157762143505088731079303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105174762336725820719535 3157762143505088731079303)
          ·
            refine ⟨4736643215257633096618955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157762143505088731079303 4736643215257633096618955)
            ·
              refine ⟨7104964822886449644928433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736643215257633096618955 7104964822886449644928433)
              ·
                refine ⟨5328723617164837233696325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7104964822886449644928433 5328723617164837233696325)
                ·
                  refine ⟨999135678218406981318061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5328723617164837233696325 999135678218406981318061)
                  ·
                    refine ⟨374675879331902617994273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999135678218406981318061 374675879331902617994273)
                    ·
                      rfl

theorem cell22_1094518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1094518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094518 prefixEnd_1094518 := by exact prefixLift 1094518
  have htrace : WordTrace (prefixWord ++ tailWord_1094518) baseStart_1094518 baseEnd_1094518 := by
    simpa [prefixWord, tailWord_1094518, baseEnd_1094518] using wordTrace_append hprefix tailTrace_1094518
  have hstable : (prefixWord ++ tailWord_1094518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094518).length < 2 ^ (prefixWord ++ tailWord_1094518).sum := by decide
  have hdescent : baseEnd_1094518 < baseStart_1094518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094606 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1094606 : Nat := 118140960795 + 1094606 * 2 ^ 59
def prefixEnd_1094606 : Nat := 4983230072969 + 3 ^ 40 * 1094606 * 2
def baseEnd_1094606 : Nat := 374706003530299721794003

theorem tailTrace_1094606 : CollatzResearch.WordTrace tailWord_1094606 prefixEnd_1094606 374706003530299721794003 := by
  unfold tailWord_1094606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990445084054610083318959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26615707114957920444367781 4990445084054610083318959)
  ·
    refine ⟨7485667626081915124978439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4990445084054610083318959 7485667626081915124978439)
    ·
      refine ⟨11228501439122872687467659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7485667626081915124978439 11228501439122872687467659)
      ·
        refine ⟨16842752158684309031201489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228501439122872687467659 16842752158684309031201489)
        ·
          refine ⟨12632064119013231773401117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16842752158684309031201489 12632064119013231773401117)
          ·
            refine ⟨4737024044629961915025419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12632064119013231773401117 4737024044629961915025419)
            ·
              refine ⟨7105536066944942872538129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737024044629961915025419 7105536066944942872538129)
              ·
                refine ⟨5329152050208707154403597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7105536066944942872538129 5329152050208707154403597)
                ·
                  refine ⟨1998432018828265182901349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5329152050208707154403597 1998432018828265182901349)
                  ·
                    refine ⟨374706003530299721794003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998432018828265182901349 374706003530299721794003)
                    ·
                      rfl

theorem cell22_1094606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1094606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094606 prefixEnd_1094606 := by exact prefixLift 1094606
  have htrace : WordTrace (prefixWord ++ tailWord_1094606) baseStart_1094606 baseEnd_1094606 := by
    simpa [prefixWord, tailWord_1094606, baseEnd_1094606] using wordTrace_append hprefix tailTrace_1094606
  have hstable : (prefixWord ++ tailWord_1094606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094606).length < 2 ^ (prefixWord ++ tailWord_1094606).sum := by decide
  have hdescent : baseEnd_1094606 < baseStart_1094606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094621 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 8]
def baseStart_1094621 : Nat := 118140960795 + 1094621 * 2 ^ 59
def prefixEnd_1094621 : Nat := 4983230072969 + 3 ^ 40 * 1094621 * 2
def baseEnd_1094621 : Nat := 124903712778948227556319

theorem tailTrace_1094621 : CollatzResearch.WordTrace tailWord_1094621 prefixEnd_1094621 124903712778948227556319 := by
  unfold tailWord_1094621
  simp only [CollatzResearch.WordTrace]
  refine ⟨39924107767382538228347717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26616071844921692152231811 39924107767382538228347717)
  ·
    refine ⟨7485770206384225917815197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39924107767382538228347717 7485770206384225917815197)
    ·
      refine ⟨2807163827394084719180699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7485770206384225917815197 2807163827394084719180699)
      ·
        refine ⟨4210745741091127078771049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807163827394084719180699 4210745741091127078771049)
        ·
          refine ⟨3158059305818345309078287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4210745741091127078771049 3158059305818345309078287)
          ·
            refine ⟨4737088958727517963617431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158059305818345309078287 4737088958727517963617431)
            ·
              refine ⟨7105633438091276945426147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737088958727517963617431 7105633438091276945426147)
              ·
                refine ⟨10658450157136915418139221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7105633438091276945426147 10658450157136915418139221)
                ·
                  refine ⟨124903712778948227556319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10658450157136915418139221 124903712778948227556319)
                  ·
                    rfl

theorem cell22_1094621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_1094621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094621 prefixEnd_1094621 := by exact prefixLift 1094621
  have htrace : WordTrace (prefixWord ++ tailWord_1094621) baseStart_1094621 baseEnd_1094621 := by
    simpa [prefixWord, tailWord_1094621, baseEnd_1094621] using wordTrace_append hprefix tailTrace_1094621
  have hstable : (prefixWord ++ tailWord_1094621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094621).length < 2 ^ (prefixWord ++ tailWord_1094621).sum := by decide
  have hdescent : baseEnd_1094621 < baseStart_1094621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094649 : List Nat := [1, 2, 1, 3, 1, 3, 11]
def baseStart_1094649 : Nat := 118140960795 + 1094649 * 2 ^ 59
def prefixEnd_1094649 : Nat := 4983230072969 + 3 ^ 40 * 1094649 * 2
def baseEnd_1094649 : Nat := 13878545307743034924773

theorem tailTrace_1094649 : CollatzResearch.WordTrace tailWord_1094649 prefixEnd_1094649 13878545307743034924773 := by
  unfold tailWord_1094649
  simp only [CollatzResearch.WordTrace]
  refine ⟨39925129011281099010367001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26616752674187399340244667 39925129011281099010367001)
  ·
    refine ⟨29943846758460824257775251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39925129011281099010367001 29943846758460824257775251)
    ·
      refine ⟨44915770137691236386662877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29943846758460824257775251 44915770137691236386662877)
      ·
        refine ⟨16843413801634213644998579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44915770137691236386662877 16843413801634213644998579)
        ·
          refine ⟨25265120702451320467497869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16843413801634213644998579 25265120702451320467497869)
          ·
            refine ⟨9474420263419245175311701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25265120702451320467497869 9474420263419245175311701)
            ·
              refine ⟨13878545307743034924773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9474420263419245175311701 13878545307743034924773)
              ·
                rfl

theorem cell22_1094649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 11].length) (baseStart_1094649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094649 prefixEnd_1094649 := by exact prefixLift 1094649
  have htrace : WordTrace (prefixWord ++ tailWord_1094649) baseStart_1094649 baseEnd_1094649 := by
    simpa [prefixWord, tailWord_1094649, baseEnd_1094649] using wordTrace_append hprefix tailTrace_1094649
  have hstable : (prefixWord ++ tailWord_1094649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094649).length < 2 ^ (prefixWord ++ tailWord_1094649).sum := by decide
  have hdescent : baseEnd_1094649 < baseStart_1094649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094674 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1094674 : Nat := 118140960795 + 1094674 * 2 ^ 59
def prefixEnd_1094674 : Nat := 4983230072969 + 3 ^ 40 * 1094674 * 2
def baseEnd_1094674 : Nat := 374729281319970211093795

theorem tailTrace_1094674 : CollatzResearch.WordTrace tailWord_1094674 prefixEnd_1094674 374729281319970211093795 := by
  unfold tailWord_1094674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9981510209047632070006769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26617360557460352186684717 9981510209047632070006769)
  ·
    refine ⟨7486132656785724052505077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9981510209047632070006769 7486132656785724052505077)
    ·
      refine ⟨701824936573661629922351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7486132656785724052505077 701824936573661629922351)
      ·
        refine ⟨1052737404860492444883527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701824936573661629922351 1052737404860492444883527)
        ·
          refine ⟨1579106107290738667325291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052737404860492444883527 1579106107290738667325291)
          ·
            refine ⟨2368659160936108000987937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579106107290738667325291 2368659160936108000987937)
            ·
              refine ⟨1776494370702081000740953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2368659160936108000987937 1776494370702081000740953)
              ·
                refine ⟨1332370778026560750555715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1776494370702081000740953 1332370778026560750555715)
                ·
                  refine ⟨1998556167039841125833573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332370778026560750555715 1998556167039841125833573)
                  ·
                    refine ⟨374729281319970211093795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998556167039841125833573 374729281319970211093795)
                    ·
                      rfl

theorem cell22_1094674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1094674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094674 prefixEnd_1094674 := by exact prefixLift 1094674
  have htrace : WordTrace (prefixWord ++ tailWord_1094674) baseStart_1094674 baseEnd_1094674 := by
    simpa [prefixWord, tailWord_1094674, baseEnd_1094674] using wordTrace_append hprefix tailTrace_1094674
  have hstable : (prefixWord ++ tailWord_1094674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094674).length < 2 ^ (prefixWord ++ tailWord_1094674).sum := by decide
  have hdescent : baseEnd_1094674 < baseStart_1094674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094711 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 5]
def baseStart_1094711 : Nat := 118140960795 + 1094711 * 2 ^ 59
def prefixEnd_1094711 : Nat := 4983230072969 + 3 ^ 40 * 1094711 * 2
def baseEnd_1094711 : Nat := 124913982392038149306227

theorem tailTrace_1094711 : CollatzResearch.WordTrace tailWord_1094711 prefixEnd_1094711 124913982392038149306227 := by
  unfold tailWord_1094711
  simp only [CollatzResearch.WordTrace]
  refine ⟨39927390337056483599123987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26618260224704322399415991 39927390337056483599123987)
  ·
    refine ⟨59891085505584725398685981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39927390337056483599123987 59891085505584725398685981)
    ·
      refine ⟨22459157064594272024507243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59891085505584725398685981 22459157064594272024507243)
      ·
        refine ⟨33688735596891408036760865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22459157064594272024507243 33688735596891408036760865)
        ·
          refine ⟨25266551697668556027570649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33688735596891408036760865 25266551697668556027570649)
          ·
            refine ⟨18949913773251417020677987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25266551697668556027570649 18949913773251417020677987)
            ·
              refine ⟨28424870659877125531016981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18949913773251417020677987 28424870659877125531016981)
              ·
                refine ⟨1332415812181740259266421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28424870659877125531016981 1332415812181740259266421)
                ·
                  refine ⟨124913982392038149306227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1332415812181740259266421 124913982392038149306227)
                  ·
                    rfl

theorem cell22_1094711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 5].length) (baseStart_1094711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094711 prefixEnd_1094711 := by exact prefixLift 1094711
  have htrace : WordTrace (prefixWord ++ tailWord_1094711) baseStart_1094711 baseEnd_1094711 := by
    simpa [prefixWord, tailWord_1094711, baseEnd_1094711] using wordTrace_append hprefix tailTrace_1094711
  have hstable : (prefixWord ++ tailWord_1094711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094711).length < 2 ^ (prefixWord ++ tailWord_1094711).sum := by decide
  have hdescent : baseEnd_1094711 < baseStart_1094711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094788 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1094788 : Nat := 118140960795 + 1094788 * 2 ^ 59
def prefixEnd_1094788 : Nat := 4983230072969 + 3 ^ 40 * 1094788 * 2
def baseEnd_1094788 : Nat := 374768305849711913743445

theorem tailTrace_1094788 : CollatzResearch.WordTrace tailWord_1094788 prefixEnd_1094788 374768305849711913743445 := by
  unfold tailWord_1094788
  simp only [CollatzResearch.WordTrace]
  refine ⟨19965099378888762874838509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26620132505185017166451345 19965099378888762874838509)
  ·
    refine ⟨7486912267083286078064441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19965099378888762874838509 7486912267083286078064441)
    ·
      refine ⟨5615184200312464558548331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7486912267083286078064441 5615184200312464558548331)
      ·
        refine ⟨8422776300468696837822497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5615184200312464558548331 8422776300468696837822497)
        ·
          refine ⟨6317082225351522628366873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8422776300468696837822497 6317082225351522628366873)
          ·
            refine ⟨4737811669013641971275155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6317082225351522628366873 4737811669013641971275155)
            ·
              refine ⟨7106717503520462956912733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737811669013641971275155 7106717503520462956912733)
              ·
                refine ⟨2665019063820173608842275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7106717503520462956912733 2665019063820173608842275)
                ·
                  refine ⟨3997528595730260413263413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665019063820173608842275 3997528595730260413263413)
                  ·
                    refine ⟨374768305849711913743445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3997528595730260413263413 374768305849711913743445)
                    ·
                      rfl

theorem cell22_1094788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1094788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094788 prefixEnd_1094788 := by exact prefixLift 1094788
  have htrace : WordTrace (prefixWord ++ tailWord_1094788) baseStart_1094788 baseEnd_1094788 := by
    simpa [prefixWord, tailWord_1094788, baseEnd_1094788] using wordTrace_append hprefix tailTrace_1094788
  have hstable : (prefixWord ++ tailWord_1094788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094788).length < 2 ^ (prefixWord ++ tailWord_1094788).sum := by decide
  have hdescent : baseEnd_1094788 < baseStart_1094788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094803 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 2, 4]
def baseStart_1094803 : Nat := 118140960795 + 1094803 * 2 ^ 59
def prefixEnd_1094803 : Nat := 4983230072969 + 3 ^ 40 * 1094803 * 2
def baseEnd_1094803 : Nat := 374773440656256874618399

theorem tailTrace_1094803 : CollatzResearch.WordTrace tailWord_1094803 prefixEnd_1094803 374773440656256874618399 := by
  unfold tailWord_1094803
  simp only [CollatzResearch.WordTrace]
  refine ⟨39930745852723183311473063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26620497235148788874315375 39930745852723183311473063)
  ·
    refine ⟨59896118779084774967209595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39930745852723183311473063 59896118779084774967209595)
    ·
      refine ⟨89844178168627162450814393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59896118779084774967209595 89844178168627162450814393)
      ·
        refine ⟨67383133626470371838110795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89844178168627162450814393 67383133626470371838110795)
        ·
          refine ⟨101074700439705557757166193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67383133626470371838110795 101074700439705557757166193)
          ·
            refine ⟨75806025329779168317874645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101074700439705557757166193 75806025329779168317874645)
            ·
              refine ⟨1776703718666699257450187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75806025329779168317874645 1776703718666699257450187)
              ·
                refine ⟨2665055578000048886175281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776703718666699257450187 2665055578000048886175281)
                ·
                  refine ⟨1998791683500036664631461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665055578000048886175281 1998791683500036664631461)
                  ·
                    refine ⟨374773440656256874618399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998791683500036664631461 374773440656256874618399)
                    ·
                      rfl

theorem cell22_1094803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4].length) (baseStart_1094803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094803 prefixEnd_1094803 := by exact prefixLift 1094803
  have htrace : WordTrace (prefixWord ++ tailWord_1094803) baseStart_1094803 baseEnd_1094803 := by
    simpa [prefixWord, tailWord_1094803, baseEnd_1094803] using wordTrace_append hprefix tailTrace_1094803
  have hstable : (prefixWord ++ tailWord_1094803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094803).length < 2 ^ (prefixWord ++ tailWord_1094803).sum := by decide
  have hdescent : baseEnd_1094803 < baseStart_1094803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094831 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 8]
def baseStart_1094831 : Nat := 118140960795 + 1094831 * 2 ^ 59
def prefixEnd_1094831 : Nat := 4983230072969 + 3 ^ 40 * 1094831 * 2
def baseEnd_1094831 : Nat := 374783025628474134918313

theorem tailTrace_1094831 : CollatzResearch.WordTrace tailWord_1094831 prefixEnd_1094831 374783025628474134918313 := by
  unfold tailWord_1094831
  simp only [CollatzResearch.WordTrace]
  refine ⟨39931767096621744093492347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26621178064414496062328231 39931767096621744093492347)
  ·
    refine ⟨59897650644932616140238521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39931767096621744093492347 59897650644932616140238521)
    ·
      refine ⟨44923237983699462105178891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59897650644932616140238521 44923237983699462105178891)
      ·
        refine ⟨67384856975549193157768337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44923237983699462105178891 67384856975549193157768337)
        ·
          refine ⟨50538642731661894868326253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67384856975549193157768337 50538642731661894868326253)
          ·
            refine ⟨18951991024373210575622345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50538642731661894868326253 18951991024373210575622345)
            ·
              refine ⟨14213993268279907931716759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18951991024373210575622345 14213993268279907931716759)
              ·
                refine ⟨21320989902419861897575139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14213993268279907931716759 21320989902419861897575139)
                ·
                  refine ⟨31981484853629792846362709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21320989902419861897575139 31981484853629792846362709)
                  ·
                    refine ⟨374783025628474134918313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31981484853629792846362709 374783025628474134918313)
                    ·
                      rfl

theorem cell22_1094831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_1094831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094831 prefixEnd_1094831 := by exact prefixLift 1094831
  have htrace : WordTrace (prefixWord ++ tailWord_1094831) baseStart_1094831 baseEnd_1094831 := by
    simpa [prefixWord, tailWord_1094831, baseEnd_1094831] using wordTrace_append hprefix tailTrace_1094831
  have hstable : (prefixWord ++ tailWord_1094831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094831).length < 2 ^ (prefixWord ++ tailWord_1094831).sum := by decide
  have hdescent : baseEnd_1094831 < baseStart_1094831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094852 : List Nat := [2, 3, 3, 1, 3, 2, 2, 6]
def baseStart_1094852 : Nat := 118140960795 + 1094852 * 2 ^ 59
def prefixEnd_1094852 : Nat := 4983230072969 + 3 ^ 40 * 1094852 * 2
def baseEnd_1094852 : Nat := 41643357150848564460361

theorem tailTrace_1094852 : CollatzResearch.WordTrace tailWord_1094852 prefixEnd_1094852 41643357150848564460361 := by
  unfold tailWord_1094852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19966266514772832340003405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26621688686363776453337873 19966266514772832340003405)
  ·
    refine ⟨7487349943039812127501277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19966266514772832340003405 7487349943039812127501277)
    ·
      refine ⟨2807756228639929547812979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7487349943039812127501277 2807756228639929547812979)
      ·
        refine ⟨4211634342959894321719469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807756228639929547812979 4211634342959894321719469)
        ·
          refine ⟨1579362878609960370644801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4211634342959894321719469 1579362878609960370644801)
          ·
            refine ⟨1184522158957470277983601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579362878609960370644801 1184522158957470277983601)
            ·
              refine ⟨888391619218102708487701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184522158957470277983601 888391619218102708487701)
              ·
                refine ⟨41643357150848564460361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 888391619218102708487701 41643357150848564460361)
                ·
                  rfl

theorem cell22_1094852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 6].length) (baseStart_1094852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094852 prefixEnd_1094852 := by exact prefixLift 1094852
  have htrace : WordTrace (prefixWord ++ tailWord_1094852) baseStart_1094852 baseEnd_1094852 := by
    simpa [prefixWord, tailWord_1094852, baseEnd_1094852] using wordTrace_append hprefix tailTrace_1094852
  have hstable : (prefixWord ++ tailWord_1094852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094852).length < 2 ^ (prefixWord ++ tailWord_1094852).sum := by decide
  have hdescent : baseEnd_1094852 < baseStart_1094852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094923 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 3, 5]
def baseStart_1094923 : Nat := 118140960795 + 1094923 * 2 ^ 59
def prefixEnd_1094923 : Nat := 4983230072969 + 3 ^ 40 * 1094923 * 2
def baseEnd_1094923 : Nat := 374814519108616561618031

theorem tailTrace_1094923 : CollatzResearch.WordTrace tailWord_1094923 prefixEnd_1094923 374814519108616561618031 := by
  unfold tailWord_1094923
  simp only [CollatzResearch.WordTrace]
  refine ⟨39935122612288443805841423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26623415074858962537227615 39935122612288443805841423)
  ·
    refine ⟨59902683918432665708762135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39935122612288443805841423 59902683918432665708762135)
    ·
      refine ⟨89854025877648998563143203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59902683918432665708762135 89854025877648998563143203)
      ·
        refine ⟨134781038816473497844714805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89854025877648998563143203 134781038816473497844714805)
        ·
          refine ⟨12635722389044390422942013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134781038816473497844714805 12635722389044390422942013)
          ·
            refine ⟨4738395895891646408603255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12635722389044390422942013 4738395895891646408603255)
            ·
              refine ⟨7107593843837469612904883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738395895891646408603255 7107593843837469612904883)
              ·
                refine ⟨10661390765756204419357325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7107593843837469612904883 10661390765756204419357325)
                ·
                  refine ⟨3998021537158576657258997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10661390765756204419357325 3998021537158576657258997)
                  ·
                    refine ⟨374814519108616561618031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3998021537158576657258997 374814519108616561618031)
                    ·
                      rfl

theorem cell22_1094923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_1094923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094923 prefixEnd_1094923 := by exact prefixLift 1094923
  have htrace : WordTrace (prefixWord ++ tailWord_1094923) baseStart_1094923 baseEnd_1094923 := by
    simpa [prefixWord, tailWord_1094923, baseEnd_1094923] using wordTrace_append hprefix tailTrace_1094923
  have hstable : (prefixWord ++ tailWord_1094923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094923).length < 2 ^ (prefixWord ++ tailWord_1094923).sum := by decide
  have hdescent : baseEnd_1094923 < baseStart_1094923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094940 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1094940 : Nat := 118140960795 + 1094940 * 2 ^ 59
def prefixEnd_1094940 : Nat := 4983230072969 + 3 ^ 40 * 1094940 * 2
def baseEnd_1094940 : Nat := 374820338556034183942979

theorem tailTrace_1094940 : CollatzResearch.WordTrace tailWord_1094940 prefixEnd_1094940 374820338556034183942979 := by
  unfold tailWord_1094940
  simp only [CollatzResearch.WordTrace]
  refine ⟨19967871326613427854605137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26623828435484570472806849 19967871326613427854605137)
  ·
    refine ⟨14975903494960070890953853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19967871326613427854605137 14975903494960070890953853)
    ·
      refine ⟨5615963810610026584107695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14975903494960070890953853 5615963810610026584107695)
      ·
        refine ⟨8423945715915039876161543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5615963810610026584107695 8423945715915039876161543)
        ·
          refine ⟨12635918573872559814242315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8423945715915039876161543 12635918573872559814242315)
          ·
            refine ⟨18953877860808839721363473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12635918573872559814242315 18953877860808839721363473)
            ·
              refine ⟨14215408395606629791022605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18953877860808839721363473 14215408395606629791022605)
              ·
                refine ⟨5330778148352486171633477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14215408395606629791022605 5330778148352486171633477)
                ·
                  refine ⟨999520902816091157181277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5330778148352486171633477 999520902816091157181277)
                  ·
                    refine ⟨374820338556034183942979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999520902816091157181277 374820338556034183942979)
                    ·
                      rfl

theorem cell22_1094940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1094940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094940 prefixEnd_1094940 := by exact prefixLift 1094940
  have htrace : WordTrace (prefixWord ++ tailWord_1094940) baseStart_1094940 baseEnd_1094940 := by
    simpa [prefixWord, tailWord_1094940, baseEnd_1094940] using wordTrace_append hprefix tailTrace_1094940
  have hstable : (prefixWord ++ tailWord_1094940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094940).length < 2 ^ (prefixWord ++ tailWord_1094940).sum := by decide
  have hdescent : baseEnd_1094940 < baseStart_1094940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094957 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1094957 : Nat := 118140960795 + 1094957 * 2 ^ 59
def prefixEnd_1094957 : Nat := 4983230072969 + 3 ^ 40 * 1094957 * 2
def baseEnd_1094957 : Nat := 374826158003451806267927

theorem tailTrace_1094957 : CollatzResearch.WordTrace tailWord_1094957 prefixEnd_1094957 374826158003451806267927 := by
  unfold tailWord_1094957
  simp only [CollatzResearch.WordTrace]
  refine ⟨39936362694165267612579125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26624241796110178408386083 39936362694165267612579125)
  ·
    refine ⟨3744034002577993838679293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39936362694165267612579125 3744034002577993838679293)
    ·
      refine ⟨1404012750966747689504735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3744034002577993838679293 1404012750966747689504735)
      ·
        refine ⟨2106019126450121534257103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404012750966747689504735 2106019126450121534257103)
        ·
          refine ⟨3159028689675182301385655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106019126450121534257103 3159028689675182301385655)
          ·
            refine ⟨4738543034512773452078483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159028689675182301385655 4738543034512773452078483)
            ·
              refine ⟨7107814551769160178117725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738543034512773452078483 7107814551769160178117725)
              ·
                refine ⟨2665430456913435066794147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7107814551769160178117725 2665430456913435066794147)
                ·
                  refine ⟨3998145685370152600191221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665430456913435066794147 3998145685370152600191221)
                  ·
                    refine ⟨374826158003451806267927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3998145685370152600191221 374826158003451806267927)
                    ·
                      rfl

theorem cell22_1094957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1094957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094957 prefixEnd_1094957 := by exact prefixLift 1094957
  have htrace : WordTrace (prefixWord ++ tailWord_1094957) baseStart_1094957 baseEnd_1094957 := by
    simpa [prefixWord, tailWord_1094957, baseEnd_1094957] using wordTrace_append hprefix tailTrace_1094957
  have hstable : (prefixWord ++ tailWord_1094957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094957).length < 2 ^ (prefixWord ++ tailWord_1094957).sum := by decide
  have hdescent : baseEnd_1094957 < baseStart_1094957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094970 : List Nat := [3, 1, 1, 1, 4, 1, 5, 6]
def baseStart_1094970 : Nat := 118140960795 + 1094970 * 2 ^ 59
def prefixEnd_1094970 : Nat := 4983230072969 + 3 ^ 40 * 1094970 * 2
def baseEnd_1094970 : Nat := 41647845352124900632543

theorem tailTrace_1094970 : CollatzResearch.WordTrace tailWord_1094970 prefixEnd_1094970 41647845352124900632543 := by
  unfold tailWord_1094970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9984209210779542708200591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26624557895412113888534909 9984209210779542708200591)
  ·
    refine ⟨14976313816169314062300887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9984209210779542708200591 14976313816169314062300887)
    ·
      refine ⟨22464470724253971093451331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14976313816169314062300887 22464470724253971093451331)
      ·
        refine ⟨33696706086380956640176997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22464470724253971093451331 33696706086380956640176997)
        ·
          refine ⟨6318132391196429370033187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33696706086380956640176997 6318132391196429370033187)
          ·
            refine ⟨9477198586794644055049781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6318132391196429370033187 9477198586794644055049781)
            ·
              refine ⟨888487367511997880160917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9477198586794644055049781 888487367511997880160917)
              ·
                refine ⟨41647845352124900632543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 888487367511997880160917 41647845352124900632543)
                ·
                  rfl

theorem cell22_1094970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_1094970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094970 prefixEnd_1094970 := by exact prefixLift 1094970
  have htrace : WordTrace (prefixWord ++ tailWord_1094970) baseStart_1094970 baseEnd_1094970 := by
    simpa [prefixWord, tailWord_1094970, baseEnd_1094970] using wordTrace_append hprefix tailTrace_1094970
  have hstable : (prefixWord ++ tailWord_1094970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094970).length < 2 ^ (prefixWord ++ tailWord_1094970).sum := by decide
  have hdescent : baseEnd_1094970 < baseStart_1094970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1094972 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_1094972 : Nat := 118140960795 + 1094972 * 2 ^ 59
def prefixEnd_1094972 : Nat := 4983230072969 + 3 ^ 40 * 1094972 * 2
def baseEnd_1094972 : Nat := 374831292809996767142881

theorem tailTrace_1094972 : CollatzResearch.WordTrace tailWord_1094972 prefixEnd_1094972 374831292809996767142881 := by
  unfold tailWord_1094972
  simp only [CollatzResearch.WordTrace]
  refine ⟨19968454894555462587187585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26624606526073950116250113 19968454894555462587187585)
  ·
    refine ⟨14976341170916596940390689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19968454894555462587187585 14976341170916596940390689)
    ·
      refine ⟨11232255878187447705293017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14976341170916596940390689 11232255878187447705293017)
      ·
        refine ⟨8424191908640585778969763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11232255878187447705293017 8424191908640585778969763)
        ·
          refine ⟨12636287862960878668454645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8424191908640585778969763 12636287862960878668454645)
          ·
            refine ⟨1184651987152582375167623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12636287862960878668454645 1184651987152582375167623)
            ·
              refine ⟨1776977980728873562751435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184651987152582375167623 1776977980728873562751435)
              ·
                refine ⟨2665466971093310344127153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776977980728873562751435 2665466971093310344127153)
                ·
                  refine ⟨1999100228319982758095365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665466971093310344127153 1999100228319982758095365)
                  ·
                    refine ⟨374831292809996767142881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1999100228319982758095365 374831292809996767142881)
                    ·
                      rfl

theorem cell22_1094972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_1094972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1094972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1094972 prefixEnd_1094972 := by exact prefixLift 1094972
  have htrace : WordTrace (prefixWord ++ tailWord_1094972) baseStart_1094972 baseEnd_1094972 := by
    simpa [prefixWord, tailWord_1094972, baseEnd_1094972] using wordTrace_append hprefix tailTrace_1094972
  have hstable : (prefixWord ++ tailWord_1094972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1094972).length < 2 ^ (prefixWord ++ tailWord_1094972).sum := by decide
  have hdescent : baseEnd_1094972 < baseStart_1094972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1094972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095075 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 1, 5]
def baseStart_1095075 : Nat := 118140960795 + 1095075 * 2 ^ 59
def prefixEnd_1095075 : Nat := 4983230072969 + 3 ^ 40 * 1095075 * 2
def baseEnd_1095075 : Nat := 374866551814938831817565

theorem tailTrace_1095075 : CollatzResearch.WordTrace tailWord_1095075 prefixEnd_1095075 374866551814938831817565 := by
  unfold tailWord_1095075
  simp only [CollatzResearch.WordTrace]
  refine ⟨39940666507737773765374679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26627111005158515843583119 39940666507737773765374679)
  ·
    refine ⟨59910999761606660648062019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39940666507737773765374679 59910999761606660648062019)
    ·
      refine ⟨89866499642409990972093029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59910999761606660648062019 89866499642409990972093029)
      ·
        refine ⟨16849968682951873307267443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89866499642409990972093029 16849968682951873307267443)
        ·
          refine ⟨25274953024427809960901165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16849968682951873307267443 25274953024427809960901165)
          ·
            refine ⟨9478107384160428735337937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25274953024427809960901165 9478107384160428735337937)
            ·
              refine ⟨7108580538120321551503453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9478107384160428735337937 7108580538120321551503453)
              ·
                refine ⟨2665717701795120581813795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7108580538120321551503453 2665717701795120581813795)
                ·
                  refine ⟨3998576552692680872720693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665717701795120581813795 3998576552692680872720693)
                  ·
                    refine ⟨374866551814938831817565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3998576552692680872720693 374866551814938831817565)
                    ·
                      rfl

theorem cell22_1095075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_1095075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095075 prefixEnd_1095075 := by exact prefixLift 1095075
  have htrace : WordTrace (prefixWord ++ tailWord_1095075) baseStart_1095075 baseEnd_1095075 := by
    simpa [prefixWord, tailWord_1095075, baseEnd_1095075] using wordTrace_append hprefix tailTrace_1095075
  have hstable : (prefixWord ++ tailWord_1095075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095075).length < 2 ^ (prefixWord ++ tailWord_1095075).sum := by decide
  have hdescent : baseEnd_1095075 < baseStart_1095075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095126 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1095126 : Nat := 118140960795 + 1095126 * 2 ^ 59
def prefixEnd_1095126 : Nat := 4983230072969 + 3 ^ 40 * 1095126 * 2
def baseEnd_1095126 : Nat := 374884010157191698792409

theorem tailTrace_1095126 : CollatzResearch.WordTrace tailWord_1095126 prefixEnd_1095126 374884010157191698792409 := by
  unfold tailWord_1095126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496407914409563092217577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26628351087035339650320821 2496407914409563092217577)
  ·
    refine ⟨1872305935807172319163183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2496407914409563092217577 1872305935807172319163183)
    ·
      refine ⟨2808458903710758478744775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1872305935807172319163183 2808458903710758478744775)
      ·
        refine ⟨4212688355566137718117163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808458903710758478744775 4212688355566137718117163)
        ·
          refine ⟨6319032533349206577175745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212688355566137718117163 6319032533349206577175745)
          ·
            refine ⟨4739274400011904932881809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6319032533349206577175745 4739274400011904932881809)
            ·
              refine ⟨3554455800008928699661357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4739274400011904932881809 3554455800008928699661357)
              ·
                refine ⟨1332920925003348262373009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3554455800008928699661357 1332920925003348262373009)
                ·
                  refine ⟨999690693752511196779757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332920925003348262373009 999690693752511196779757)
                  ·
                    refine ⟨374884010157191698792409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999690693752511196779757 374884010157191698792409)
                    ·
                      rfl

theorem cell22_1095126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1095126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095126 prefixEnd_1095126 := by exact prefixLift 1095126
  have htrace : WordTrace (prefixWord ++ tailWord_1095126) baseStart_1095126 baseEnd_1095126 := by
    simpa [prefixWord, tailWord_1095126, baseEnd_1095126] using wordTrace_append hprefix tailTrace_1095126
  have hstable : (prefixWord ++ tailWord_1095126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095126).length < 2 ^ (prefixWord ++ tailWord_1095126).sum := by decide
  have hdescent : baseEnd_1095126 < baseStart_1095126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095135 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 2, 6]
def baseStart_1095135 : Nat := 118140960795 + 1095135 * 2 ^ 59
def prefixEnd_1095135 : Nat := 4983230072969 + 3 ^ 40 * 1095135 * 2
def baseEnd_1095135 : Nat := 374887091041118675317381

theorem tailTrace_1095135 : CollatzResearch.WordTrace tailWord_1095135 prefixEnd_1095135 374887091041118675317381 := by
  unfold tailWord_1095135
  simp only [CollatzResearch.WordTrace]
  refine ⟨39942854887520404012558859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26628569925013602675039239 39942854887520404012558859)
  ·
    refine ⟨59914282331280606018838289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39942854887520404012558859 59914282331280606018838289)
    ·
      refine ⟨44935711748460454514128717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59914282331280606018838289 44935711748460454514128717)
      ·
        refine ⟨16850891905672670442798269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44935711748460454514128717 16850891905672670442798269)
        ·
          refine ⟨6319084464627251416049351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16850891905672670442798269 6319084464627251416049351)
          ·
            refine ⟨9478626696940877124074027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319084464627251416049351 9478626696940877124074027)
            ·
              refine ⟨14217940045411315686111041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9478626696940877124074027 14217940045411315686111041)
              ·
                refine ⟨10663455034058486764583281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14217940045411315686111041 10663455034058486764583281)
                ·
                  refine ⟨7997591275543865073437461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10663455034058486764583281 7997591275543865073437461)
                  ·
                    refine ⟨374887091041118675317381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7997591275543865073437461 374887091041118675317381)
                    ·
                      rfl

theorem cell22_1095135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_1095135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095135 prefixEnd_1095135 := by exact prefixLift 1095135
  have htrace : WordTrace (prefixWord ++ tailWord_1095135) baseStart_1095135 baseEnd_1095135 := by
    simpa [prefixWord, tailWord_1095135, baseEnd_1095135] using wordTrace_append hprefix tailTrace_1095135
  have hstable : (prefixWord ++ tailWord_1095135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095135).length < 2 ^ (prefixWord ++ tailWord_1095135).sum := by decide
  have hdescent : baseEnd_1095135 < baseStart_1095135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095137 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 5, 3]
def baseStart_1095137 : Nat := 118140960795 + 1095137 * 2 ^ 59
def prefixEnd_1095137 : Nat := 4983230072969 + 3 ^ 40 * 1095137 * 2
def baseEnd_1095137 : Nat := 374887775681991336767375

theorem tailTrace_1095137 : CollatzResearch.WordTrace tailWord_1095137 prefixEnd_1095137 374887775681991336767375 := by
  unfold tailWord_1095137
  simp only [CollatzResearch.WordTrace]
  refine ⟨39942927833513158354131665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26628618555675438902754443 39942927833513158354131665)
  ·
    refine ⟨29957195875134868765598749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39942927833513158354131665 29957195875134868765598749)
    ·
      refine ⟨11233948453175575787099531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29957195875134868765598749 11233948453175575787099531)
      ·
        refine ⟨16850922679763363680649297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11233948453175575787099531 16850922679763363680649297)
        ·
          refine ⟨12638192009822522760486973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16850922679763363680649297 12638192009822522760486973)
          ·
            refine ⟨4739322003683446035182615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12638192009822522760486973 4739322003683446035182615)
            ·
              refine ⟨7108983005525169052773923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739322003683446035182615 7108983005525169052773923)
              ·
                refine ⟨10663474508287753579160885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108983005525169052773923 10663474508287753579160885)
                ·
                  refine ⟨999700735151976898046333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10663474508287753579160885 999700735151976898046333)
                  ·
                    refine ⟨374887775681991336767375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999700735151976898046333 374887775681991336767375)
                    ·
                      rfl

theorem cell22_1095137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_1095137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095137 prefixEnd_1095137 := by exact prefixLift 1095137
  have htrace : WordTrace (prefixWord ++ tailWord_1095137) baseStart_1095137 baseEnd_1095137 := by
    simpa [prefixWord, tailWord_1095137, baseEnd_1095137] using wordTrace_append hprefix tailTrace_1095137
  have hstable : (prefixWord ++ tailWord_1095137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095137).length < 2 ^ (prefixWord ++ tailWord_1095137).sum := by decide
  have hdescent : baseEnd_1095137 < baseStart_1095137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095242 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1095242 : Nat := 118140960795 + 1095242 * 2 ^ 59
def prefixEnd_1095242 : Nat := 4983230072969 + 3 ^ 40 * 1095242 * 2
def baseEnd_1095242 : Nat := 374923719327806062892053

theorem tailTrace_1095242 : CollatzResearch.WordTrace tailWord_1095242 prefixEnd_1095242 374923719327806062892053 := by
  unfold tailWord_1095242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986689374533190321675995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26631171665421840857802653 9986689374533190321675995)
  ·
    refine ⟨14980034061799785482513993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9986689374533190321675995 14980034061799785482513993)
    ·
      refine ⟨11235025546349839111885495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14980034061799785482513993 11235025546349839111885495)
      ·
        refine ⟨16852538319524758667828243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11235025546349839111885495 16852538319524758667828243)
        ·
          refine ⟨25278807479287138001742365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16852538319524758667828243 25278807479287138001742365)
          ·
            refine ⟨9479552804732676750653387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25278807479287138001742365 9479552804732676750653387)
            ·
              refine ⟨14219329207099015125980081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9479552804732676750653387 14219329207099015125980081)
              ·
                refine ⟨10664496905324261344485061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14219329207099015125980081 10664496905324261344485061)
                ·
                  refine ⟨1999593169748299002090949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10664496905324261344485061 1999593169748299002090949)
                  ·
                    refine ⟨374923719327806062892053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1999593169748299002090949 374923719327806062892053)
                    ·
                      rfl

theorem cell22_1095242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1095242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095242 prefixEnd_1095242 := by exact prefixLift 1095242
  have htrace : WordTrace (prefixWord ++ tailWord_1095242) baseStart_1095242 baseEnd_1095242 := by
    simpa [prefixWord, tailWord_1095242, baseEnd_1095242] using wordTrace_append hprefix tailTrace_1095242
  have hstable : (prefixWord ++ tailWord_1095242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095242).length < 2 ^ (prefixWord ++ tailWord_1095242).sum := by decide
  have hdescent : baseEnd_1095242 < baseStart_1095242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095278 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1095278 : Nat := 118140960795 + 1095278 * 2 ^ 59
def prefixEnd_1095278 : Nat := 4983230072969 + 3 ^ 40 * 1095278 * 2
def baseEnd_1095278 : Nat := 374936042863513968991943

theorem tailTrace_1095278 : CollatzResearch.WordTrace tailWord_1095278 prefixEnd_1095278 374936042863513968991943 := by
  unfold tailWord_1095278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993508815750292429376811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26632047017334892956676325 4993508815750292429376811)
  ·
    refine ⟨7490263223625438644065217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4993508815750292429376811 7490263223625438644065217)
    ·
      refine ⟨5617697417719078983048913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7490263223625438644065217 5617697417719078983048913)
      ·
        refine ⟨4213273063289309237286685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5617697417719078983048913 4213273063289309237286685)
        ·
          refine ⟨1579977398733490963982507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4213273063289309237286685 1579977398733490963982507)
          ·
            refine ⟨2369966098100236445973761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579977398733490963982507 2369966098100236445973761)
            ·
              refine ⟨1777474573575177334480321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369966098100236445973761 1777474573575177334480321)
              ·
                refine ⟨1333105930181383000860241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777474573575177334480321 1333105930181383000860241)
                ·
                  refine ⟨999829447636037250645181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1333105930181383000860241 999829447636037250645181)
                  ·
                    refine ⟨374936042863513968991943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999829447636037250645181 374936042863513968991943)
                    ·
                      rfl

theorem cell22_1095278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1095278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095278 prefixEnd_1095278 := by exact prefixLift 1095278
  have htrace : WordTrace (prefixWord ++ tailWord_1095278) baseStart_1095278 baseEnd_1095278 := by
    simpa [prefixWord, tailWord_1095278, baseEnd_1095278] using wordTrace_append hprefix tailTrace_1095278
  have hstable : (prefixWord ++ tailWord_1095278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095278).length < 2 ^ (prefixWord ++ tailWord_1095278).sum := by decide
  have hdescent : baseEnd_1095278 < baseStart_1095278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095289 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 3, 3]
def baseStart_1095289 : Nat := 118140960795 + 1095289 * 2 ^ 59
def prefixEnd_1095289 : Nat := 4983230072969 + 3 ^ 40 * 1095289 * 2
def baseEnd_1095289 : Nat := 374939808388313606966909

theorem tailTrace_1095289 : CollatzResearch.WordTrace tailWord_1095289 prefixEnd_1095289 374939808388313606966909 := by
  unfold tailWord_1095289
  simp only [CollatzResearch.WordTrace]
  refine ⟨39948471728962488313664921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26632314485974992209109947 39948471728962488313664921)
  ·
    refine ⟨29961353796721866235248691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39948471728962488313664921 29961353796721866235248691)
    ·
      refine ⟨44942030695082799352873037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29961353796721866235248691 44942030695082799352873037)
      ·
        refine ⟨16853261510656049757327389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44942030695082799352873037 16853261510656049757327389)
        ·
          refine ⟨6319973066496018658997771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16853261510656049757327389 6319973066496018658997771)
          ·
            refine ⟨9479959599744027988496657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319973066496018658997771 9479959599744027988496657)
            ·
              refine ⟨7109969699808020991372493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9479959599744027988496657 7109969699808020991372493)
              ·
                refine ⟨2666238637428007871764685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7109969699808020991372493 2666238637428007871764685)
                ·
                  refine ⟨999839489035502951911757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2666238637428007871764685 999839489035502951911757)
                  ·
                    refine ⟨374939808388313606966909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999839489035502951911757 374939808388313606966909)
                    ·
                      rfl

theorem cell22_1095289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_1095289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095289 prefixEnd_1095289 := by exact prefixLift 1095289
  have htrace : WordTrace (prefixWord ++ tailWord_1095289) baseStart_1095289 baseEnd_1095289 := by
    simpa [prefixWord, tailWord_1095289, baseEnd_1095289] using wordTrace_append hprefix tailTrace_1095289
  have hstable : (prefixWord ++ tailWord_1095289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095289).length < 2 ^ (prefixWord ++ tailWord_1095289).sum := by decide
  have hdescent : baseEnd_1095289 < baseStart_1095289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095306 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_1095306 : Nat := 118140960795 + 1095306 * 2 ^ 59
def prefixEnd_1095306 : Nat := 4983230072969 + 3 ^ 40 * 1095306 * 2
def baseEnd_1095306 : Nat := 374945627835731229291857

theorem tailTrace_1095306 : CollatzResearch.WordTrace tailWord_1095306 prefixEnd_1095306 374945627835731229291857 := by
  unfold tailWord_1095306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9987272942475225054258443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26632727846600600144689181 9987272942475225054258443)
  ·
    refine ⟨14980909413712837581387665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9987272942475225054258443 14980909413712837581387665)
    ·
      refine ⟨11235682060284628186040749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14980909413712837581387665 11235682060284628186040749)
      ·
        refine ⟨4213380772606735569765281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11235682060284628186040749 4213380772606735569765281)
        ·
          refine ⟨3160035579455051677323961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4213380772606735569765281 3160035579455051677323961)
          ·
            refine ⟨2370026684591288757992971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3160035579455051677323961 2370026684591288757992971)
            ·
              refine ⟨3555040026886933136989457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370026684591288757992971 3555040026886933136989457)
              ·
                refine ⟨2666280020165199852742093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3555040026886933136989457 2666280020165199852742093)
                ·
                  refine ⟨999855007561949944778285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2666280020165199852742093 999855007561949944778285)
                  ·
                    refine ⟨374945627835731229291857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999855007561949944778285 374945627835731229291857)
                    ·
                      rfl

theorem cell22_1095306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_1095306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095306 prefixEnd_1095306 := by exact prefixLift 1095306
  have htrace : WordTrace (prefixWord ++ tailWord_1095306) baseStart_1095306 baseEnd_1095306 := by
    simpa [prefixWord, tailWord_1095306, baseEnd_1095306] using wordTrace_append hprefix tailTrace_1095306
  have hstable : (prefixWord ++ tailWord_1095306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095306).length < 2 ^ (prefixWord ++ tailWord_1095306).sum := by decide
  have hdescent : baseEnd_1095306 < baseStart_1095306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095364 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1095364 : Nat := 118140960795 + 1095364 * 2 ^ 59
def prefixEnd_1095364 : Nat := 4983230072969 + 3 ^ 40 * 1095364 * 2
def baseEnd_1095364 : Nat := 124988494140346137113893

theorem tailTrace_1095364 : CollatzResearch.WordTrace tailWord_1095364 prefixEnd_1095364 124988494140346137113893 := by
  unfold tailWord_1095364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19975603601845388061322573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26634138135793850748430097 19975603601845388061322573)
  ·
    refine ⟨7490851350692020522995965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19975603601845388061322573 7490851350692020522995965)
    ·
      refine ⟨2809069256509507696123487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7490851350692020522995965 2809069256509507696123487)
      ·
        refine ⟨4213603884764261544185231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2809069256509507696123487 4213603884764261544185231)
        ·
          refine ⟨6320405827146392316277847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4213603884764261544185231 6320405827146392316277847)
          ·
            refine ⟨9480608740719588474416771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6320405827146392316277847 9480608740719588474416771)
            ·
              refine ⟨14220913111079382711625157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9480608740719588474416771 14220913111079382711625157)
              ·
                refine ⟨2666421208327384258429717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14220913111079382711625157 2666421208327384258429717)
                ·
                  refine ⟨124988494140346137113893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2666421208327384258429717 124988494140346137113893)
                  ·
                    rfl

theorem cell22_1095364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1095364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095364 prefixEnd_1095364 := by exact prefixLift 1095364
  have htrace : WordTrace (prefixWord ++ tailWord_1095364) baseStart_1095364 baseEnd_1095364 := by
    simpa [prefixWord, tailWord_1095364, baseEnd_1095364] using wordTrace_append hprefix tailTrace_1095364
  have hstable : (prefixWord ++ tailWord_1095364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095364).length < 2 ^ (prefixWord ++ tailWord_1095364).sum := by decide
  have hdescent : baseEnd_1095364 < baseStart_1095364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095392 : List Nat := [2, 1, 1, 3, 1, 2, 12]
def baseStart_1095392 : Nat := 118140960795 + 1095392 * 2 ^ 59
def prefixEnd_1095392 : Nat := 4983230072969 + 3 ^ 40 * 1095392 * 2
def baseEnd_1095392 : Nat := 13887965459009469320059

theorem tailTrace_1095392 : CollatzResearch.WordTrace tailWord_1095392 prefixEnd_1095392 13887965459009469320059 := by
  unfold tailWord_1095392
  simp only [CollatzResearch.WordTrace]
  refine ⟨19976114223794668452332215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26634818965059557936442953 19976114223794668452332215)
  ·
    refine ⟨29964171335692002678498323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19976114223794668452332215 29964171335692002678498323)
    ·
      refine ⟨44946257003538004017747485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29964171335692002678498323 44946257003538004017747485)
      ·
        refine ⟨16854846376326751506655307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44946257003538004017747485 16854846376326751506655307)
        ·
          refine ⟨25282269564490127259982961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16854846376326751506655307 25282269564490127259982961)
          ·
            refine ⟨18961702173367595444987221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25282269564490127259982961 18961702173367595444987221)
            ·
              refine ⟨13887965459009469320059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 18961702173367595444987221 13887965459009469320059)
              ·
                rfl

theorem cell22_1095392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 12].length) (baseStart_1095392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095392 prefixEnd_1095392 := by exact prefixLift 1095392
  have htrace : WordTrace (prefixWord ++ tailWord_1095392) baseStart_1095392 baseEnd_1095392 := by
    simpa [prefixWord, tailWord_1095392, baseEnd_1095392] using wordTrace_append hprefix tailTrace_1095392
  have hstable : (prefixWord ++ tailWord_1095392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095392).length < 2 ^ (prefixWord ++ tailWord_1095392).sum := by decide
  have hdescent : baseEnd_1095392 < baseStart_1095392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095396 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_1095396 : Nat := 118140960795 + 1095396 * 2 ^ 59
def prefixEnd_1095396 : Nat := 4983230072969 + 3 ^ 40 * 1095396 * 2
def baseEnd_1095396 : Nat := 374976436675000994541581

theorem tailTrace_1095396 : CollatzResearch.WordTrace tailWord_1095396 prefixEnd_1095396 374976436675000994541581 := by
  unfold tailWord_1095396
  simp only [CollatzResearch.WordTrace]
  refine ⟨19976187169787422793905021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26634916226383230391873361 19976187169787422793905021)
  ·
    refine ⟨7491070188670283547714383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19976187169787422793905021 7491070188670283547714383)
    ·
      refine ⟨11236605283005425321571575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7491070188670283547714383 11236605283005425321571575)
      ·
        refine ⟨16854907924508137982357363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11236605283005425321571575 16854907924508137982357363)
        ·
          refine ⟨25282361886762206973536045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16854907924508137982357363 25282361886762206973536045)
          ·
            refine ⟨9480885707535827615076017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25282361886762206973536045 9480885707535827615076017)
            ·
              refine ⟨7110664280651870711307013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9480885707535827615076017 7110664280651870711307013)
              ·
                refine ⟨1333249552622225758370065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7110664280651870711307013 1333249552622225758370065)
                ·
                  refine ⟨999937164466669318777549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1333249552622225758370065 999937164466669318777549)
                  ·
                    refine ⟨374976436675000994541581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999937164466669318777549 374976436675000994541581)
                    ·
                      rfl

theorem cell22_1095396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_1095396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095396 prefixEnd_1095396 := by exact prefixLift 1095396
  have htrace : WordTrace (prefixWord ++ tailWord_1095396) baseStart_1095396 baseEnd_1095396 := by
    simpa [prefixWord, tailWord_1095396, baseEnd_1095396] using wordTrace_append hprefix tailTrace_1095396
  have hstable : (prefixWord ++ tailWord_1095396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095396).length < 2 ^ (prefixWord ++ tailWord_1095396).sum := by decide
  have hdescent : baseEnd_1095396 < baseStart_1095396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095409 : List Nat := [1, 2, 2, 2, 2, 4, 2, 7]
def baseStart_1095409 : Nat := 118140960795 + 1095409 * 2 ^ 59
def prefixEnd_1095409 : Nat := 4983230072969 + 3 ^ 40 * 1095409 * 2
def baseEnd_1095409 : Nat := 41664542982297032662949

theorem tailTrace_1095409 : CollatzResearch.WordTrace tailWord_1095409 prefixEnd_1095409 41664542982297032662949 := by
  unfold tailWord_1095409
  simp only [CollatzResearch.WordTrace]
  refine ⟨39952848488527748808033281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26635232325685165872022187 39952848488527748808033281)
  ·
    refine ⟨29964636366395811606024961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39952848488527748808033281 29964636366395811606024961)
    ·
      refine ⟨22473477274796858704518721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29964636366395811606024961 22473477274796858704518721)
      ·
        refine ⟨16855107956097644028389041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22473477274796858704518721 16855107956097644028389041)
        ·
          refine ⟨12641330967073233021291781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16855107956097644028389041 12641330967073233021291781)
          ·
            refine ⟨2370249556326231191492209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12641330967073233021291781 2370249556326231191492209)
            ·
              refine ⟨1777687167244673393619157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370249556326231191492209 1777687167244673393619157)
              ·
                refine ⟨41664542982297032662949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1777687167244673393619157 41664542982297032662949)
                ·
                  rfl

theorem cell22_1095409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 7].length) (baseStart_1095409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095409 prefixEnd_1095409 := by exact prefixLift 1095409
  have htrace : WordTrace (prefixWord ++ tailWord_1095409) baseStart_1095409 baseEnd_1095409 := by
    simpa [prefixWord, tailWord_1095409, baseEnd_1095409] using wordTrace_append hprefix tailTrace_1095409
  have hstable : (prefixWord ++ tailWord_1095409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095409).length < 2 ^ (prefixWord ++ tailWord_1095409).sum := by decide
  have hdescent : baseEnd_1095409 < baseStart_1095409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095644 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1095644 : Nat := 118140960795 + 1095644 * 2 ^ 59
def prefixEnd_1095644 : Nat := 4983230072969 + 3 ^ 40 * 1095644 * 2
def baseEnd_1095644 : Nat := 375061332143211014340821

theorem tailTrace_1095644 : CollatzResearch.WordTrace tailWord_1095644 prefixEnd_1095644 375061332143211014340821 := by
  unfold tailWord_1095644
  simp only [CollatzResearch.WordTrace]
  refine ⟨19980709821338191971418993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26640946428450922628558657 19980709821338191971418993)
  ·
    refine ⟨14985532366003643978564245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19980709821338191971418993 14985532366003643978564245)
    ·
      refine ⟨702446829656420811495199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14985532366003643978564245 702446829656420811495199)
      ·
        refine ⟨1053670244484631217242799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702446829656420811495199 1053670244484631217242799)
        ·
          refine ⟨1580505366726946825864199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053670244484631217242799 1580505366726946825864199)
          ·
            refine ⟨2370758050090420238796299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580505366726946825864199 2370758050090420238796299)
            ·
              refine ⟨3556137075135630358194449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370758050090420238796299 3556137075135630358194449)
              ·
                refine ⟨2667102806351722768645837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556137075135630358194449 2667102806351722768645837)
                ·
                  refine ⟨1000163552381896038242189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2667102806351722768645837 1000163552381896038242189)
                  ·
                    refine ⟨375061332143211014340821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000163552381896038242189 375061332143211014340821)
                    ·
                      rfl

theorem cell22_1095644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1095644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095644 prefixEnd_1095644 := by exact prefixLift 1095644
  have htrace : WordTrace (prefixWord ++ tailWord_1095644) baseStart_1095644 baseEnd_1095644 := by
    simpa [prefixWord, tailWord_1095644, baseEnd_1095644] using wordTrace_append hprefix tailTrace_1095644
  have hstable : (prefixWord ++ tailWord_1095644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095644).length < 2 ^ (prefixWord ++ tailWord_1095644).sum := by decide
  have hdescent : baseEnd_1095644 < baseStart_1095644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095651 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 8]
def baseStart_1095651 : Nat := 118140960795 + 1095651 * 2 ^ 59
def prefixEnd_1095651 : Nat := 4983230072969 + 3 ^ 40 * 1095651 * 2
def baseEnd_1095651 : Nat := 125021242795421776471933

theorem tailTrace_1095651 : CollatzResearch.WordTrace tailWord_1095651 prefixEnd_1095651 125021242795421776471933 := by
  unfold tailWord_1095651
  simp only [CollatzResearch.WordTrace]
  refine ⟨39961674953651024138342807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26641116635767349425561871 39961674953651024138342807)
  ·
    refine ⟨59942512430476536207514211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39961674953651024138342807 59942512430476536207514211)
    ·
      refine ⟨89913768645714804311271317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59942512430476536207514211 89913768645714804311271317)
      ·
        refine ⟨4214707905267881452090843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89913768645714804311271317 4214707905267881452090843)
        ·
          refine ⟨6322061857901822178136265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214707905267881452090843 6322061857901822178136265)
          ·
            refine ⟨4741546393426366633602199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6322061857901822178136265 4741546393426366633602199)
            ·
              refine ⟨7112319590139549950403299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741546393426366633602199 7112319590139549950403299)
              ·
                refine ⟨10668479385209324925604949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7112319590139549950403299 10668479385209324925604949)
                ·
                  refine ⟨125021242795421776471933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10668479385209324925604949 125021242795421776471933)
                  ·
                    rfl

theorem cell22_1095651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_1095651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095651 prefixEnd_1095651 := by exact prefixLift 1095651
  have htrace : WordTrace (prefixWord ++ tailWord_1095651) baseStart_1095651 baseEnd_1095651 := by
    simpa [prefixWord, tailWord_1095651, baseEnd_1095651] using wordTrace_append hprefix tailTrace_1095651
  have hstable : (prefixWord ++ tailWord_1095651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095651).length < 2 ^ (prefixWord ++ tailWord_1095651).sum := by decide
  have hdescent : baseEnd_1095651 < baseStart_1095651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095711 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 2, 7]
def baseStart_1095711 : Nat := 118140960795 + 1095711 * 2 ^ 59
def prefixEnd_1095711 : Nat := 4983230072969 + 3 ^ 40 * 1095711 * 2
def baseEnd_1095711 : Nat := 375084267612445172915615

theorem tailTrace_1095711 : CollatzResearch.WordTrace tailWord_1095711 prefixEnd_1095711 375084267612445172915615 := by
  unfold tailWord_1095711
  simp only [CollatzResearch.WordTrace]
  refine ⟨39963863333433654385526987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26642575555622436257017991 39963863333433654385526987)
  ·
    refine ⟨59945795000150481578290481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39963863333433654385526987 59945795000150481578290481)
    ·
      refine ⟨44959346250112861183717861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59945795000150481578290481 44959346250112861183717861)
      ·
        refine ⟨8429877421896161471947099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44959346250112861183717861 8429877421896161471947099)
        ·
          refine ⟨12644816132844242207920649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8429877421896161471947099 12644816132844242207920649)
          ·
            refine ⟨9483612099633181655940487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12644816132844242207920649 9483612099633181655940487)
            ·
              refine ⟨14225418149449772483910731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9483612099633181655940487 14225418149449772483910731)
              ·
                refine ⟨21338127224174658725866097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14225418149449772483910731 21338127224174658725866097)
                ·
                  refine ⟨16003595418130994044399573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21338127224174658725866097 16003595418130994044399573)
                  ·
                    refine ⟨375084267612445172915615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16003595418130994044399573 375084267612445172915615)
                    ·
                      rfl

theorem cell22_1095711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_1095711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095711 prefixEnd_1095711 := by exact prefixLift 1095711
  have htrace : WordTrace (prefixWord ++ tailWord_1095711) baseStart_1095711 baseEnd_1095711 := by
    simpa [prefixWord, tailWord_1095711, baseEnd_1095711] using wordTrace_append hprefix tailTrace_1095711
  have hstable : (prefixWord ++ tailWord_1095711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095711).length < 2 ^ (prefixWord ++ tailWord_1095711).sum := by decide
  have hdescent : baseEnd_1095711 < baseStart_1095711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095713 : List Nat := [1, 2, 3, 2, 4, 1, 1, 8]
def baseStart_1095713 : Nat := 118140960795 + 1095713 * 2 ^ 59
def prefixEnd_1095713 : Nat := 4983230072969 + 3 ^ 40 * 1095713 * 2
def baseEnd_1095713 : Nat := 41676105805924203818401

theorem tailTrace_1095713 : CollatzResearch.WordTrace tailWord_1095713 prefixEnd_1095713 41676105805924203818401 := by
  unfold tailWord_1095713
  simp only [CollatzResearch.WordTrace]
  refine ⟨39963936279426408727099793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26642624186284272484733195 39963936279426408727099793)
  ·
    refine ⟨29972952209569806545324845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39963936279426408727099793 29972952209569806545324845)
    ·
      refine ⟨11239857078588677454496817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29972952209569806545324845 11239857078588677454496817)
      ·
        refine ⟨8429892808941508090872613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11239857078588677454496817 8429892808941508090872613)
        ·
          refine ⟨1580604901676532767038615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8429892808941508090872613 1580604901676532767038615)
          ·
            refine ⟨2370907352514799150557923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580604901676532767038615 2370907352514799150557923)
            ·
              refine ⟨3556361028772198725836885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370907352514799150557923 3556361028772198725836885)
              ·
                refine ⟨41676105805924203818401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3556361028772198725836885 41676105805924203818401)
                ·
                  rfl

theorem cell22_1095713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 8].length) (baseStart_1095713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095713 prefixEnd_1095713 := by exact prefixLift 1095713
  have htrace : WordTrace (prefixWord ++ tailWord_1095713) baseStart_1095713 baseEnd_1095713 := by
    simpa [prefixWord, tailWord_1095713, baseEnd_1095713] using wordTrace_append hprefix tailTrace_1095713
  have hstable : (prefixWord ++ tailWord_1095713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095713).length < 2 ^ (prefixWord ++ tailWord_1095713).sum := by decide
  have hdescent : baseEnd_1095713 < baseStart_1095713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095719 : List Nat := [1, 1, 7, 1, 2, 2, 1, 3, 4]
def baseStart_1095719 : Nat := 118140960795 + 1095719 * 2 ^ 59
def prefixEnd_1095719 : Nat := 4983230072969 + 3 ^ 40 * 1095719 * 2
def baseEnd_1095719 : Nat := 125029002058645272905197

theorem tailTrace_1095719 : CollatzResearch.WordTrace tailWord_1095719 prefixEnd_1095719 125029002058645272905197 := by
  unfold tailWord_1095719
  simp only [CollatzResearch.WordTrace]
  refine ⟨39964155117404671751818211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26642770078269781167878807 39964155117404671751818211)
  ·
    refine ⟨59946232676107007627727317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39964155117404671751818211 59946232676107007627727317)
    ·
      refine ⟨1404989828346257991274859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 59946232676107007627727317 1404989828346257991274859)
      ·
        refine ⟨2107484742519386986912289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404989828346257991274859 2107484742519386986912289)
        ·
          refine ⟨1580613556889540240184217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2107484742519386986912289 1580613556889540240184217)
          ·
            refine ⟨1185460167667155180138163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1580613556889540240184217 1185460167667155180138163)
            ·
              refine ⟨1778190251500732770207245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185460167667155180138163 1778190251500732770207245)
              ·
                refine ⟨666821344312774788827717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1778190251500732770207245 666821344312774788827717)
                ·
                  refine ⟨125029002058645272905197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666821344312774788827717 125029002058645272905197)
                  ·
                    rfl

theorem cell22_1095719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 4].length) (baseStart_1095719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095719 prefixEnd_1095719 := by exact prefixLift 1095719
  have htrace : WordTrace (prefixWord ++ tailWord_1095719) baseStart_1095719 baseEnd_1095719 := by
    simpa [prefixWord, tailWord_1095719, baseEnd_1095719] using wordTrace_append hprefix tailTrace_1095719
  have hstable : (prefixWord ++ tailWord_1095719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095719).length < 2 ^ (prefixWord ++ tailWord_1095719).sum := by decide
  have hdescent : baseEnd_1095719 < baseStart_1095719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095732 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1095732 : Nat := 118140960795 + 1095732 * 2 ^ 59
def prefixEnd_1095732 : Nat := 4983230072969 + 3 ^ 40 * 1095732 * 2
def baseEnd_1095732 : Nat := 375091456341608118140551

theorem tailTrace_1095732 : CollatzResearch.WordTrace tailWord_1095732 prefixEnd_1095732 375091456341608118140551 := by
  unfold tailWord_1095732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19982314633178787486020725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26643086177571716648027633 19982314633178787486020725)
  ·
    refine ⟨1873341996860511326814443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19982314633178787486020725 1873341996860511326814443)
    ·
      refine ⟨2810012995290766990221665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873341996860511326814443 2810012995290766990221665)
      ·
        refine ⟨2107509746468075242666249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2810012995290766990221665 2107509746468075242666249)
        ·
          refine ⟨1580632309851056431999687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2107509746468075242666249 1580632309851056431999687)
          ·
            refine ⟨2370948464776584647999531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580632309851056431999687 2370948464776584647999531)
            ·
              refine ⟨3556422697164876971999297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370948464776584647999531 3556422697164876971999297)
              ·
                refine ⟨2667317022873657728999473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556422697164876971999297 2667317022873657728999473)
                ·
                  refine ⟨2000487767155243296749605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2667317022873657728999473 2000487767155243296749605)
                  ·
                    refine ⟨375091456341608118140551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2000487767155243296749605 375091456341608118140551)
                    ·
                      rfl

theorem cell22_1095732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1095732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095732 prefixEnd_1095732 := by exact prefixLift 1095732
  have htrace : WordTrace (prefixWord ++ tailWord_1095732) baseStart_1095732 baseEnd_1095732 := by
    simpa [prefixWord, tailWord_1095732, baseEnd_1095732] using wordTrace_append hprefix tailTrace_1095732
  have hstable : (prefixWord ++ tailWord_1095732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095732).length < 2 ^ (prefixWord ++ tailWord_1095732).sum := by decide
  have hdescent : baseEnd_1095732 < baseStart_1095732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095837 : List Nat := [1, 4, 2, 1, 1, 4, 2, 3, 4]
def baseStart_1095837 : Nat := 118140960795 + 1095837 * 2 ^ 59
def prefixEnd_1095837 : Nat := 4983230072969 + 3 ^ 40 * 1095837 * 2
def baseEnd_1095837 : Nat := 125042466662474281421743

theorem tailTrace_1095837 : CollatzResearch.WordTrace tailWord_1095837 prefixEnd_1095837 125042466662474281421743 := by
  unfold tailWord_1095837
  simp only [CollatzResearch.WordTrace]
  refine ⟨39968458930977177904613765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26645639287318118603075843 39968458930977177904613765)
  ·
    refine ⟨7494086049558220857115081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39968458930977177904613765 7494086049558220857115081)
    ·
      refine ⟨5620564537168665642836311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7494086049558220857115081 5620564537168665642836311)
      ·
        refine ⟨8430846805752998464254467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5620564537168665642836311 8430846805752998464254467)
        ·
          refine ⟨12646270208629497696381701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8430846805752998464254467 12646270208629497696381701)
          ·
            refine ⟨2371175664118030818071569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12646270208629497696381701 2371175664118030818071569)
            ·
              refine ⟨1778381748088523113553677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371175664118030818071569 1778381748088523113553677)
              ·
                refine ⟨666893155533196167582629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1778381748088523113553677 666893155533196167582629)
                ·
                  refine ⟨125042466662474281421743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666893155533196167582629 125042466662474281421743)
                  ·
                    rfl

theorem cell22_1095837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_1095837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095837 prefixEnd_1095837 := by exact prefixLift 1095837
  have htrace : WordTrace (prefixWord ++ tailWord_1095837) baseStart_1095837 baseEnd_1095837 := by
    simpa [prefixWord, tailWord_1095837, baseEnd_1095837] using wordTrace_append hprefix tailTrace_1095837
  have hstable : (prefixWord ++ tailWord_1095837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095837).length < 2 ^ (prefixWord ++ tailWord_1095837).sum := by decide
  have hdescent : baseEnd_1095837 < baseStart_1095837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095839 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 1, 4]
def baseStart_1095839 : Nat := 118140960795 + 1095839 * 2 ^ 59
def prefixEnd_1095839 : Nat := 4983230072969 + 3 ^ 40 * 1095839 * 2
def baseEnd_1095839 : Nat := 375128084628295505715223

theorem tailTrace_1095839 : CollatzResearch.WordTrace tailWord_1095839 prefixEnd_1095839 375128084628295505715223 := by
  unfold tailWord_1095839
  simp only [CollatzResearch.WordTrace]
  refine ⟨39968531876969932246186571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26645687917979954830791047 39968531876969932246186571)
  ·
    refine ⟨59952797815454898369279857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39968531876969932246186571 59952797815454898369279857)
    ·
      refine ⟨44964598361591173776959893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59952797815454898369279857 44964598361591173776959893)
      ·
        refine ⟨2107715548199586270794995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44964598361591173776959893 2107715548199586270794995)
        ·
          refine ⟨3161573322299379406192493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107715548199586270794995 3161573322299379406192493)
          ·
            refine ⟨1185589995862267277322185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3161573322299379406192493 1185589995862267277322185)
            ·
              refine ⟨889192496896700457991639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185589995862267277322185 889192496896700457991639)
              ·
                refine ⟨1333788745345050686987459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889192496896700457991639 1333788745345050686987459)
                ·
                  refine ⟨2000683118017576030481189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1333788745345050686987459 2000683118017576030481189)
                  ·
                    refine ⟨375128084628295505715223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2000683118017576030481189 375128084628295505715223)
                    ·
                      rfl

theorem cell22_1095839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_1095839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095839 prefixEnd_1095839 := by exact prefixLift 1095839
  have htrace : WordTrace (prefixWord ++ tailWord_1095839) baseStart_1095839 baseEnd_1095839 := by
    simpa [prefixWord, tailWord_1095839, baseEnd_1095839] using wordTrace_append hprefix tailTrace_1095839
  have hstable : (prefixWord ++ tailWord_1095839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095839).length < 2 ^ (prefixWord ++ tailWord_1095839).sum := by decide
  have hdescent : baseEnd_1095839 < baseStart_1095839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095854 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_1095854 : Nat := 118140960795 + 1095854 * 2 ^ 59
def prefixEnd_1095854 : Nat := 4983230072969 + 3 ^ 40 * 1095854 * 2
def baseEnd_1095854 : Nat := 125044406478280155530059

theorem tailTrace_1095854 : CollatzResearch.WordTrace tailWord_1095854 prefixEnd_1095854 125044406478280155530059 := by
  unfold tailWord_1095854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4996134871489448725997827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26646052647943726538655077 4996134871489448725997827)
  ·
    refine ⟨7494202307234173088996741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4996134871489448725997827 7494202307234173088996741)
    ·
      refine ⟨1405162932606407454186889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7494202307234173088996741 1405162932606407454186889)
      ·
        refine ⟨1053872199454805590640167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1405162932606407454186889 1053872199454805590640167)
        ·
          refine ⟨1580808299182208385960251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053872199454805590640167 1580808299182208385960251)
          ·
            refine ⟨2371212448773312578940377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580808299182208385960251 2371212448773312578940377)
            ·
              refine ⟨1778409336579984434205283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371212448773312578940377 1778409336579984434205283)
              ·
                refine ⟨2667614004869976651307925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778409336579984434205283 2667614004869976651307925)
                ·
                  refine ⟨125044406478280155530059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2667614004869976651307925 125044406478280155530059)
                  ·
                    rfl

theorem cell22_1095854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_1095854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095854 prefixEnd_1095854 := by exact prefixLift 1095854
  have htrace : WordTrace (prefixWord ++ tailWord_1095854) baseStart_1095854 baseEnd_1095854 := by
    simpa [prefixWord, tailWord_1095854, baseEnd_1095854] using wordTrace_append hprefix tailTrace_1095854
  have hstable : (prefixWord ++ tailWord_1095854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095854).length < 2 ^ (prefixWord ++ tailWord_1095854).sum := by decide
  have hdescent : baseEnd_1095854 < baseStart_1095854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095965 : List Nat := [1, 4, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_1095965 : Nat := 118140960795 + 1095965 * 2 ^ 59
def prefixEnd_1095965 : Nat := 4983230072969 + 3 ^ 40 * 1095965 * 2
def baseEnd_1095965 : Nat := 375171217003273177064837

theorem tailTrace_1095965 : CollatzResearch.WordTrace tailWord_1095965 prefixEnd_1095965 375171217003273177064837 := by
  unfold tailWord_1095965
  simp only [CollatzResearch.WordTrace]
  refine ⟨39973127474513455765273349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26648751649675637176848899 39973127474513455765273349)
  ·
    refine ⟨7494961401471272955988753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39973127474513455765273349 7494961401471272955988753)
    ·
      refine ⟨5621221051103454716991565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7494961401471272955988753 5621221051103454716991565)
      ·
        refine ⟨2107957894163795518871837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5621221051103454716991565 2107957894163795518871837)
        ·
          refine ⟨790484210311423319576939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2107957894163795518871837 790484210311423319576939)
          ·
            refine ⟨1185726315467134979365409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790484210311423319576939 1185726315467134979365409)
            ·
              refine ⟨889294736600351234524057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185726315467134979365409 889294736600351234524057)
              ·
                refine ⟨666971052450263425893043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889294736600351234524057 666971052450263425893043)
                ·
                  refine ⟨1000456578675395138839565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666971052450263425893043 1000456578675395138839565)
                  ·
                    refine ⟨375171217003273177064837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000456578675395138839565 375171217003273177064837)
                    ·
                      rfl

theorem cell22_1095965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_1095965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095965 prefixEnd_1095965 := by exact prefixLift 1095965
  have htrace : WordTrace (prefixWord ++ tailWord_1095965) baseStart_1095965 baseEnd_1095965 := by
    simpa [prefixWord, tailWord_1095965, baseEnd_1095965] using wordTrace_append hprefix tailTrace_1095965
  have hstable : (prefixWord ++ tailWord_1095965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095965).length < 2 ^ (prefixWord ++ tailWord_1095965).sum := by decide
  have hdescent : baseEnd_1095965 < baseStart_1095965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095987 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 2, 3]
def baseStart_1095987 : Nat := 118140960795 + 1095987 * 2 ^ 59
def prefixEnd_1095987 : Nat := 4983230072969 + 3 ^ 40 * 1095987 * 2
def baseEnd_1095987 : Nat := 375178748052872453014769

theorem tailTrace_1095987 : CollatzResearch.WordTrace tailWord_1095987 prefixEnd_1095987 375178748052872453014769 := by
  unfold tailWord_1095987
  simp only [CollatzResearch.WordTrace]
  refine ⟨39973929880433753522574215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26649286586955835681716143 39973929880433753522574215)
  ·
    refine ⟨59960894820650630283861323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39973929880433753522574215 59960894820650630283861323)
    ·
      refine ⟨89941342230975945425791985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59960894820650630283861323 89941342230975945425791985)
      ·
        refine ⟨67456006673231959069343989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89941342230975945425791985 67456006673231959069343989)
        ·
          refine ⟨6324000625615496162750999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67456006673231959069343989 6324000625615496162750999)
          ·
            refine ⟨9486000938423244244126499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6324000625615496162750999 9486000938423244244126499)
            ·
              refine ⟨14229001407634866366189749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9486000938423244244126499 14229001407634866366189749)
              ·
                refine ⟨1333968881965768721830289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14229001407634866366189749 1333968881965768721830289)
                ·
                  refine ⟨1000476661474326541372717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1333968881965768721830289 1000476661474326541372717)
                  ·
                    refine ⟨375178748052872453014769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000476661474326541372717 375178748052872453014769)
                    ·
                      rfl

theorem cell22_1095987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 3].length) (baseStart_1095987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1095987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1095987 prefixEnd_1095987 := by exact prefixLift 1095987
  have htrace : WordTrace (prefixWord ++ tailWord_1095987) baseStart_1095987 baseEnd_1095987 := by
    simpa [prefixWord, tailWord_1095987, baseEnd_1095987] using wordTrace_append hprefix tailTrace_1095987
  have hstable : (prefixWord ++ tailWord_1095987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095987).length < 2 ^ (prefixWord ++ tailWord_1095987).sum := by decide
  have hdescent : baseEnd_1095987 < baseStart_1095987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096021 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1096021 : Nat := 118140960795 + 1096021 * 2 ^ 59
def prefixEnd_1096021 : Nat := 4983230072969 + 3 ^ 40 * 1096021 * 2
def baseEnd_1096021 : Nat := 375190386947707697664665

theorem tailTrace_1096021 : CollatzResearch.WordTrace tailWord_1096021 prefixEnd_1096021 375190386947707697664665 := by
  unfold tailWord_1096021
  simp only [CollatzResearch.WordTrace]
  refine ⟨39975169962310577329311917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26650113308207051552874611 39975169962310577329311917)
  ·
    refine ⟨14990688735866466498491969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39975169962310577329311917 14990688735866466498491969)
    ·
      refine ⟨11243016551899849873868977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14990688735866466498491969 11243016551899849873868977)
      ·
        refine ⟨8432262413924887405401733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11243016551899849873868977 8432262413924887405401733)
        ·
          refine ⟨1581049202610916388512825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8432262413924887405401733 1581049202610916388512825)
          ·
            refine ⟨1185786901958187291384619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581049202610916388512825 1185786901958187291384619)
            ·
              refine ⟨1778680352937280937076929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185786901958187291384619 1778680352937280937076929)
              ·
                refine ⟨1334010264702960702807697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778680352937280937076929 1334010264702960702807697)
                ·
                  refine ⟨1000507698527220527105773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1334010264702960702807697 1000507698527220527105773)
                  ·
                    refine ⟨375190386947707697664665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000507698527220527105773 375190386947707697664665)
                    ·
                      rfl

theorem cell22_1096021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1096021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096021 prefixEnd_1096021 := by exact prefixLift 1096021
  have htrace : WordTrace (prefixWord ++ tailWord_1096021) baseStart_1096021 baseEnd_1096021 := by
    simpa [prefixWord, tailWord_1096021, baseEnd_1096021] using wordTrace_append hprefix tailTrace_1096021
  have hstable : (prefixWord ++ tailWord_1096021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096021).length < 2 ^ (prefixWord ++ tailWord_1096021).sum := by decide
  have hdescent : baseEnd_1096021 < baseStart_1096021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096060 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1096060 : Nat := 118140960795 + 1096060 * 2 ^ 59
def prefixEnd_1096060 : Nat := 4983230072969 + 3 ^ 40 * 1096060 * 2
def baseEnd_1096060 : Nat := 375203737444724595939545

theorem tailTrace_1096060 : CollatzResearch.WordTrace tailWord_1096060 prefixEnd_1096060 375203737444724595939545 := by
  unfold tailWord_1096060
  simp only [CollatzResearch.WordTrace]
  refine ⟨19988296204584643494990817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26651061606112857993321089 19988296204584643494990817)
  ·
    refine ⟨14991222153438482621243113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19988296204584643494990817 14991222153438482621243113)
    ·
      refine ⟨11243416615078861965932335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14991222153438482621243113 11243416615078861965932335)
      ·
        refine ⟨16865124922618292948898503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11243416615078861965932335 16865124922618292948898503)
        ·
          refine ⟨25297687383927439423347755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16865124922618292948898503 25297687383927439423347755)
          ·
            refine ⟨37946531075891159135021633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25297687383927439423347755 37946531075891159135021633)
            ·
              refine ⟨28459898306918369351266225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37946531075891159135021633 28459898306918369351266225)
              ·
                refine ⟨21344923730188777013449669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28459898306918369351266225 21344923730188777013449669)
                ·
                  refine ⟨4002173199410395690021813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21344923730188777013449669 4002173199410395690021813)
                  ·
                    refine ⟨375203737444724595939545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4002173199410395690021813 375203737444724595939545)
                    ·
                      rfl

theorem cell22_1096060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1096060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096060 prefixEnd_1096060 := by exact prefixLift 1096060
  have htrace : WordTrace (prefixWord ++ tailWord_1096060) baseStart_1096060 baseEnd_1096060 := by
    simpa [prefixWord, tailWord_1096060, baseEnd_1096060] using wordTrace_append hprefix tailTrace_1096060
  have hstable : (prefixWord ++ tailWord_1096060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096060).length < 2 ^ (prefixWord ++ tailWord_1096060).sum := by decide
  have hdescent : baseEnd_1096060 < baseStart_1096060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096105 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_1096105 : Nat := 118140960795 + 1096105 * 2 ^ 59
def prefixEnd_1096105 : Nat := 4983230072969 + 3 ^ 40 * 1096105 * 2
def baseEnd_1096105 : Nat := 375219141864359478564407

theorem tailTrace_1096105 : CollatzResearch.WordTrace tailWord_1096105 prefixEnd_1096105 375219141864359478564407 := by
  unfold tailWord_1096105
  simp only [CollatzResearch.WordTrace]
  refine ⟨39978233694006259675369769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26652155796004173116913179 39978233694006259675369769)
  ·
    refine ⟨29983675270504694756527327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39978233694006259675369769 29983675270504694756527327)
    ·
      refine ⟨44975512905757042134790991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29983675270504694756527327 44975512905757042134790991)
      ·
        refine ⟨67463269358635563202186487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44975512905757042134790991 67463269358635563202186487)
        ·
          refine ⟨101194904037953344803279731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67463269358635563202186487 101194904037953344803279731)
          ·
            refine ⟨151792356056930017204919597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101194904037953344803279731 151792356056930017204919597)
            ·
              refine ⟨56922133521348756451844849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151792356056930017204919597 56922133521348756451844849)
              ·
                refine ⟨42691600141011567338883637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56922133521348756451844849 42691600141011567338883637)
                ·
                  refine ⟨4002337513219834438020341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42691600141011567338883637 4002337513219834438020341)
                  ·
                    refine ⟨375219141864359478564407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4002337513219834438020341 375219141864359478564407)
                    ·
                      rfl

theorem cell22_1096105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_1096105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096105 prefixEnd_1096105 := by exact prefixLift 1096105
  have htrace : WordTrace (prefixWord ++ tailWord_1096105) baseStart_1096105 baseEnd_1096105 := by
    simpa [prefixWord, tailWord_1096105, baseEnd_1096105] using wordTrace_append hprefix tailTrace_1096105
  have hstable : (prefixWord ++ tailWord_1096105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096105).length < 2 ^ (prefixWord ++ tailWord_1096105).sum := by decide
  have hdescent : baseEnd_1096105 < baseStart_1096105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096122 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_1096122 : Nat := 118140960795 + 1096122 * 2 ^ 59
def prefixEnd_1096122 : Nat := 4983230072969 + 3 ^ 40 * 1096122 * 2
def baseEnd_1096122 : Nat := 375224961311777100889355

theorem tailTrace_1096122 : CollatzResearch.WordTrace tailWord_1096122 prefixEnd_1096122 375224961311777100889355 := by
  unfold tailWord_1096122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9994713433736167894684655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26652569156629781052492413 9994713433736167894684655)
  ·
    refine ⟨14992070150604251842026983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9994713433736167894684655 14992070150604251842026983)
    ·
      refine ⟨22488105225906377763040475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14992070150604251842026983 22488105225906377763040475)
      ·
        refine ⟨33732157838859566644560713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22488105225906377763040475 33732157838859566644560713)
        ·
          refine ⟨25299118379144674983420535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33732157838859566644560713 25299118379144674983420535)
          ·
            refine ⟨37948677568717012475130803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25299118379144674983420535 37948677568717012475130803)
            ·
              refine ⟨56923016353075518712696205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37948677568717012475130803 56923016353075518712696205)
              ·
                refine ⟨21346131132403319517261077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56923016353075518712696205 21346131132403319517261077)
                ·
                  refine ⟨1000599896831405602371613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21346131132403319517261077 1000599896831405602371613)
                  ·
                    refine ⟨375224961311777100889355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000599896831405602371613 375224961311777100889355)
                    ·
                      rfl

theorem cell22_1096122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_1096122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096122 prefixEnd_1096122 := by exact prefixLift 1096122
  have htrace : WordTrace (prefixWord ++ tailWord_1096122) baseStart_1096122 baseEnd_1096122 := by
    simpa [prefixWord, tailWord_1096122, baseEnd_1096122] using wordTrace_append hprefix tailTrace_1096122
  have hstable : (prefixWord ++ tailWord_1096122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096122).length < 2 ^ (prefixWord ++ tailWord_1096122).sum := by decide
  have hdescent : baseEnd_1096122 < baseStart_1096122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096135 : List Nat := [1, 1, 4, 1, 1, 14]
def baseStart_1096135 : Nat := 118140960795 + 1096135 * 2 ^ 59
def prefixEnd_1096135 : Nat := 4983230072969 + 3 ^ 40 * 1096135 * 2
def baseEnd_1096135 : Nat := 4632461870091967905115

theorem tailTrace_1096135 : CollatzResearch.WordTrace tailWord_1096135 prefixEnd_1096135 4632461870091967905115 := by
  unfold tailWord_1096135
  simp only [CollatzResearch.WordTrace]
  refine ⟨39979327883897574798961859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26652885255931716532641239 39979327883897574798961859)
  ·
    refine ⟨59968991825846362198442789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39979327883897574798961859 59968991825846362198442789)
    ·
      refine ⟨11244185967346192912208023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59968991825846362198442789 11244185967346192912208023)
      ·
        refine ⟨16866278951019289368312035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11244185967346192912208023 16866278951019289368312035)
        ·
          refine ⟨25299418426528934052468053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16866278951019289368312035 25299418426528934052468053)
          ·
            refine ⟨4632461870091967905115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 25299418426528934052468053 4632461870091967905115)
            ·
              rfl

theorem cell22_1096135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 14].length) (baseStart_1096135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096135 prefixEnd_1096135 := by exact prefixLift 1096135
  have htrace : WordTrace (prefixWord ++ tailWord_1096135) baseStart_1096135 baseEnd_1096135 := by
    simpa [prefixWord, tailWord_1096135, baseEnd_1096135] using wordTrace_append hprefix tailTrace_1096135
  have hstable : (prefixWord ++ tailWord_1096135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096135).length < 2 ^ (prefixWord ++ tailWord_1096135).sum := by decide
  have hdescent : baseEnd_1096135 < baseStart_1096135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096137 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_1096137 : Nat := 118140960795 + 1096137 * 2 ^ 59
def prefixEnd_1096137 : Nat := 4983230072969 + 3 ^ 40 * 1096137 * 2
def baseEnd_1096137 : Nat := 375230096118322061764309

theorem tailTrace_1096137 : CollatzResearch.WordTrace tailWord_1096137 prefixEnd_1096137 375230096118322061764309 := by
  unfold tailWord_1096137
  simp only [CollatzResearch.WordTrace]
  refine ⟨39979400829890329140534665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26652933886593552760356443 39979400829890329140534665)
  ·
    refine ⟨29984550622417746855400999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39979400829890329140534665 29984550622417746855400999)
    ·
      refine ⟨44976825933626620283101499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29984550622417746855400999 44976825933626620283101499)
      ·
        refine ⟨67465238900439930424652249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44976825933626620283101499 67465238900439930424652249)
        ·
          refine ⟨50598929175329947818489187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67465238900439930424652249 50598929175329947818489187)
          ·
            refine ⟨75898393762994921727733781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50598929175329947818489187 75898393762994921727733781)
            ·
              refine ⟨3557737207640386955987521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75898393762994921727733781 3557737207640386955987521)
              ·
                refine ⟨2668302905730290216990641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3557737207640386955987521 2668302905730290216990641)
                ·
                  refine ⟨2001227179297717662742981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2668302905730290216990641 2001227179297717662742981)
                  ·
                    refine ⟨375230096118322061764309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2001227179297717662742981 375230096118322061764309)
                    ·
                      rfl

theorem cell22_1096137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_1096137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096137 prefixEnd_1096137 := by exact prefixLift 1096137
  have htrace : WordTrace (prefixWord ++ tailWord_1096137) baseStart_1096137 baseEnd_1096137 := by
    simpa [prefixWord, tailWord_1096137, baseEnd_1096137] using wordTrace_append hprefix tailTrace_1096137
  have hstable : (prefixWord ++ tailWord_1096137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096137).length < 2 ^ (prefixWord ++ tailWord_1096137).sum := by decide
  have hdescent : baseEnd_1096137 < baseStart_1096137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096242 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_1096242 : Nat := 118140960795 + 1096242 * 2 ^ 59
def prefixEnd_1096242 : Nat := 4983230072969 + 3 ^ 40 * 1096242 * 2
def baseEnd_1096242 : Nat := 125088679921378929296329

theorem tailTrace_1096242 : CollatzResearch.WordTrace tailWord_1096242 prefixEnd_1096242 125088679921378929296329 := by
  unfold tailWord_1096242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9995807623627483018276745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26655486996339954715404653 9995807623627483018276745)
  ·
    refine ⟨7496855717720612263707559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9995807623627483018276745 7496855717720612263707559)
    ·
      refine ⟨11245283576580918395561339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7496855717720612263707559 11245283576580918395561339)
      ·
        refine ⟨16867925364871377593342009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11245283576580918395561339 16867925364871377593342009)
        ·
          refine ⟨12650944023653533195006507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16867925364871377593342009 12650944023653533195006507)
          ·
            refine ⟨18976416035480299792509761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12650944023653533195006507 18976416035480299792509761)
            ·
              refine ⟨14232312026610224844382321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18976416035480299792509761 14232312026610224844382321)
              ·
                refine ⟨10674234019957668633286741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14232312026610224844382321 10674234019957668633286741)
                ·
                  refine ⟨125088679921378929296329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10674234019957668633286741 125088679921378929296329)
                  ·
                    rfl

theorem cell22_1096242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_1096242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096242 prefixEnd_1096242 := by exact prefixLift 1096242
  have htrace : WordTrace (prefixWord ++ tailWord_1096242) baseStart_1096242 baseEnd_1096242 := by
    simpa [prefixWord, tailWord_1096242, baseEnd_1096242] using wordTrace_append hprefix tailTrace_1096242
  have hstable : (prefixWord ++ tailWord_1096242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096242).length < 2 ^ (prefixWord ++ tailWord_1096242).sum := by decide
  have hdescent : baseEnd_1096242 < baseStart_1096242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096259 : List Nat := [1, 1, 1, 3, 1, 2, 1, 8, 4]
def baseStart_1096259 : Nat := 118140960795 + 1096259 * 2 ^ 59
def prefixEnd_1096259 : Nat := 4983230072969 + 3 ^ 40 * 1096259 * 2
def baseEnd_1096259 : Nat := 125090619737184803404645

theorem tailTrace_1096259 : CollatzResearch.WordTrace tailWord_1096259 prefixEnd_1096259 125090619737184803404645 := by
  unfold tailWord_1096259
  simp only [CollatzResearch.WordTrace]
  refine ⟨39983850535448343976475831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26655900356965562650983887 39983850535448343976475831)
  ·
    refine ⟨59975775803172515964713747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39983850535448343976475831 59975775803172515964713747)
    ·
      refine ⟨89963663704758773947070621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59975775803172515964713747 89963663704758773947070621)
      ·
        refine ⟨33736373889284540230151483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89963663704758773947070621 33736373889284540230151483)
        ·
          refine ⟨50604560833926810345227225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33736373889284540230151483 50604560833926810345227225)
          ·
            refine ⟨37953420625445107758920419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50604560833926810345227225 37953420625445107758920419)
            ·
              refine ⟨56930130938167661638380629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37953420625445107758920419 56930130938167661638380629)
              ·
                refine ⟨667149971931652284824773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 56930130938167661638380629 667149971931652284824773)
                ·
                  refine ⟨125090619737184803404645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667149971931652284824773 125090619737184803404645)
                  ·
                    rfl

theorem cell22_1096259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 4].length) (baseStart_1096259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096259 prefixEnd_1096259 := by exact prefixLift 1096259
  have htrace : WordTrace (prefixWord ++ tailWord_1096259) baseStart_1096259 baseEnd_1096259 := by
    simpa [prefixWord, tailWord_1096259, baseEnd_1096259] using wordTrace_append hprefix tailTrace_1096259
  have hstable : (prefixWord ++ tailWord_1096259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096259).length < 2 ^ (prefixWord ++ tailWord_1096259).sum := by decide
  have hdescent : baseEnd_1096259 < baseStart_1096259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096272 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_1096272 : Nat := 118140960795 + 1096272 * 2 ^ 59
def prefixEnd_1096272 : Nat := 4983230072969 + 3 ^ 40 * 1096272 * 2
def baseEnd_1096272 : Nat := 375276309377226709638895

theorem tailTrace_1096272 : CollatzResearch.WordTrace tailWord_1096272 prefixEnd_1096272 375276309377226709638895 := by
  unfold tailWord_1096272
  simp only [CollatzResearch.WordTrace]
  refine ⟨19992162342200623598349535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26656216456267498131132713 19992162342200623598349535)
  ·
    refine ⟨29988243513300935397524303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19992162342200623598349535 29988243513300935397524303)
    ·
      refine ⟨44982365269951403096286455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29988243513300935397524303 44982365269951403096286455)
      ·
        refine ⟨67473547904927104644429683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44982365269951403096286455 67473547904927104644429683)
        ·
          refine ⟨101210321857390656966644525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67473547904927104644429683 101210321857390656966644525)
          ·
            refine ⟨37953870696521496362491697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101210321857390656966644525 37953870696521496362491697)
            ·
              refine ⟨28465403022391122271868773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37953870696521496362491697 28465403022391122271868773)
              ·
                refine ⟨5337263066698335425975395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28465403022391122271868773 5337263066698335425975395)
                ·
                  refine ⟨8005894600047503138963093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5337263066698335425975395 8005894600047503138963093)
                  ·
                    refine ⟨375276309377226709638895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8005894600047503138963093 375276309377226709638895)
                    ·
                      rfl

theorem cell22_1096272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_1096272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096272 prefixEnd_1096272 := by exact prefixLift 1096272
  have htrace : WordTrace (prefixWord ++ tailWord_1096272) baseStart_1096272 baseEnd_1096272 := by
    simpa [prefixWord, tailWord_1096272, baseEnd_1096272] using wordTrace_append hprefix tailTrace_1096272
  have hstable : (prefixWord ++ tailWord_1096272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096272).length < 2 ^ (prefixWord ++ tailWord_1096272).sum := by decide
  have hdescent : baseEnd_1096272 < baseStart_1096272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096274 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1096274 : Nat := 118140960795 + 1096274 * 2 ^ 59
def prefixEnd_1096274 : Nat := 4983230072969 + 3 ^ 40 * 1096274 * 2
def baseEnd_1096274 : Nat := 375276994018099371088889

theorem tailTrace_1096274 : CollatzResearch.WordTrace tailWord_1096274 prefixEnd_1096274 375276994018099371088889 := by
  unfold tailWord_1096274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9996099407598500384567969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26656265086929334358847917 9996099407598500384567969)
  ·
    refine ⟨7497074555698875288425977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9996099407598500384567969 7497074555698875288425977)
    ·
      refine ⟨5622805916774156466319483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7497074555698875288425977 5622805916774156466319483)
      ·
        refine ⟨8434208875161234699479225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5622805916774156466319483 8434208875161234699479225)
        ·
          refine ⟨6325656656370926024609419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8434208875161234699479225 6325656656370926024609419)
          ·
            refine ⟨9488484984556389036914129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6325656656370926024609419 9488484984556389036914129)
            ·
              refine ⟨7116363738417291777685597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9488484984556389036914129 7116363738417291777685597)
              ·
                refine ⟨2668636401906484416632099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7116363738417291777685597 2668636401906484416632099)
                ·
                  refine ⟨4002954602859726624948149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668636401906484416632099 4002954602859726624948149)
                  ·
                    refine ⟨375276994018099371088889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4002954602859726624948149 375276994018099371088889)
                    ·
                      rfl

theorem cell22_1096274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1096274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096274 prefixEnd_1096274 := by exact prefixLift 1096274
  have htrace : WordTrace (prefixWord ++ tailWord_1096274) baseStart_1096274 baseEnd_1096274 := by
    simpa [prefixWord, tailWord_1096274, baseEnd_1096274] using wordTrace_append hprefix tailTrace_1096274
  have hstable : (prefixWord ++ tailWord_1096274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096274).length < 2 ^ (prefixWord ++ tailWord_1096274).sum := by decide
  have hdescent : baseEnd_1096274 < baseStart_1096274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096289 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1096289 : Nat := 118140960795 + 1096289 * 2 ^ 59
def prefixEnd_1096289 : Nat := 4983230072969 + 3 ^ 40 * 1096289 * 2
def baseEnd_1096289 : Nat := 375282128824644331963843

theorem tailTrace_1096289 : CollatzResearch.WordTrace tailWord_1096289 prefixEnd_1096289 375282128824644331963843 := by
  unfold tailWord_1096289
  simp only [CollatzResearch.WordTrace]
  refine ⟨39984944725339659100067921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26656629816893106066711947 39984944725339659100067921)
  ·
    refine ⟨29988708544004744325050941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39984944725339659100067921 29988708544004744325050941)
    ·
      refine ⟨11245765704001779121894103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29988708544004744325050941 11245765704001779121894103)
      ·
        refine ⟨16868648556002668682841155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11245765704001779121894103 16868648556002668682841155)
        ·
          refine ⟨25302972834004003024261733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16868648556002668682841155 25302972834004003024261733)
          ·
            refine ⟨4744307406375750567049075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25302972834004003024261733 4744307406375750567049075)
            ·
              refine ⟨7116461109563625850573613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4744307406375750567049075 7116461109563625850573613)
              ·
                refine ⟨2668672916086359693965105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7116461109563625850573613 2668672916086359693965105)
                ·
                  refine ⟨2001504687064769770473829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2668672916086359693965105 2001504687064769770473829)
                  ·
                    refine ⟨375282128824644331963843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2001504687064769770473829 375282128824644331963843)
                    ·
                      rfl

theorem cell22_1096289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1096289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096289 prefixEnd_1096289 := by exact prefixLift 1096289
  have htrace : WordTrace (prefixWord ++ tailWord_1096289) baseStart_1096289 baseEnd_1096289 := by
    simpa [prefixWord, tailWord_1096289, baseEnd_1096289] using wordTrace_append hprefix tailTrace_1096289
  have hstable : (prefixWord ++ tailWord_1096289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096289).length < 2 ^ (prefixWord ++ tailWord_1096289).sum := by decide
  have hdescent : baseEnd_1096289 < baseStart_1096289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096304 : List Nat := [2, 1, 1, 1, 8, 9]
def baseStart_1096304 : Nat := 118140960795 + 1096304 * 2 ^ 59
def prefixEnd_1096304 : Nat := 4983230072969 + 3 ^ 40 * 1096304 * 2
def baseEnd_1096304 : Nat := 4633176094212213491837

theorem tailTrace_1096304 : CollatzResearch.WordTrace tailWord_1096304 prefixEnd_1096304 4633176094212213491837 := by
  unfold tailWord_1096304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19992745910142658330931983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26656994546856877774575977 19992745910142658330931983)
  ·
    refine ⟨29989118865213987496397975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19992745910142658330931983 29989118865213987496397975)
    ·
      refine ⟨44983678297820981244596963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29989118865213987496397975 44983678297820981244596963)
      ·
        refine ⟨67475517446731471866895445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44983678297820981244596963 67475517446731471866895445)
        ·
          refine ⟨790728720078884435940181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 67475517446731471866895445 790728720078884435940181)
          ·
            refine ⟨4633176094212213491837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 790728720078884435940181 4633176094212213491837)
            ·
              rfl

theorem cell22_1096304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 9].length) (baseStart_1096304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096304 prefixEnd_1096304 := by exact prefixLift 1096304
  have htrace : WordTrace (prefixWord ++ tailWord_1096304) baseStart_1096304 baseEnd_1096304 := by
    simpa [prefixWord, tailWord_1096304, baseEnd_1096304] using wordTrace_append hprefix tailTrace_1096304
  have hstable : (prefixWord ++ tailWord_1096304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096304).length < 2 ^ (prefixWord ++ tailWord_1096304).sum := by decide
  have hdescent : baseEnd_1096304 < baseStart_1096304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096334 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1096334 : Nat := 118140960795 + 1096334 * 2 ^ 59
def prefixEnd_1096334 : Nat := 4983230072969 + 3 ^ 40 * 1096334 * 2
def baseEnd_1096334 : Nat := 375297533244279214588705

theorem tailTrace_1096334 : CollatzResearch.WordTrace tailWord_1096334 prefixEnd_1096334 375297533244279214588705 := by
  unfold tailWord_1096334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998323251272078973182007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26657724006784421190304037 4998323251272078973182007)
  ·
    refine ⟨7497484876908118459773011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4998323251272078973182007 7497484876908118459773011)
    ·
      refine ⟨11246227315362177689659517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7497484876908118459773011 11246227315362177689659517)
      ·
        refine ⟨4217335243260816633622319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11246227315362177689659517 4217335243260816633622319)
        ·
          refine ⟨6326002864891224950433479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4217335243260816633622319 6326002864891224950433479)
          ·
            refine ⟨9489004297336837425650219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6326002864891224950433479 9489004297336837425650219)
            ·
              refine ⟨14233506446005256138475329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9489004297336837425650219 14233506446005256138475329)
              ·
                refine ⟨10675129834503942103856497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14233506446005256138475329 10675129834503942103856497)
                ·
                  refine ⟨8006347375877956577892373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10675129834503942103856497 8006347375877956577892373)
                  ·
                    refine ⟨375297533244279214588705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8006347375877956577892373 375297533244279214588705)
                    ·
                      rfl

theorem cell22_1096334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1096334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096334 prefixEnd_1096334 := by exact prefixLift 1096334
  have htrace : WordTrace (prefixWord ++ tailWord_1096334) baseStart_1096334 baseEnd_1096334 := by
    simpa [prefixWord, tailWord_1096334, baseEnd_1096334] using wordTrace_append hprefix tailTrace_1096334
  have hstable : (prefixWord ++ tailWord_1096334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096334).length < 2 ^ (prefixWord ++ tailWord_1096334).sum := by decide
  have hdescent : baseEnd_1096334 < baseStart_1096334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096404 : List Nat := [2, 4, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1096404 : Nat := 118140960795 + 1096404 * 2 ^ 59
def prefixEnd_1096404 : Nat := 4983230072969 + 3 ^ 40 * 1096404 * 2
def baseEnd_1096404 : Nat := 375321495674822365338491

theorem tailTrace_1096404 : CollatzResearch.WordTrace tailWord_1096404 prefixEnd_1096404 375321495674822365338491 := by
  unfold tailWord_1096404
  simp only [CollatzResearch.WordTrace]
  refine ⟨19994569559961516870252133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26659426079948689160336177 19994569559961516870252133)
  ·
    refine ⟨3748981792492784413172275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19994569559961516870252133 3748981792492784413172275)
    ·
      refine ⟨5623472688739176619758413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3748981792492784413172275 5623472688739176619758413)
      ·
        refine ⟨2108802258277191232409405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5623472688739176619758413 2108802258277191232409405)
        ·
          refine ⟨790800846853946712153527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2108802258277191232409405 790800846853946712153527)
          ·
            refine ⟨1186201270280920068230291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790800846853946712153527 1186201270280920068230291)
            ·
              refine ⟨1779301905421380102345437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186201270280920068230291 1779301905421380102345437)
              ·
                refine ⟨667238214533017538379539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1779301905421380102345437 667238214533017538379539)
                ·
                  refine ⟨1000857321799526307569309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667238214533017538379539 1000857321799526307569309)
                  ·
                    refine ⟨375321495674822365338491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000857321799526307569309 375321495674822365338491)
                    ·
                      rfl

theorem cell22_1096404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1096404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096404 prefixEnd_1096404 := by exact prefixLift 1096404
  have htrace : WordTrace (prefixWord ++ tailWord_1096404) baseStart_1096404 baseEnd_1096404 := by
    simpa [prefixWord, tailWord_1096404, baseEnd_1096404] using wordTrace_append hprefix tailTrace_1096404
  have hstable : (prefixWord ++ tailWord_1096404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096404).length < 2 ^ (prefixWord ++ tailWord_1096404).sum := by decide
  have hdescent : baseEnd_1096404 < baseStart_1096404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096409 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_1096409 : Nat := 118140960795 + 1096409 * 2 ^ 59
def prefixEnd_1096409 : Nat := 4983230072969 + 3 ^ 40 * 1096409 * 2
def baseEnd_1096409 : Nat := 375323207277004018963475

theorem tailTrace_1096409 : CollatzResearch.WordTrace tailWord_1096409 prefixEnd_1096409 375323207277004018963475 := by
  unfold tailWord_1096409
  simp only [CollatzResearch.WordTrace]
  refine ⟨39989321484904919594436281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26659547656603279729624187 39989321484904919594436281)
  ·
    refine ⟨29991991113678689695827211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39989321484904919594436281 29991991113678689695827211)
    ·
      refine ⟨44987986670518034543740817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29991991113678689695827211 44987986670518034543740817)
      ·
        refine ⟨33740990002888525907805613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44987986670518034543740817 33740990002888525907805613)
        ·
          refine ⟨12652871251083197215427105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33740990002888525907805613 12652871251083197215427105)
          ·
            refine ⟨9489653438312397911570329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12652871251083197215427105 9489653438312397911570329)
            ·
              refine ⟨7117240078734298433677747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9489653438312397911570329 7117240078734298433677747)
              ·
                refine ⟨10675860118101447650516621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7117240078734298433677747 10675860118101447650516621)
                ·
                  refine ⟨4003447544288042868943733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10675860118101447650516621 4003447544288042868943733)
                  ·
                    refine ⟨375323207277004018963475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4003447544288042868943733 375323207277004018963475)
                    ·
                      rfl

theorem cell22_1096409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_1096409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096409 prefixEnd_1096409 := by exact prefixLift 1096409
  have htrace : WordTrace (prefixWord ++ tailWord_1096409) baseStart_1096409 baseEnd_1096409 := by
    simpa [prefixWord, tailWord_1096409, baseEnd_1096409] using wordTrace_append hprefix tailTrace_1096409
  have hstable : (prefixWord ++ tailWord_1096409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096409).length < 2 ^ (prefixWord ++ tailWord_1096409).sum := by decide
  have hdescent : baseEnd_1096409 < baseStart_1096409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096477 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1096477 : Nat := 118140960795 + 1096477 * 2 ^ 59
def prefixEnd_1096477 : Nat := 4983230072969 + 3 ^ 40 * 1096477 * 2
def baseEnd_1096477 : Nat := 375346485066674508263267

theorem tailTrace_1096477 : CollatzResearch.WordTrace tailWord_1096477 prefixEnd_1096477 375346485066674508263267 := by
  unfold tailWord_1096477
  simp only [CollatzResearch.WordTrace]
  refine ⟨39991801648658567207911685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26661201099105711471941123 39991801648658567207911685)
  ·
    refine ⟨7498462809123481351483441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39991801648658567207911685 7498462809123481351483441)
    ·
      refine ⟨5623847106842611013612581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7498462809123481351483441 5623847106842611013612581)
      ·
        refine ⟨1054471332532989565052359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5623847106842611013612581 1054471332532989565052359)
        ·
          refine ⟨1581706998799484347578539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054471332532989565052359 1581706998799484347578539)
          ·
            refine ⟨2372560498199226521367809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581706998799484347578539 2372560498199226521367809)
            ·
              refine ⟨1779420373649419891025857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2372560498199226521367809 1779420373649419891025857)
              ·
                refine ⟨1334565280237064918269393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779420373649419891025857 1334565280237064918269393)
                ·
                  refine ⟨1000923960177798688702045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1334565280237064918269393 1000923960177798688702045)
                  ·
                    refine ⟨375346485066674508263267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000923960177798688702045 375346485066674508263267)
                    ·
                      rfl

theorem cell22_1096477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1096477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096477 prefixEnd_1096477 := by exact prefixLift 1096477
  have htrace : WordTrace (prefixWord ++ tailWord_1096477) baseStart_1096477 baseEnd_1096477 := by
    simpa [prefixWord, tailWord_1096477, baseEnd_1096477] using wordTrace_append hprefix tailTrace_1096477
  have hstable : (prefixWord ++ tailWord_1096477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096477).length < 2 ^ (prefixWord ++ tailWord_1096477).sum := by decide
  have hdescent : baseEnd_1096477 < baseStart_1096477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096488 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1096488 : Nat := 118140960795 + 1096488 * 2 ^ 59
def prefixEnd_1096488 : Nat := 4983230072969 + 3 ^ 40 * 1096488 * 2
def baseEnd_1096488 : Nat := 375350250591474146238233

theorem tailTrace_1096488 : CollatzResearch.WordTrace tailWord_1096488 prefixEnd_1096488 375350250591474146238233 := by
  unfold tailWord_1096488
  simp only [CollatzResearch.WordTrace]
  refine ⟨19996101425809358043281059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26661468567745810724374745 19996101425809358043281059)
  ·
    refine ⟨29994152138714037064921589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19996101425809358043281059 29994152138714037064921589)
    ·
      refine ⟨2811951763004440974836399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29994152138714037064921589 2811951763004440974836399)
      ·
        refine ⟨4217927644506661462254599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811951763004440974836399 4217927644506661462254599)
        ·
          refine ⟨6326891466759992193381899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4217927644506661462254599 6326891466759992193381899)
          ·
            refine ⟨9490337200139988290072849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6326891466759992193381899 9490337200139988290072849)
            ·
              refine ⟨7117752900104991217554637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9490337200139988290072849 7117752900104991217554637)
              ·
                refine ⟨2669157337539371706582989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7117752900104991217554637 2669157337539371706582989)
                ·
                  refine ⟨1000934001577264389968621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2669157337539371706582989 1000934001577264389968621)
                  ·
                    refine ⟨375350250591474146238233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000934001577264389968621 375350250591474146238233)
                    ·
                      rfl

theorem cell22_1096488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1096488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096488 prefixEnd_1096488 := by exact prefixLift 1096488
  have htrace : WordTrace (prefixWord ++ tailWord_1096488) baseStart_1096488 baseEnd_1096488 := by
    simpa [prefixWord, tailWord_1096488, baseEnd_1096488] using wordTrace_append hprefix tailTrace_1096488
  have hstable : (prefixWord ++ tailWord_1096488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096488).length < 2 ^ (prefixWord ++ tailWord_1096488).sum := by decide
  have hdescent : baseEnd_1096488 < baseStart_1096488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096490 : List Nat := [3, 1, 4, 3, 1, 2, 1, 7]
def baseStart_1096490 : Nat := 118140960795 + 1096490 * 2 ^ 59
def prefixEnd_1096490 : Nat := 4983230072969 + 3 ^ 40 * 1096490 * 2
def baseEnd_1096490 : Nat := 41705659470260756409803

theorem tailTrace_1096490 : CollatzResearch.WordTrace tailWord_1096490 prefixEnd_1096490 41705659470260756409803 := by
  unfold tailWord_1096490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9998068949402867607033731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26661517198407646952089949 9998068949402867607033731)
  ·
    refine ⟨14997103424104301410550597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9998068949402867607033731 14997103424104301410550597)
    ·
      refine ⟨2811956892019556514478237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14997103424104301410550597 2811956892019556514478237)
      ·
        refine ⟨1054483834507333692929339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2811956892019556514478237 1054483834507333692929339)
        ·
          refine ⟨1581725751761000539394009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054483834507333692929339 1581725751761000539394009)
          ·
            refine ⟨1186294313820750404545507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581725751761000539394009 1186294313820750404545507)
            ·
              refine ⟨1779441470731125606818261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186294313820750404545507 1779441470731125606818261)
              ·
                refine ⟨41705659470260756409803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1779441470731125606818261 41705659470260756409803)
                ·
                  rfl

theorem cell22_1096490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_1096490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096490 prefixEnd_1096490 := by exact prefixLift 1096490
  have htrace : WordTrace (prefixWord ++ tailWord_1096490) baseStart_1096490 baseEnd_1096490 := by
    simpa [prefixWord, tailWord_1096490, baseEnd_1096490] using wordTrace_append hprefix tailTrace_1096490
  have hstable : (prefixWord ++ tailWord_1096490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096490).length < 2 ^ (prefixWord ++ tailWord_1096490).sum := by decide
  have hdescent : baseEnd_1096490 < baseStart_1096490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096565 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1096565 : Nat := 118140960795 + 1096565 * 2 ^ 59
def prefixEnd_1096565 : Nat := 4983230072969 + 3 ^ 40 * 1096565 * 2
def baseEnd_1096565 : Nat := 375376609265071612062997

theorem tailTrace_1096565 : CollatzResearch.WordTrace tailWord_1096565 prefixEnd_1096565 375376609265071612062997 := by
  unfold tailWord_1096565
  simp only [CollatzResearch.WordTrace]
  refine ⟨39995011272339758237115149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26663340848226505491410099 39995011272339758237115149)
  ·
    refine ⟨14998129227127409338918181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39995011272339758237115149 14998129227127409338918181)
    ·
      refine ⟨2812149230086389251047159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14998129227127409338918181 2812149230086389251047159)
      ·
        refine ⟨4218223845129583876570739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812149230086389251047159 4218223845129583876570739)
        ·
          refine ⟨6327335767694375814856109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4218223845129583876570739 6327335767694375814856109)
          ·
            refine ⟨2372750912885390930571041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6327335767694375814856109 2372750912885390930571041)
            ·
              refine ⟨1779563184664043197928281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2372750912885390930571041 1779563184664043197928281)
              ·
                refine ⟨1334672388498032398446211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779563184664043197928281 1334672388498032398446211)
                ·
                  refine ⟨2002008582747048597669317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334672388498032398446211 2002008582747048597669317)
                  ·
                    refine ⟨375376609265071612062997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002008582747048597669317 375376609265071612062997)
                    ·
                      rfl

theorem cell22_1096565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1096565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096565 prefixEnd_1096565 := by exact prefixLift 1096565
  have htrace : WordTrace (prefixWord ++ tailWord_1096565) baseStart_1096565 baseEnd_1096565 := by
    simpa [prefixWord, tailWord_1096565, baseEnd_1096565] using wordTrace_append hprefix tailTrace_1096565
  have hstable : (prefixWord ++ tailWord_1096565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096565).length < 2 ^ (prefixWord ++ tailWord_1096565).sum := by decide
  have hdescent : baseEnd_1096565 < baseStart_1096565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096700 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_1096700 : Nat := 118140960795 + 1096700 * 2 ^ 59
def prefixEnd_1096700 : Nat := 4983230072969 + 3 ^ 40 * 1096700 * 2
def baseEnd_1096700 : Nat := 375422822523976259937583

theorem tailTrace_1096700 : CollatzResearch.WordTrace tailWord_1096700 prefixEnd_1096700 375422822523976259937583 := by
  unfold tailWord_1096700
  simp only [CollatzResearch.WordTrace]
  refine ⟨19999967563425338146639777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26666623417900450862186369 19999967563425338146639777)
  ·
    refine ⟨14999975672569003609979833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19999967563425338146639777 14999975672569003609979833)
    ·
      refine ⟨11249981754426752707484875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14999975672569003609979833 11249981754426752707484875)
      ·
        refine ⟨16874972631640129061227313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11249981754426752707484875 16874972631640129061227313)
        ·
          refine ⟨12656229473730096795920485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16874972631640129061227313 12656229473730096795920485)
          ·
            refine ⟨2373043026324393149235091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12656229473730096795920485 2373043026324393149235091)
            ·
              refine ⟨3559564539486589723852637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373043026324393149235091 3559564539486589723852637)
              ·
                refine ⟨1334836702307471146444739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3559564539486589723852637 1334836702307471146444739)
                ·
                  refine ⟨2002255053461206719667109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334836702307471146444739 2002255053461206719667109)
                  ·
                    refine ⟨375422822523976259937583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002255053461206719667109 375422822523976259937583)
                    ·
                      rfl

theorem cell22_1096700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_1096700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096700 prefixEnd_1096700 := by exact prefixLift 1096700
  have htrace : WordTrace (prefixWord ++ tailWord_1096700) baseStart_1096700 baseEnd_1096700 := by
    simpa [prefixWord, tailWord_1096700, baseEnd_1096700] using wordTrace_append hprefix tailTrace_1096700
  have hstable : (prefixWord ++ tailWord_1096700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096700).length < 2 ^ (prefixWord ++ tailWord_1096700).sum := by decide
  have hdescent : baseEnd_1096700 < baseStart_1096700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096715 : List Nat := [1, 1, 1, 1, 6, 2, 2, 4, 4]
def baseStart_1096715 : Nat := 118140960795 + 1096715 * 2 ^ 59
def prefixEnd_1096715 : Nat := 4983230072969 + 3 ^ 40 * 1096715 * 2
def baseEnd_1096715 : Nat := 125142652443507073604179

theorem tailTrace_1096715 : CollatzResearch.WordTrace tailWord_1096715 prefixEnd_1096715 125142652443507073604179 := by
  unfold tailWord_1096715
  simp only [CollatzResearch.WordTrace]
  refine ⟨40000482221796333855075599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26666988147864222570050399 40000482221796333855075599)
  ·
    refine ⟨60000723332694500782613399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40000482221796333855075599 60000723332694500782613399)
    ·
      refine ⟨90001084999041751173920099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60000723332694500782613399 90001084999041751173920099)
      ·
        refine ⟨135001627498562626760880149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90001084999041751173920099 135001627498562626760880149)
        ·
          refine ⟨6328201288995123129416257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135001627498562626760880149 6328201288995123129416257)
          ·
            refine ⟨4746150966746342347062193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6328201288995123129416257 4746150966746342347062193)
            ·
              refine ⟨3559613225059756760296645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4746150966746342347062193 3559613225059756760296645)
              ·
                refine ⟨667427479698704392555621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3559613225059756760296645 667427479698704392555621)
                ·
                  refine ⟨125142652443507073604179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667427479698704392555621 125142652443507073604179)
                  ·
                    rfl

theorem cell22_1096715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 4].length) (baseStart_1096715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096715 prefixEnd_1096715 := by exact prefixLift 1096715
  have htrace : WordTrace (prefixWord ++ tailWord_1096715) baseStart_1096715 baseEnd_1096715 := by
    simpa [prefixWord, tailWord_1096715, baseEnd_1096715] using wordTrace_append hprefix tailTrace_1096715
  have hstable : (prefixWord ++ tailWord_1096715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096715).length < 2 ^ (prefixWord ++ tailWord_1096715).sum := by decide
  have hdescent : baseEnd_1096715 < baseStart_1096715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096728 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1096728 : Nat := 118140960795 + 1096728 * 2 ^ 59
def prefixEnd_1096728 : Nat := 4983230072969 + 3 ^ 40 * 1096728 * 2
def baseEnd_1096728 : Nat := 375432407496193520237497

theorem tailTrace_1096728 : CollatzResearch.WordTrace tailWord_1096728 prefixEnd_1096728 375432407496193520237497 := by
  unfold tailWord_1096728
  simp only [CollatzResearch.WordTrace]
  refine ⟨20000478185374618537649419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26667304247166158050199225 20000478185374618537649419)
  ·
    refine ⟨30000717278061927806474129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20000478185374618537649419 30000717278061927806474129)
    ·
      refine ⟨22500537958546445854855597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30000717278061927806474129 22500537958546445854855597)
      ·
        refine ⟨8437701734454917195570849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22500537958546445854855597 8437701734454917195570849)
        ·
          refine ⟨6328276300841187896678137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8437701734454917195570849 6328276300841187896678137)
          ·
            refine ⟨4746207225630890922508603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6328276300841187896678137 4746207225630890922508603)
            ·
              refine ⟨7119310838446336383762905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746207225630890922508603 7119310838446336383762905)
              ·
                refine ⟨5339483128834752287822179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7119310838446336383762905 5339483128834752287822179)
                ·
                  refine ⟨8009224693252128431733269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5339483128834752287822179 8009224693252128431733269)
                  ·
                    refine ⟨375432407496193520237497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8009224693252128431733269 375432407496193520237497)
                    ·
                      rfl

theorem cell22_1096728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1096728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096728 prefixEnd_1096728 := by exact prefixLift 1096728
  have htrace : WordTrace (prefixWord ++ tailWord_1096728) baseStart_1096728 baseEnd_1096728 := by
    simpa [prefixWord, tailWord_1096728, baseEnd_1096728] using wordTrace_append hprefix tailTrace_1096728
  have hstable : (prefixWord ++ tailWord_1096728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096728).length < 2 ^ (prefixWord ++ tailWord_1096728).sum := by decide
  have hdescent : baseEnd_1096728 < baseStart_1096728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096781 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1096781 : Nat := 118140960795 + 1096781 * 2 ^ 59
def prefixEnd_1096781 : Nat := 4983230072969 + 3 ^ 40 * 1096781 * 2
def baseEnd_1096781 : Nat := 375450550479319048662335

theorem tailTrace_1096781 : CollatzResearch.WordTrace tailWord_1096781 prefixEnd_1096781 375450550479319048662335 := by
  unfold tailWord_1096781
  simp only [CollatzResearch.WordTrace]
  refine ⟨40002889439557227126978197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26668592959704818084652131 40002889439557227126978197)
  ·
    refine ⟨1875135442479245021577103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40002889439557227126978197 1875135442479245021577103)
    ·
      refine ⟨2812703163718867532365655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875135442479245021577103 2812703163718867532365655)
      ·
        refine ⟨4219054745578301298548483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812703163718867532365655 4219054745578301298548483)
        ·
          refine ⟨6328582118367451947822725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219054745578301298548483 6328582118367451947822725)
          ·
            refine ⟨1186609147193897240216761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6328582118367451947822725 1186609147193897240216761)
            ·
              refine ⟨889956860395422930162571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186609147193897240216761 889956860395422930162571)
              ·
                refine ⟨1334935290593134395243857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889956860395422930162571 1334935290593134395243857)
                ·
                  refine ⟨1001201467944850796432893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1334935290593134395243857 1001201467944850796432893)
                  ·
                    refine ⟨375450550479319048662335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1001201467944850796432893 375450550479319048662335)
                    ·
                      rfl

theorem cell22_1096781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1096781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096781 prefixEnd_1096781 := by exact prefixLift 1096781
  have htrace : WordTrace (prefixWord ++ tailWord_1096781) baseStart_1096781 baseEnd_1096781 := by
    simpa [prefixWord, tailWord_1096781, baseEnd_1096781] using wordTrace_append hprefix tailTrace_1096781
  have hstable : (prefixWord ++ tailWord_1096781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096781).length < 2 ^ (prefixWord ++ tailWord_1096781).sum := by decide
  have hdescent : baseEnd_1096781 < baseStart_1096781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096803 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 4, 5]
def baseStart_1096803 : Nat := 118140960795 + 1096803 * 2 ^ 59
def prefixEnd_1096803 : Nat := 4983230072969 + 3 ^ 40 * 1096803 * 2
def baseEnd_1096803 : Nat := 375458081528918324612267

theorem tailTrace_1096803 : CollatzResearch.WordTrace tailWord_1096803 prefixEnd_1096803 375458081528918324612267 := by
  unfold tailWord_1096803
  simp only [CollatzResearch.WordTrace]
  refine ⟨40003691845477524884279063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26669127896985016589519375 40003691845477524884279063)
  ·
    refine ⟨60005537768216287326418595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40003691845477524884279063 60005537768216287326418595)
    ·
      refine ⟨90008306652324430989627893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60005537768216287326418595 90008306652324430989627893)
      ·
        refine ⟨8438278748655415405277615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90008306652324430989627893 8438278748655415405277615)
        ·
          refine ⟨12657418122983123107916423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8438278748655415405277615 12657418122983123107916423)
          ·
            refine ⟨18986127184474684661874635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12657418122983123107916423 18986127184474684661874635)
            ·
              refine ⟨28479190776712026992811953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18986127184474684661874635 28479190776712026992811953)
              ·
                refine ⟨21359393082534020244608965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28479190776712026992811953 21359393082534020244608965)
                ·
                  refine ⟨4004886202975128795864181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21359393082534020244608965 4004886202975128795864181)
                  ·
                    refine ⟨375458081528918324612267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4004886202975128795864181 375458081528918324612267)
                    ·
                      rfl

theorem cell22_1096803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_1096803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096803 prefixEnd_1096803 := by exact prefixLift 1096803
  have htrace : WordTrace (prefixWord ++ tailWord_1096803) baseStart_1096803 baseEnd_1096803 := by
    simpa [prefixWord, tailWord_1096803, baseEnd_1096803] using wordTrace_append hprefix tailTrace_1096803
  have hstable : (prefixWord ++ tailWord_1096803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096803).length < 2 ^ (prefixWord ++ tailWord_1096803).sum := by decide
  have hdescent : baseEnd_1096803 < baseStart_1096803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096822 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1096822 : Nat := 118140960795 + 1096822 * 2 ^ 59
def prefixEnd_1096822 : Nat := 4983230072969 + 3 ^ 40 * 1096822 * 2
def baseEnd_1096822 : Nat := 125154861872402869462403

theorem tailTrace_1096822 : CollatzResearch.WordTrace tailWord_1096822 prefixEnd_1096822 125154861872402869462403 := by
  unfold tailWord_1096822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500274052025543195576295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26669589888272460752813813 2500274052025543195576295)
  ·
    refine ⟨3750411078038314793364443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2500274052025543195576295 3750411078038314793364443)
    ·
      refine ⟨5625616617057472190046665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750411078038314793364443 5625616617057472190046665)
      ·
        refine ⟨4219212462793104142534999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5625616617057472190046665 4219212462793104142534999)
        ·
          refine ⟨6328818694189656213802499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219212462793104142534999 6328818694189656213802499)
          ·
            refine ⟨9493228041284484320703749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328818694189656213802499 9493228041284484320703749)
            ·
              refine ⟨1779980257740840810131953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9493228041284484320703749 1779980257740840810131953)
              ·
                refine ⟨1334985193305630607598965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779980257740840810131953 1334985193305630607598965)
                ·
                  refine ⟨125154861872402869462403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1334985193305630607598965 125154861872402869462403)
                  ·
                    rfl

theorem cell22_1096822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1096822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096822 prefixEnd_1096822 := by exact prefixLift 1096822
  have htrace : WordTrace (prefixWord ++ tailWord_1096822) baseStart_1096822 baseEnd_1096822 := by
    simpa [prefixWord, tailWord_1096822, baseEnd_1096822] using wordTrace_append hprefix tailTrace_1096822
  have hstable : (prefixWord ++ tailWord_1096822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096822).length < 2 ^ (prefixWord ++ tailWord_1096822).sum := by decide
  have hdescent : baseEnd_1096822 < baseStart_1096822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096850 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1096850 : Nat := 118140960795 + 1096850 * 2 ^ 59
def prefixEnd_1096850 : Nat := 4983230072969 + 3 ^ 40 * 1096850 * 2
def baseEnd_1096850 : Nat := 125158056863141956229041

theorem tailTrace_1096850 : CollatzResearch.WordTrace tailWord_1096850 prefixEnd_1096850 125158056863141956229041 := by
  unfold tailWord_1096850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10001351519076812977810001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26670270717538167940826669 10001351519076812977810001)
  ·
    refine ⟨7501013639307609733357501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10001351519076812977810001 7501013639307609733357501)
    ·
      refine ⟨2812880114740353650009063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7501013639307609733357501 2812880114740353650009063)
      ·
        refine ⟨4219320172110530475013595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812880114740353650009063 4219320172110530475013595)
        ·
          refine ⟨6328980258165795712520393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219320172110530475013595 6328980258165795712520393)
          ·
            refine ⟨4746735193624346784390295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6328980258165795712520393 4746735193624346784390295)
            ·
              refine ⟨7120102790436520176585443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746735193624346784390295 7120102790436520176585443)
              ·
                refine ⟨10680154185654780264878165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7120102790436520176585443 10680154185654780264878165)
                ·
                  refine ⟨125158056863141956229041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10680154185654780264878165 125158056863141956229041)
                  ·
                    rfl

theorem cell22_1096850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1096850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096850 prefixEnd_1096850 := by exact prefixLift 1096850
  have htrace : WordTrace (prefixWord ++ tailWord_1096850) baseStart_1096850 baseEnd_1096850 := by
    simpa [prefixWord, tailWord_1096850, baseEnd_1096850] using wordTrace_append hprefix tailTrace_1096850
  have hstable : (prefixWord ++ tailWord_1096850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096850).length < 2 ^ (prefixWord ++ tailWord_1096850).sum := by decide
  have hdescent : baseEnd_1096850 < baseStart_1096850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096865 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1096865 : Nat := 118140960795 + 1096865 * 2 ^ 59
def prefixEnd_1096865 : Nat := 4983230072969 + 3 ^ 40 * 1096865 * 2
def baseEnd_1096865 : Nat := 375479305395970829562077

theorem tailTrace_1096865 : CollatzResearch.WordTrace tailWord_1096865 prefixEnd_1096865 375479305395970829562077 := by
  unfold tailWord_1096865
  simp only [CollatzResearch.WordTrace]
  refine ⟨40005953171252909473036049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26670635447501939648690699 40005953171252909473036049)
  ·
    refine ⟨30004464878439682104777037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40005953171252909473036049 30004464878439682104777037)
    ·
      refine ⟨11251674329414880789291389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30004464878439682104777037 11251674329414880789291389)
      ·
        refine ⟨4219377873530580295984271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11251674329414880789291389 4219377873530580295984271)
        ·
          refine ⟨6329066810295870443976407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219377873530580295984271 6329066810295870443976407)
          ·
            refine ⟨9493600215443805665964611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6329066810295870443976407 9493600215443805665964611)
            ·
              refine ⟨14240400323165708498946917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9493600215443805665964611 14240400323165708498946917)
              ·
                refine ⟨2670075060593570343552547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14240400323165708498946917 2670075060593570343552547)
                ·
                  refine ⟨4005112590890355515328821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670075060593570343552547 4005112590890355515328821)
                  ·
                    refine ⟨375479305395970829562077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4005112590890355515328821 375479305395970829562077)
                    ·
                      rfl

theorem cell22_1096865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1096865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096865 prefixEnd_1096865 := by exact prefixLift 1096865
  have htrace : WordTrace (prefixWord ++ tailWord_1096865) baseStart_1096865 baseEnd_1096865 := by
    simpa [prefixWord, tailWord_1096865, baseEnd_1096865] using wordTrace_append hprefix tailTrace_1096865
  have hstable : (prefixWord ++ tailWord_1096865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096865).length < 2 ^ (prefixWord ++ tailWord_1096865).sum := by decide
  have hdescent : baseEnd_1096865 < baseStart_1096865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096869 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_1096869 : Nat := 118140960795 + 1096869 * 2 ^ 59
def prefixEnd_1096869 : Nat := 4983230072969 + 3 ^ 40 * 1096869 * 2
def baseEnd_1096869 : Nat := 375480674677716152462065

theorem tailTrace_1096869 : CollatzResearch.WordTrace tailWord_1096869 prefixEnd_1096869 375480674677716152462065 := by
  unfold tailWord_1096869
  simp only [CollatzResearch.WordTrace]
  refine ⟨40006099063238418156181661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26670732708825612104121107 40006099063238418156181661)
  ·
    refine ⟨15002287148714406808568123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40006099063238418156181661 15002287148714406808568123)
    ·
      refine ⟨22503430723071610212852185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15002287148714406808568123 22503430723071610212852185)
      ·
        refine ⟨16877573042303707659639139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22503430723071610212852185 16877573042303707659639139)
        ·
          refine ⟨25316359563455561489458709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16877573042303707659639139 25316359563455561489458709)
          ·
            refine ⟨1186704354536979444818377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25316359563455561489458709 1186704354536979444818377)
            ·
              refine ⟨890028265902734583613783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186704354536979444818377 890028265902734583613783)
              ·
                refine ⟨1335042398854101875420675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890028265902734583613783 1335042398854101875420675)
                ·
                  refine ⟨2002563598281152813131013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335042398854101875420675 2002563598281152813131013)
                  ·
                    refine ⟨375480674677716152462065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002563598281152813131013 375480674677716152462065)
                    ·
                      rfl

theorem cell22_1096869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_1096869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096869 prefixEnd_1096869 := by exact prefixLift 1096869
  have htrace : WordTrace (prefixWord ++ tailWord_1096869) baseStart_1096869 baseEnd_1096869 := by
    simpa [prefixWord, tailWord_1096869, baseEnd_1096869] using wordTrace_append hprefix tailTrace_1096869
  have hstable : (prefixWord ++ tailWord_1096869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096869).length < 2 ^ (prefixWord ++ tailWord_1096869).sum := by decide
  have hdescent : baseEnd_1096869 < baseStart_1096869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096882 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_1096882 : Nat := 118140960795 + 1096882 * 2 ^ 59
def prefixEnd_1096882 : Nat := 4983230072969 + 3 ^ 40 * 1096882 * 2
def baseEnd_1096882 : Nat := 375485124843388451887025

theorem tailTrace_1096882 : CollatzResearch.WordTrace tailWord_1096882 prefixEnd_1096882 375485124843388451887025 := by
  unfold tailWord_1096882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10001643303047830344101225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26671048808127547584269933 10001643303047830344101225)
  ·
    refine ⟨7501232477285872758075919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10001643303047830344101225 7501232477285872758075919)
    ·
      refine ⟨11251848715928809137113879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7501232477285872758075919 11251848715928809137113879)
      ·
        refine ⟨16877773073893213705670819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11251848715928809137113879 16877773073893213705670819)
        ·
          refine ⟨25316659610839820558506229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16877773073893213705670819 25316659610839820558506229)
          ·
            refine ⟨2373436838516233177359959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25316659610839820558506229 2373436838516233177359959)
            ·
              refine ⟨3560155257774349766039939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373436838516233177359959 3560155257774349766039939)
              ·
                refine ⟨5340232886661524649059909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560155257774349766039939 5340232886661524649059909)
                ·
                  refine ⟨1001293666249035871698733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5340232886661524649059909 1001293666249035871698733)
                  ·
                    refine ⟨375485124843388451887025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1001293666249035871698733 375485124843388451887025)
                    ·
                      rfl

theorem cell22_1096882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_1096882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096882 prefixEnd_1096882 := by exact prefixLift 1096882
  have htrace : WordTrace (prefixWord ++ tailWord_1096882) baseStart_1096882 baseEnd_1096882 := by
    simpa [prefixWord, tailWord_1096882, baseEnd_1096882] using wordTrace_append hprefix tailTrace_1096882
  have hstable : (prefixWord ++ tailWord_1096882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096882).length < 2 ^ (prefixWord ++ tailWord_1096882).sum := by decide
  have hdescent : baseEnd_1096882 < baseStart_1096882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096897 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1096897 : Nat := 118140960795 + 1096897 * 2 ^ 59
def prefixEnd_1096897 : Nat := 4983230072969 + 3 ^ 40 * 1096897 * 2
def baseEnd_1096897 : Nat := 375490259649933412761979

theorem tailTrace_1096897 : CollatzResearch.WordTrace tailWord_1096897 prefixEnd_1096897 375490259649933412761979 := by
  unfold tailWord_1096897
  simp only [CollatzResearch.WordTrace]
  refine ⟨40007120307136978938200945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26671413538091319292133963 40007120307136978938200945)
  ·
    refine ⟨30005340230352734203650709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40007120307136978938200945 30005340230352734203650709)
    ·
      refine ⟨1406500323297784415796127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30005340230352734203650709 1406500323297784415796127)
      ·
        refine ⟨2109750484946676623694191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406500323297784415796127 2109750484946676623694191)
        ·
          refine ⟨3164625727420014935541287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109750484946676623694191 3164625727420014935541287)
          ·
            refine ⟨4746938591130022403311931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164625727420014935541287 4746938591130022403311931)
            ·
              refine ⟨7120407886695033604967897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746938591130022403311931 7120407886695033604967897)
              ·
                refine ⟨5340305915021275203725923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7120407886695033604967897 5340305915021275203725923)
                ·
                  refine ⟨8010458872531912805588885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340305915021275203725923 8010458872531912805588885)
                  ·
                    refine ⟨375490259649933412761979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8010458872531912805588885 375490259649933412761979)
                    ·
                      rfl

theorem cell22_1096897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1096897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096897 prefixEnd_1096897 := by exact prefixLift 1096897
  have htrace : WordTrace (prefixWord ++ tailWord_1096897) baseStart_1096897 baseEnd_1096897 := by
    simpa [prefixWord, tailWord_1096897, baseEnd_1096897] using wordTrace_append hprefix tailTrace_1096897
  have hstable : (prefixWord ++ tailWord_1096897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096897).length < 2 ^ (prefixWord ++ tailWord_1096897).sum := by decide
  have hdescent : baseEnd_1096897 < baseStart_1096897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096918 : List Nat := [5, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1096918 : Nat := 118140960795 + 1096918 * 2 ^ 59
def prefixEnd_1096918 : Nat := 4983230072969 + 3 ^ 40 * 1096918 * 2
def baseEnd_1096918 : Nat := 125165816126365452662305

theorem tailTrace_1096918 : CollatzResearch.WordTrace tailWord_1096918 prefixEnd_1096918 125165816126365452662305 := by
  unfold tailWord_1096918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500492890003806220294713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26671924160040599683143605 2500492890003806220294713)
  ·
    refine ⟨1875369667502854665221035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2500492890003806220294713 1875369667502854665221035)
    ·
      refine ⟨2813054501254281997831553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875369667502854665221035 2813054501254281997831553)
      ·
        refine ⟨2109790875940711498373665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2813054501254281997831553 2109790875940711498373665)
        ·
          refine ⟨1582343156955533623780249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2109790875940711498373665 1582343156955533623780249)
          ·
            refine ⟨1186757367716650217835187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1582343156955533623780249 1186757367716650217835187)
            ·
              refine ⟨1780136051574975326752781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186757367716650217835187 1780136051574975326752781)
              ·
                refine ⟨667551019340615747532293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1780136051574975326752781 667551019340615747532293)
                ·
                  refine ⟨125165816126365452662305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667551019340615747532293 125165816126365452662305)
                  ·
                    rfl

theorem cell22_1096918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1096918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096918 prefixEnd_1096918 := by exact prefixLift 1096918
  have htrace : WordTrace (prefixWord ++ tailWord_1096918) baseStart_1096918 baseEnd_1096918 := by
    simpa [prefixWord, tailWord_1096918, baseEnd_1096918] using wordTrace_append hprefix tailTrace_1096918
  have hstable : (prefixWord ++ tailWord_1096918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096918).length < 2 ^ (prefixWord ++ tailWord_1096918).sum := by decide
  have hdescent : baseEnd_1096918 < baseStart_1096918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096940 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 7]
def baseStart_1096940 : Nat := 118140960795 + 1096940 * 2 ^ 59
def prefixEnd_1096940 : Nat := 4983230072969 + 3 ^ 40 * 1096940 * 2
def baseEnd_1096940 : Nat := 125168326476231877978949

theorem tailTrace_1096940 : CollatzResearch.WordTrace tailWord_1096940 prefixEnd_1096940 125168326476231877978949 := by
  unfold tailWord_1096940
  simp only [CollatzResearch.WordTrace]
  refine ⟨20004344322990598641008137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26672459097320798188010849 20004344322990598641008137)
  ·
    refine ⟨15003258242242948980756103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20004344322990598641008137 15003258242242948980756103)
    ·
      refine ⟨22504887363364423471134155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15003258242242948980756103 22504887363364423471134155)
      ·
        refine ⟨33757331045046635206701233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22504887363364423471134155 33757331045046635206701233)
        ·
          refine ⟨25317998283784976405025925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33757331045046635206701233 25317998283784976405025925)
          ·
            refine ⟨4747124678209683075942361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25317998283784976405025925 4747124678209683075942361)
            ·
              refine ⟨3560343508657262306956771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4747124678209683075942361 3560343508657262306956771)
              ·
                refine ⟨5340515262985893460435157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560343508657262306956771 5340515262985893460435157)
                ·
                  refine ⟨125168326476231877978949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5340515262985893460435157 125168326476231877978949)
                  ·
                    rfl

theorem cell22_1096940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_1096940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1096940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1096940 prefixEnd_1096940 := by exact prefixLift 1096940
  have htrace : WordTrace (prefixWord ++ tailWord_1096940) baseStart_1096940 baseEnd_1096940 := by
    simpa [prefixWord, tailWord_1096940, baseEnd_1096940] using wordTrace_append hprefix tailTrace_1096940
  have hstable : (prefixWord ++ tailWord_1096940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096940).length < 2 ^ (prefixWord ++ tailWord_1096940).sum := by decide
  have hdescent : baseEnd_1096940 < baseStart_1096940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097053 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1097053 : Nat := 118140960795 + 1097053 * 2 ^ 59
def prefixEnd_1097053 : Nat := 4983230072969 + 3 ^ 40 * 1097053 * 2
def baseEnd_1097053 : Nat := 125181220546000335287167

theorem tailTrace_1097053 : CollatzResearch.WordTrace tailWord_1097053 prefixEnd_1097053 125181220546000335287167 := by
  unfold tailWord_1097053
  simp only [CollatzResearch.WordTrace]
  refine ⟨40012810094571817580879813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26675206729714545053919875 40012810094571817580879813)
  ·
    refine ⟨7502401892732215796414965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40012810094571817580879813 7502401892732215796414965)
    ·
      refine ⟨703350177443645230913903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7502401892732215796414965 703350177443645230913903)
      ·
        refine ⟨1055025266165467846370855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703350177443645230913903 1055025266165467846370855)
        ·
          refine ⟨1582537899248201769556283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055025266165467846370855 1582537899248201769556283)
          ·
            refine ⟨2373806848872302654334425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582537899248201769556283 2373806848872302654334425)
            ·
              refine ⟨1780355136654226990750819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373806848872302654334425 1780355136654226990750819)
              ·
                refine ⟨2670532704981340486126229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780355136654226990750819 2670532704981340486126229)
                ·
                  refine ⟨125181220546000335287167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2670532704981340486126229 125181220546000335287167)
                  ·
                    rfl

theorem cell22_1097053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1097053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097053 prefixEnd_1097053 := by exact prefixLift 1097053
  have htrace : WordTrace (prefixWord ++ tailWord_1097053) baseStart_1097053 baseEnd_1097053 := by
    simpa [prefixWord, tailWord_1097053, baseEnd_1097053] using wordTrace_append hprefix tailTrace_1097053
  have hstable : (prefixWord ++ tailWord_1097053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097053).length < 2 ^ (prefixWord ++ tailWord_1097053).sum := by decide
  have hdescent : baseEnd_1097053 < baseStart_1097053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097075 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 11]
def baseStart_1097075 : Nat := 118140960795 + 1097075 * 2 ^ 59
def prefixEnd_1097075 : Nat := 4983230072969 + 3 ^ 40 * 1097075 * 2
def baseEnd_1097075 : Nat := 125183730895866760603811

theorem tailTrace_1097075 : CollatzResearch.WordTrace tailWord_1097075 prefixEnd_1097075 125183730895866760603811 := by
  unfold tailWord_1097075
  simp only [CollatzResearch.WordTrace]
  refine ⟨40013612500492115338180679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26675741666994743558787119 40013612500492115338180679)
  ·
    refine ⟨60020418750738173007271019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40013612500492115338180679 60020418750738173007271019)
    ·
      refine ⟨90030628126107259510906529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60020418750738173007271019 90030628126107259510906529)
      ·
        refine ⟨67522971094580444633179897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90030628126107259510906529 67522971094580444633179897)
        ·
          refine ⟨50642228320935333474884923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67522971094580444633179897 50642228320935333474884923)
          ·
            refine ⟨75963342481403000212327385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50642228320935333474884923 75963342481403000212327385)
            ·
              refine ⟨56972506861052250159245539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75963342481403000212327385 56972506861052250159245539)
              ·
                refine ⟨85458760291578375238868309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56972506861052250159245539 85458760291578375238868309)
                ·
                  refine ⟨125183730895866760603811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 85458760291578375238868309 125183730895866760603811)
                  ·
                    rfl

theorem cell22_1097075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_1097075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097075 prefixEnd_1097075 := by exact prefixLift 1097075
  have htrace : WordTrace (prefixWord ++ tailWord_1097075) baseStart_1097075 baseEnd_1097075 := by
    simpa [prefixWord, tailWord_1097075, baseEnd_1097075] using wordTrace_append hprefix tailTrace_1097075
  have hstable : (prefixWord ++ tailWord_1097075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097075).length < 2 ^ (prefixWord ++ tailWord_1097075).sum := by decide
  have hdescent : baseEnd_1097075 < baseStart_1097075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097092 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1097092 : Nat := 118140960795 + 1097092 * 2 ^ 59
def prefixEnd_1097092 : Nat := 4983230072969 + 3 ^ 40 * 1097092 * 2
def baseEnd_1097092 : Nat := 125185670711672634712127

theorem tailTrace_1097092 : CollatzResearch.WordTrace tailWord_1097092 prefixEnd_1097092 125185670711672634712127 := by
  unfold tailWord_1097092
  simp only [CollatzResearch.WordTrace]
  refine ⟨20007116270715263620774765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26676155027620351494366353 20007116270715263620774765)
  ·
    refine ⟨7502668601518223857790537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20007116270715263620774765 7502668601518223857790537)
    ·
      refine ⟨5627001451138667893342903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7502668601518223857790537 5627001451138667893342903)
      ·
        refine ⟨8440502176708001840014355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5627001451138667893342903 8440502176708001840014355)
        ·
          refine ⟨12660753265062002760021533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8440502176708001840014355 12660753265062002760021533)
          ·
            refine ⟨4747782474398251035008075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12660753265062002760021533 4747782474398251035008075)
            ·
              refine ⟨7121673711597376552512113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747782474398251035008075 7121673711597376552512113)
              ·
                refine ⟨5341255283698032414384085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7121673711597376552512113 5341255283698032414384085)
                ·
                  refine ⟨125185670711672634712127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5341255283698032414384085 125185670711672634712127)
                  ·
                    rfl

theorem cell22_1097092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1097092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097092 prefixEnd_1097092 := by exact prefixLift 1097092
  have htrace : WordTrace (prefixWord ++ tailWord_1097092) baseStart_1097092 baseEnd_1097092 := by
    simpa [prefixWord, tailWord_1097092, baseEnd_1097092] using wordTrace_append hprefix tailTrace_1097092
  have hstable : (prefixWord ++ tailWord_1097092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097092).length < 2 ^ (prefixWord ++ tailWord_1097092).sum := by decide
  have hdescent : baseEnd_1097092 < baseStart_1097092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097113 : List Nat := [1, 2, 1, 2, 1, 6, 3, 2, 1, 3]
def baseStart_1097113 : Nat := 118140960795 + 1097113 * 2 ^ 59
def prefixEnd_1097113 : Nat := 4983230072969 + 3 ^ 40 * 1097113 * 2
def baseEnd_1097113 : Nat := 375564200864180849361317

theorem tailTrace_1097113 : CollatzResearch.WordTrace tailWord_1097113 prefixEnd_1097113 375564200864180849361317 := by
  unfold tailWord_1097113
  simp only [CollatzResearch.WordTrace]
  refine ⟨40014998474354447828063993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26676665649569631885375995 40014998474354447828063993)
  ·
    refine ⟨30011248855765835871047995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40014998474354447828063993 30011248855765835871047995)
    ·
      refine ⟨45016873283648753806571993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30011248855765835871047995 45016873283648753806571993)
      ·
        refine ⟨33762654962736565354928995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45016873283648753806571993 33762654962736565354928995)
        ·
          refine ⟨50643982444104848032393493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33762654962736565354928995 50643982444104848032393493)
          ·
            refine ⟨2373936677067414751518445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50643982444104848032393493 2373936677067414751518445)
            ·
              refine ⟨890226253900280531819417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2373936677067414751518445 890226253900280531819417)
              ·
                refine ⟨667669690425210398864563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890226253900280531819417 667669690425210398864563)
                ·
                  refine ⟨1001504535637815598296845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667669690425210398864563 1001504535637815598296845)
                  ·
                    refine ⟨375564200864180849361317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1001504535637815598296845 375564200864180849361317)
                    ·
                      rfl

theorem cell22_1097113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 3].length) (baseStart_1097113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097113 prefixEnd_1097113 := by exact prefixLift 1097113
  have htrace : WordTrace (prefixWord ++ tailWord_1097113) baseStart_1097113 baseEnd_1097113 := by
    simpa [prefixWord, tailWord_1097113, baseEnd_1097113] using wordTrace_append hprefix tailTrace_1097113
  have hstable : (prefixWord ++ tailWord_1097113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097113).length < 2 ^ (prefixWord ++ tailWord_1097113).sum := by decide
  have hdescent : baseEnd_1097113 < baseStart_1097113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097137 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 8]
def baseStart_1097137 : Nat := 118140960795 + 1097137 * 2 ^ 59
def prefixEnd_1097137 : Nat := 4983230072969 + 3 ^ 40 * 1097137 * 2
def baseEnd_1097137 : Nat := 125190805518217595587081

theorem tailTrace_1097137 : CollatzResearch.WordTrace tailWord_1097137 prefixEnd_1097137 125190805518217595587081 := by
  unfold tailWord_1097137
  simp only [CollatzResearch.WordTrace]
  refine ⟨40015873826267499926937665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26677249217511666617958443 40015873826267499926937665)
  ·
    refine ⟨30011905369700624945203249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40015873826267499926937665 30011905369700624945203249)
    ·
      refine ⟨22508929027275468708902437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30011905369700624945203249 22508929027275468708902437)
      ·
        refine ⟨4220424192614150382919207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22508929027275468708902437 4220424192614150382919207)
        ·
          refine ⟨6330636288921225574378811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220424192614150382919207 6330636288921225574378811)
          ·
            refine ⟨9495954433381838361568217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330636288921225574378811 9495954433381838361568217)
            ·
              refine ⟨7121965825036378771176163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9495954433381838361568217 7121965825036378771176163)
              ·
                refine ⟨10682948737554568156764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7121965825036378771176163 10682948737554568156764245)
                ·
                  refine ⟨125190805518217595587081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10682948737554568156764245 125190805518217595587081)
                  ·
                    rfl

theorem cell22_1097137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_1097137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097137 prefixEnd_1097137 := by exact prefixLift 1097137
  have htrace : WordTrace (prefixWord ++ tailWord_1097137) baseStart_1097137 baseEnd_1097137 := by
    simpa [prefixWord, tailWord_1097137, baseEnd_1097137] using wordTrace_append hprefix tailTrace_1097137
  have hstable : (prefixWord ++ tailWord_1097137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097137).length < 2 ^ (prefixWord ++ tailWord_1097137).sum := by decide
  have hdescent : baseEnd_1097137 < baseStart_1097137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097152 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_1097152 : Nat := 118140960795 + 1097152 * 2 ^ 59
def prefixEnd_1097152 : Nat := 4983230072969 + 3 ^ 40 * 1097152 * 2
def baseEnd_1097152 : Nat := 375577551361197747636197

theorem tailTrace_1097152 : CollatzResearch.WordTrace tailWord_1097152 prefixEnd_1097152 375577551361197747636197 := by
  unfold tailWord_1097152
  simp only [CollatzResearch.WordTrace]
  refine ⟨20008210460606578744366855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26677613947475438325822473 20008210460606578744366855)
  ·
    refine ⟨30012315690909868116550283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20008210460606578744366855 30012315690909868116550283)
    ·
      refine ⟨45018473536364802174825425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30012315690909868116550283 45018473536364802174825425)
      ·
        refine ⟨33763855152273601631119069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45018473536364802174825425 33763855152273601631119069)
        ·
          refine ⟨12661445682102600611669651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33763855152273601631119069 12661445682102600611669651)
          ·
            refine ⟨18992168523153900917504477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12661445682102600611669651 18992168523153900917504477)
            ·
              refine ⟨7122063196182712844064179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18992168523153900917504477 7122063196182712844064179)
              ·
                refine ⟨10683094794274069266096269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122063196182712844064179 10683094794274069266096269)
                ·
                  refine ⟨4006160547852775974786101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10683094794274069266096269 4006160547852775974786101)
                  ·
                    refine ⟨375577551361197747636197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4006160547852775974786101 375577551361197747636197)
                    ·
                      rfl

theorem cell22_1097152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_1097152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097152 prefixEnd_1097152 := by exact prefixLift 1097152
  have htrace : WordTrace (prefixWord ++ tailWord_1097152) baseStart_1097152 baseEnd_1097152 := by
    simpa [prefixWord, tailWord_1097152, baseEnd_1097152] using wordTrace_append hprefix tailTrace_1097152
  have hstable : (prefixWord ++ tailWord_1097152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097152).length < 2 ^ (prefixWord ++ tailWord_1097152).sum := by decide
  have hdescent : baseEnd_1097152 < baseStart_1097152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097201 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 2, 4]
def baseStart_1097201 : Nat := 118140960795 + 1097201 * 2 ^ 59
def prefixEnd_1097201 : Nat := 4983230072969 + 3 ^ 40 * 1097201 * 2
def baseEnd_1097201 : Nat := 375594325062577953161047

theorem tailTrace_1097201 : CollatzResearch.WordTrace tailWord_1097201 prefixEnd_1097201 375594325062577953161047 := by
  unfold tailWord_1097201
  simp only [CollatzResearch.WordTrace]
  refine ⟨40018208098035638857267457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26678805398690425904844971 40018208098035638857267457)
  ·
    refine ⟨30013656073526729142950593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40018208098035638857267457 30013656073526729142950593)
    ·
      refine ⟨22510242055145046857212945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30013656073526729142950593 22510242055145046857212945)
      ·
        refine ⟨16882681541358785142909709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22510242055145046857212945 16882681541358785142909709)
        ·
          refine ⟨6331005578009544428591141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16882681541358785142909709 6331005578009544428591141)
          ·
            refine ⟨1187063545876789580360839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6331005578009544428591141 1187063545876789580360839)
            ·
              refine ⟨1780595318815184370541259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187063545876789580360839 1780595318815184370541259)
              ·
                refine ⟨2670892978222776555811889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780595318815184370541259 2670892978222776555811889)
                ·
                  refine ⟨2003169733667082416858917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2670892978222776555811889 2003169733667082416858917)
                  ·
                    refine ⟨375594325062577953161047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003169733667082416858917 375594325062577953161047)
                    ·
                      rfl

theorem cell22_1097201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_1097201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097201 prefixEnd_1097201 := by exact prefixLift 1097201
  have htrace : WordTrace (prefixWord ++ tailWord_1097201) baseStart_1097201 baseEnd_1097201 := by
    simpa [prefixWord, tailWord_1097201, baseEnd_1097201] using wordTrace_append hprefix tailTrace_1097201
  have hstable : (prefixWord ++ tailWord_1097201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097201).length < 2 ^ (prefixWord ++ tailWord_1097201).sum := by decide
  have hdescent : baseEnd_1097201 < baseStart_1097201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097220 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_1097220 : Nat := 118140960795 + 1097220 * 2 ^ 59
def prefixEnd_1097220 : Nat := 4983230072969 + 3 ^ 40 * 1097220 * 2
def baseEnd_1097220 : Nat := 375600829150868236935989

theorem tailTrace_1097220 : CollatzResearch.WordTrace tailWord_1097220 prefixEnd_1097220 375600829150868236935989 := by
  unfold tailWord_1097220
  simp only [CollatzResearch.WordTrace]
  refine ⟨20009450542483402551104557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26679267389977870068139409 20009450542483402551104557)
  ·
    refine ⟨7503543953431275956664209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20009450542483402551104557 7503543953431275956664209)
    ·
      refine ⟨5627657965073456967498157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7503543953431275956664209 5627657965073456967498157)
      ·
        refine ⟨2110371736902546362811809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5627657965073456967498157 2110371736902546362811809)
        ·
          refine ⟨1582778802676909772108857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2110371736902546362811809 1582778802676909772108857)
          ·
            refine ⟨1187084102007682329081643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1582778802676909772108857 1187084102007682329081643)
            ·
              refine ⟨1780626153011523493622465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187084102007682329081643 1780626153011523493622465)
              ·
                refine ⟨1335469614758642620216849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780626153011523493622465 1335469614758642620216849)
                ·
                  refine ⟨1001602211068981965162637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1335469614758642620216849 1001602211068981965162637)
                  ·
                    refine ⟨375600829150868236935989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1001602211068981965162637 375600829150868236935989)
                    ·
                      rfl

theorem cell22_1097220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_1097220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097220 prefixEnd_1097220 := by exact prefixLift 1097220
  have htrace : WordTrace (prefixWord ++ tailWord_1097220) baseStart_1097220 baseEnd_1097220 := by
    simpa [prefixWord, tailWord_1097220, baseEnd_1097220] using wordTrace_append hprefix tailTrace_1097220
  have hstable : (prefixWord ++ tailWord_1097220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097220).length < 2 ^ (prefixWord ++ tailWord_1097220).sum := by decide
  have hdescent : baseEnd_1097220 < baseStart_1097220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097304 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1097304 : Nat := 118140960795 + 1097304 * 2 ^ 59
def prefixEnd_1097304 : Nat := 4983230072969 + 3 ^ 40 * 1097304 * 2
def baseEnd_1097304 : Nat := 375629584067520017835731

theorem tailTrace_1097304 : CollatzResearch.WordTrace tailWord_1097304 prefixEnd_1097304 375629584067520017835731 := by
  unfold tailWord_1097304
  simp only [CollatzResearch.WordTrace]
  refine ⟨20010982408331243724133483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26681309877774991632177977 20010982408331243724133483)
  ·
    refine ⟨30016473612496865586200225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20010982408331243724133483 30016473612496865586200225)
    ·
      refine ⟨22512355209372649189650169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30016473612496865586200225 22512355209372649189650169)
      ·
        refine ⟨16884266407029486892237627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22512355209372649189650169 16884266407029486892237627)
        ·
          refine ⟨25326399610544230338356441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16884266407029486892237627 25326399610544230338356441)
          ·
            refine ⟨18994799707908172753767331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25326399610544230338356441 18994799707908172753767331)
            ·
              refine ⟨28492199561862259130650997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18994799707908172753767331 28492199561862259130650997)
              ·
                refine ⟨2671143708924586793498531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28492199561862259130650997 2671143708924586793498531)
                ·
                  refine ⟨4006715563386880190247797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671143708924586793498531 4006715563386880190247797)
                  ·
                    refine ⟨375629584067520017835731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4006715563386880190247797 375629584067520017835731)
                    ·
                      rfl

theorem cell22_1097304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1097304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097304 prefixEnd_1097304 := by exact prefixLift 1097304
  have htrace : WordTrace (prefixWord ++ tailWord_1097304) baseStart_1097304 baseEnd_1097304 := by
    simpa [prefixWord, tailWord_1097304, baseEnd_1097304] using wordTrace_append hprefix tailTrace_1097304
  have hstable : (prefixWord ++ tailWord_1097304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097304).length < 2 ^ (prefixWord ++ tailWord_1097304).sum := by decide
  have hdescent : baseEnd_1097304 < baseStart_1097304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097308 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1097308 : Nat := 118140960795 + 1097308 * 2 ^ 59
def prefixEnd_1097308 : Nat := 4983230072969 + 3 ^ 40 * 1097308 * 2
def baseEnd_1097308 : Nat := 375630953349265340735719

theorem tailTrace_1097308 : CollatzResearch.WordTrace tailWord_1097308 prefixEnd_1097308 375630953349265340735719 := by
  unfold tailWord_1097308
  simp only [CollatzResearch.WordTrace]
  refine ⟨20011055354323998065706289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26681407139098664087608385 20011055354323998065706289)
  ·
    refine ⟨15008291515742998549279717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20011055354323998065706289 15008291515742998549279717)
    ·
      refine ⟨2814054659201812227989947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15008291515742998549279717 2814054659201812227989947)
      ·
        refine ⟨4221081988802718341984921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814054659201812227989947 4221081988802718341984921)
        ·
          refine ⟨3165811491602038756488691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4221081988802718341984921 3165811491602038756488691)
          ·
            refine ⟨4748717237403058134733037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3165811491602038756488691 4748717237403058134733037)
            ·
              refine ⟨1780768964026146800524889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4748717237403058134733037 1780768964026146800524889)
              ·
                refine ⟨1335576723019610100393667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780768964026146800524889 1335576723019610100393667)
                ·
                  refine ⟨2003365084529415150590501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335576723019610100393667 2003365084529415150590501)
                  ·
                    refine ⟨375630953349265340735719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003365084529415150590501 375630953349265340735719)
                    ·
                      rfl

theorem cell22_1097308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1097308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097308 prefixEnd_1097308 := by exact prefixLift 1097308
  have htrace : WordTrace (prefixWord ++ tailWord_1097308) baseStart_1097308 baseEnd_1097308 := by
    simpa [prefixWord, tailWord_1097308, baseEnd_1097308] using wordTrace_append hprefix tailTrace_1097308
  have hstable : (prefixWord ++ tailWord_1097308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097308).length < 2 ^ (prefixWord ++ tailWord_1097308).sum := by decide
  have hdescent : baseEnd_1097308 < baseStart_1097308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097319 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1097319 : Nat := 118140960795 + 1097319 * 2 ^ 59
def prefixEnd_1097319 : Nat := 4983230072969 + 3 ^ 40 * 1097319 * 2
def baseEnd_1097319 : Nat := 375634718874064978710685

theorem tailTrace_1097319 : CollatzResearch.WordTrace tailWord_1097319 prefixEnd_1097319 375634718874064978710685 := by
  unfold tailWord_1097319
  simp only [CollatzResearch.WordTrace]
  refine ⟨40022511911608145010063011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26681674607738763340042007 40022511911608145010063011)
  ·
    refine ⟨60033767867412217515094517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40022511911608145010063011 60033767867412217515094517)
    ·
      refine ⟨5628165737569895392040111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60033767867412217515094517 5628165737569895392040111)
      ·
        refine ⟨8442248606354843088060167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5628165737569895392040111 8442248606354843088060167)
        ·
          refine ⟨12663372909532264632090251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8442248606354843088060167 12663372909532264632090251)
          ·
            refine ⟨18995059364298396948135377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12663372909532264632090251 18995059364298396948135377)
            ·
              refine ⟨14246294523223797711101533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18995059364298396948135377 14246294523223797711101533)
              ·
                refine ⟨5342360446208924141663075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14246294523223797711101533 5342360446208924141663075)
                ·
                  refine ⟨8013540669313386212494613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5342360446208924141663075 8013540669313386212494613)
                  ·
                    refine ⟨375634718874064978710685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8013540669313386212494613 375634718874064978710685)
                    ·
                      rfl

theorem cell22_1097319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1097319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097319 prefixEnd_1097319 := by exact prefixLift 1097319
  have htrace : WordTrace (prefixWord ++ tailWord_1097319) baseStart_1097319 baseEnd_1097319 := by
    simpa [prefixWord, tailWord_1097319, baseEnd_1097319] using wordTrace_append hprefix tailTrace_1097319
  have hstable : (prefixWord ++ tailWord_1097319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097319).length < 2 ^ (prefixWord ++ tailWord_1097319).sum := by decide
  have hdescent : baseEnd_1097319 < baseStart_1097319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097325 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_1097325 : Nat := 118140960795 + 1097325 * 2 ^ 59
def prefixEnd_1097325 : Nat := 4983230072969 + 3 ^ 40 * 1097325 * 2
def baseEnd_1097325 : Nat := 375636772796682963060667

theorem tailTrace_1097325 : CollatzResearch.WordTrace tailWord_1097325 prefixEnd_1097325 375636772796682963060667 := by
  unfold tailWord_1097325
  simp only [CollatzResearch.WordTrace]
  refine ⟨40022730749586408034781429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26681820499724272023187619 40022730749586408034781429)
  ·
    refine ⟨3752131007773725753260759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40022730749586408034781429 3752131007773725753260759)
    ·
      refine ⟨5628196511660588629891139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3752131007773725753260759 5628196511660588629891139)
      ·
        refine ⟨8442294767490882944836709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5628196511660588629891139 8442294767490882944836709)
        ·
          refine ⟨1582930268904540552156883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8442294767490882944836709 1582930268904540552156883)
          ·
            refine ⟨2374395403356810828235325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582930268904540552156883 2374395403356810828235325)
            ·
              refine ⟨890398276258804060588247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2374395403356810828235325 890398276258804060588247)
              ·
                refine ⟨1335597414388206090882371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890398276258804060588247 1335597414388206090882371)
                ·
                  refine ⟨2003396121582309136323557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335597414388206090882371 2003396121582309136323557)
                  ·
                    refine ⟨375636772796682963060667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003396121582309136323557 375636772796682963060667)
                    ·
                      rfl

theorem cell22_1097325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_1097325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097325 prefixEnd_1097325 := by exact prefixLift 1097325
  have htrace : WordTrace (prefixWord ++ tailWord_1097325) baseStart_1097325 baseEnd_1097325 := by
    simpa [prefixWord, tailWord_1097325, baseEnd_1097325] using wordTrace_append hprefix tailTrace_1097325
  have hstable : (prefixWord ++ tailWord_1097325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097325).length < 2 ^ (prefixWord ++ tailWord_1097325).sum := by decide
  have hdescent : baseEnd_1097325 < baseStart_1097325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097351 : List Nat := [1, 1, 4, 2, 1, 5, 1, 7]
def baseStart_1097351 : Nat := 118140960795 + 1097351 * 2 ^ 59
def prefixEnd_1097351 : Nat := 4983230072969 + 3 ^ 40 * 1097351 * 2
def baseEnd_1097351 : Nat := 41738408125336395767843

theorem tailTrace_1097351 : CollatzResearch.WordTrace tailWord_1097351 prefixEnd_1097351 41738408125336395767843 := by
  unfold tailWord_1097351
  simp only [CollatzResearch.WordTrace]
  refine ⟨40023679047492214475227907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26682452698328142983485271 40023679047492214475227907)
  ·
    refine ⟨60035518571238321712841861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40023679047492214475227907 60035518571238321712841861)
    ·
      refine ⟨11256659732107185321157849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60035518571238321712841861 11256659732107185321157849)
      ·
        refine ⟨8442494799080388990868387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11256659732107185321157849 8442494799080388990868387)
        ·
          refine ⟨12663742198620583486302581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8442494799080388990868387 12663742198620583486302581)
          ·
            refine ⟨1187225831120679701840867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12663742198620583486302581 1187225831120679701840867)
            ·
              refine ⟨1780838746681019552761301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187225831120679701840867 1780838746681019552761301)
              ·
                refine ⟨41738408125336395767843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1780838746681019552761301 41738408125336395767843)
                ·
                  rfl

theorem cell22_1097351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 7].length) (baseStart_1097351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097351 prefixEnd_1097351 := by exact prefixLift 1097351
  have htrace : WordTrace (prefixWord ++ tailWord_1097351) baseStart_1097351 baseEnd_1097351 := by
    simpa [prefixWord, tailWord_1097351, baseEnd_1097351] using wordTrace_append hprefix tailTrace_1097351
  have hstable : (prefixWord ++ tailWord_1097351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097351).length < 2 ^ (prefixWord ++ tailWord_1097351).sum := by decide
  have hdescent : baseEnd_1097351 < baseStart_1097351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097379 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 7]
def baseStart_1097379 : Nat := 118140960795 + 1097379 * 2 ^ 59
def prefixEnd_1097379 : Nat := 4983230072969 + 3 ^ 40 * 1097379 * 2
def baseEnd_1097379 : Nat := 125218419366748274070167

theorem tailTrace_1097379 : CollatzResearch.WordTrace tailWord_1097379 prefixEnd_1097379 125218419366748274070167 := by
  unfold tailWord_1097379
  simp only [CollatzResearch.WordTrace]
  refine ⟨40024700291390775257247191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26683133527593850171498127 40024700291390775257247191)
  ·
    refine ⟨60037050437086162885870787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40024700291390775257247191 60037050437086162885870787)
    ·
      refine ⟨90055575655629244328806181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60037050437086162885870787 90055575655629244328806181)
      ·
        refine ⟨16885420435430483311651159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90055575655629244328806181 16885420435430483311651159)
        ·
          refine ⟨25328130653145724967476739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16885420435430483311651159 25328130653145724967476739)
          ·
            refine ⟨37992195979718587451215109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25328130653145724967476739 37992195979718587451215109)
            ·
              refine ⟨7123536746197235147102833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37992195979718587451215109 7123536746197235147102833)
              ·
                refine ⟨5342652559647926360327125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7123536746197235147102833 5342652559647926360327125)
                ·
                  refine ⟨125218419366748274070167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5342652559647926360327125 125218419366748274070167)
                  ·
                    rfl

theorem cell22_1097379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_1097379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097379 prefixEnd_1097379 := by exact prefixLift 1097379
  have htrace : WordTrace (prefixWord ++ tailWord_1097379) baseStart_1097379 baseEnd_1097379 := by
    simpa [prefixWord, tailWord_1097379, baseEnd_1097379] using wordTrace_append hprefix tailTrace_1097379
  have hstable : (prefixWord ++ tailWord_1097379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097379).length < 2 ^ (prefixWord ++ tailWord_1097379).sum := by decide
  have hdescent : baseEnd_1097379 < baseStart_1097379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097424 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 8]
def baseStart_1097424 : Nat := 118140960795 + 1097424 * 2 ^ 59
def prefixEnd_1097424 : Nat := 4983230072969 + 3 ^ 40 * 1097424 * 2
def baseEnd_1097424 : Nat := 125223554173293234945121

theorem tailTrace_1097424 : CollatzResearch.WordTrace tailWord_1097424 prefixEnd_1097424 125223554173293234945121 := by
  unfold tailWord_1097424
  simp only [CollatzResearch.WordTrace]
  refine ⟨20013170788113873971317663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26684227717485165295090217 20013170788113873971317663)
  ·
    refine ⟨30019756182170810956976495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20013170788113873971317663 30019756182170810956976495)
    ·
      refine ⟨45029634273256216435464743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30019756182170810956976495 45029634273256216435464743)
      ·
        refine ⟨67544451409884324653197115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45029634273256216435464743 67544451409884324653197115)
        ·
          refine ⟨101316677114826486979795673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67544451409884324653197115 101316677114826486979795673)
          ·
            refine ⟨75987507836119865234846755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101316677114826486979795673 75987507836119865234846755)
            ·
              refine ⟨113981261754179797852270133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75987507836119865234846755 113981261754179797852270133)
              ·
                refine ⟨10685743289454356048650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113981261754179797852270133 10685743289454356048650325)
                ·
                  refine ⟨125223554173293234945121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10685743289454356048650325 125223554173293234945121)
                  ·
                    rfl

theorem cell22_1097424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_1097424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097424 prefixEnd_1097424 := by exact prefixLift 1097424
  have htrace : WordTrace (prefixWord ++ tailWord_1097424) baseStart_1097424 baseEnd_1097424 := by
    simpa [prefixWord, tailWord_1097424, baseEnd_1097424] using wordTrace_append hprefix tailTrace_1097424
  have hstable : (prefixWord ++ tailWord_1097424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097424).length < 2 ^ (prefixWord ++ tailWord_1097424).sum := by decide
  have hdescent : baseEnd_1097424 < baseStart_1097424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097486 : List Nat := [4, 1, 1, 2, 1, 1, 4, 8]
def baseStart_1097486 : Nat := 118140960795 + 1097486 * 2 ^ 59
def prefixEnd_1097486 : Nat := 4983230072969 + 3 ^ 40 * 1097486 * 2
def baseEnd_1097486 : Nat := 41743542931881356642797

theorem tailTrace_1097486 : CollatzResearch.WordTrace tailWord_1097486 prefixEnd_1097486 41743542931881356642797 := by
  unfold tailWord_1097486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003575362750391566424039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26685735268002088354261541 5003575362750391566424039)
  ·
    refine ⟨7505363044125587349636059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5003575362750391566424039 7505363044125587349636059)
    ·
      refine ⟨11258044566188381024454089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7505363044125587349636059 11258044566188381024454089)
      ·
        refine ⟨8443533424641285768340567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11258044566188381024454089 8443533424641285768340567)
        ·
          refine ⟨12665300136961928652510851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8443533424641285768340567 12665300136961928652510851)
          ·
            refine ⟨18997950205442892978766277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12665300136961928652510851 18997950205442892978766277)
            ·
              refine ⟨3562115663520542433518677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18997950205442892978766277 3562115663520542433518677)
              ·
                refine ⟨41743542931881356642797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3562115663520542433518677 41743542931881356642797)
                ·
                  rfl

theorem cell22_1097486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_1097486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097486 prefixEnd_1097486 := by exact prefixLift 1097486
  have htrace : WordTrace (prefixWord ++ tailWord_1097486) baseStart_1097486 baseEnd_1097486 := by
    simpa [prefixWord, tailWord_1097486, baseEnd_1097486] using wordTrace_append hprefix tailTrace_1097486
  have hstable : (prefixWord ++ tailWord_1097486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097486).length < 2 ^ (prefixWord ++ tailWord_1097486).sum := by decide
  have hdescent : baseEnd_1097486 < baseStart_1097486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097490 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1097490 : Nat := 118140960795 + 1097490 * 2 ^ 59
def prefixEnd_1097490 : Nat := 4983230072969 + 3 ^ 40 * 1097490 * 2
def baseEnd_1097490 : Nat := 375693255668677532685161

theorem tailTrace_1097490 : CollatzResearch.WordTrace tailWord_1097490 prefixEnd_1097490 375693255668677532685161 := by
  unfold tailWord_1097490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007187198497160303634481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26685832529325760809691949 10007187198497160303634481)
  ·
    refine ⟨7505390398872870227725861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10007187198497160303634481 7505390398872870227725861)
    ·
      refine ⟨1407260699788663167698599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7505390398872870227725861 1407260699788663167698599)
      ·
        refine ⟨2110891049682994751547899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407260699788663167698599 2110891049682994751547899)
        ·
          refine ⟨3166336574524492127321849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110891049682994751547899 3166336574524492127321849)
          ·
            refine ⟨2374752430893369095491387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166336574524492127321849 2374752430893369095491387)
            ·
              refine ⟨3562128646340053643237081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374752430893369095491387 3562128646340053643237081)
              ·
                refine ⟨2671596484755040232427811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3562128646340053643237081 2671596484755040232427811)
                ·
                  refine ⟨4007394727132560348641717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671596484755040232427811 4007394727132560348641717)
                  ·
                    refine ⟨375693255668677532685161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4007394727132560348641717 375693255668677532685161)
                    ·
                      rfl

theorem cell22_1097490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1097490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097490 prefixEnd_1097490 := by exact prefixLift 1097490
  have htrace : WordTrace (prefixWord ++ tailWord_1097490) baseStart_1097490 baseEnd_1097490 := by
    simpa [prefixWord, tailWord_1097490, baseEnd_1097490] using wordTrace_append hprefix tailTrace_1097490
  have hstable : (prefixWord ++ tailWord_1097490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097490).length < 2 ^ (prefixWord ++ tailWord_1097490).sum := by decide
  have hdescent : baseEnd_1097490 < baseStart_1097490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097516 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_1097516 : Nat := 118140960795 + 1097516 * 2 ^ 59
def prefixEnd_1097516 : Nat := 4983230072969 + 3 ^ 40 * 1097516 * 2
def baseEnd_1097516 : Nat := 375702156000022131535081

theorem tailTrace_1097516 : CollatzResearch.WordTrace tailWord_1097516 prefixEnd_1097516 375702156000022131535081 := by
  unfold tailWord_1097516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20014848545947223827492201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26686464727929631769989601 20014848545947223827492201)
  ·
    refine ⟨15011136409460417870619151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20014848545947223827492201 15011136409460417870619151)
    ·
      refine ⟨22516704614190626805928727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15011136409460417870619151 22516704614190626805928727)
      ·
        refine ⟨33775056921285940208893091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22516704614190626805928727 33775056921285940208893091)
        ·
          refine ⟨50662585381928910313339637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33775056921285940208893091 50662585381928910313339637)
          ·
            refine ⟨4749617379555835341875591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50662585381928910313339637 4749617379555835341875591)
            ·
              refine ⟨7124426069333753012813387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749617379555835341875591 7124426069333753012813387)
              ·
                refine ⟨10686639104000629519220081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7124426069333753012813387 10686639104000629519220081)
                ·
                  refine ⟨8014979328000472139415061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10686639104000629519220081 8014979328000472139415061)
                  ·
                    refine ⟨375702156000022131535081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8014979328000472139415061 375702156000022131535081)
                    ·
                      rfl

theorem cell22_1097516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_1097516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097516 prefixEnd_1097516 := by exact prefixLift 1097516
  have htrace : WordTrace (prefixWord ++ tailWord_1097516) baseStart_1097516 baseEnd_1097516 := by
    simpa [prefixWord, tailWord_1097516, baseEnd_1097516] using wordTrace_append hprefix tailTrace_1097516
  have hstable : (prefixWord ++ tailWord_1097516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097516).length < 2 ^ (prefixWord ++ tailWord_1097516).sum := by decide
  have hdescent : baseEnd_1097516 < baseStart_1097516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097535 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 3, 3]
def baseStart_1097535 : Nat := 118140960795 + 1097535 * 2 ^ 59
def prefixEnd_1097535 : Nat := 4983230072969 + 3 ^ 40 * 1097535 * 2
def baseEnd_1097535 : Nat := 375708660088312415310023

theorem tailTrace_1097535 : CollatzResearch.WordTrace tailWord_1097535 prefixEnd_1097535 375708660088312415310023 := by
  unfold tailWord_1097535
  simp only [CollatzResearch.WordTrace]
  refine ⟨40030390078825613899926059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26686926719217075933284039 40030390078825613899926059)
  ·
    refine ⟨60045585118238420849889089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40030390078825613899926059 60045585118238420849889089)
    ·
      refine ⟨45034188838678815637416817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60045585118238420849889089 45034188838678815637416817)
      ·
        refine ⟨33775641629009111728062613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45034188838678815637416817 33775641629009111728062613)
        ·
          refine ⟨1583233201359802112252935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33775641629009111728062613 1583233201359802112252935)
          ·
            refine ⟨2374849802039703168379403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583233201359802112252935 2374849802039703168379403)
            ·
              refine ⟨3562274703059554752569105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374849802039703168379403 3562274703059554752569105)
              ·
                refine ⟨2671706027294666064426829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3562274703059554752569105 2671706027294666064426829)
                ·
                  refine ⟨1001889760235499774160061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2671706027294666064426829 1001889760235499774160061)
                  ·
                    refine ⟨375708660088312415310023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1001889760235499774160061 375708660088312415310023)
                    ·
                      rfl

theorem cell22_1097535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_1097535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097535 prefixEnd_1097535 := by exact prefixLift 1097535
  have htrace : WordTrace (prefixWord ++ tailWord_1097535) baseStart_1097535 baseEnd_1097535 := by
    simpa [prefixWord, tailWord_1097535, baseEnd_1097535] using wordTrace_append hprefix tailTrace_1097535
  have hstable : (prefixWord ++ tailWord_1097535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097535).length < 2 ^ (prefixWord ++ tailWord_1097535).sum := by decide
  have hdescent : baseEnd_1097535 < baseStart_1097535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097546 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1097546 : Nat := 118140960795 + 1097546 * 2 ^ 59
def prefixEnd_1097546 : Nat := 4983230072969 + 3 ^ 40 * 1097546 * 2
def baseEnd_1097546 : Nat := 375712425613112053284989

theorem tailTrace_1097546 : CollatzResearch.WordTrace tailWord_1097546 prefixEnd_1097546 375712425613112053284989 := by
  unfold tailWord_1097546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007697820446440694644123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26687194187857175185717661 10007697820446440694644123)
  ·
    refine ⟨15011546730669661041966185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10007697820446440694644123 15011546730669661041966185)
    ·
      refine ⟨11258660048002245781474639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15011546730669661041966185 11258660048002245781474639)
      ·
        refine ⟨16887990072003368672211959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11258660048002245781474639 16887990072003368672211959)
        ·
          refine ⟨25331985108005053008317939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16887990072003368672211959 25331985108005053008317939)
          ·
            refine ⟨37997977662007579512476909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25331985108005053008317939 37997977662007579512476909)
            ·
              refine ⟨14249241623252842317178841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37997977662007579512476909 14249241623252842317178841)
              ·
                refine ⟨10686931217439631737884131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14249241623252842317178841 10686931217439631737884131)
                ·
                  refine ⟨16030396826159447606826197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10686931217439631737884131 16030396826159447606826197)
                  ·
                    refine ⟨375712425613112053284989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16030396826159447606826197 375712425613112053284989)
                    ·
                      rfl

theorem cell22_1097546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1097546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097546 prefixEnd_1097546 := by exact prefixLift 1097546
  have htrace : WordTrace (prefixWord ++ tailWord_1097546) baseStart_1097546 baseEnd_1097546 := by
    simpa [prefixWord, tailWord_1097546, baseEnd_1097546] using wordTrace_append hprefix tailTrace_1097546
  have hstable : (prefixWord ++ tailWord_1097546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097546).length < 2 ^ (prefixWord ++ tailWord_1097546).sum := by decide
  have hdescent : baseEnd_1097546 < baseStart_1097546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097582 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_1097582 : Nat := 118140960795 + 1097582 * 2 ^ 59
def prefixEnd_1097582 : Nat := 4983230072969 + 3 ^ 40 * 1097582 * 2
def baseEnd_1097582 : Nat := 125241583049606653128293

theorem tailTrace_1097582 : CollatzResearch.WordTrace tailWord_1097582 prefixEnd_1097582 125241583049606653128293 := by
  unfold tailWord_1097582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004013038706917615860875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26688069539770227284591333 5004013038706917615860875)
  ·
    refine ⟨7506019558060376423791313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5004013038706917615860875 7506019558060376423791313)
    ·
      refine ⟨5629514668545282317843485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7506019558060376423791313 5629514668545282317843485)
      ·
        refine ⟨2111068000704480869191307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5629514668545282317843485 2111068000704480869191307)
        ·
          refine ⟨3166602001056721303786961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111068000704480869191307 3166602001056721303786961)
          ·
            refine ⟨2374951500792540977840221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166602001056721303786961 2374951500792540977840221)
            ·
              refine ⟨890606812797202866690083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2374951500792540977840221 890606812797202866690083)
              ·
                refine ⟨1335910219195804300035125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890606812797202866690083 1335910219195804300035125)
                ·
                  refine ⟨125241583049606653128293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1335910219195804300035125 125241583049606653128293)
                  ·
                    rfl

theorem cell22_1097582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_1097582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097582 prefixEnd_1097582 := by exact prefixLift 1097582
  have htrace : WordTrace (prefixWord ++ tailWord_1097582) baseStart_1097582 baseEnd_1097582 := by
    simpa [prefixWord, tailWord_1097582, baseEnd_1097582] using wordTrace_append hprefix tailTrace_1097582
  have hstable : (prefixWord ++ tailWord_1097582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097582).length < 2 ^ (prefixWord ++ tailWord_1097582).sum := by decide
  have hdescent : baseEnd_1097582 < baseStart_1097582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097623 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 4, 4]
def baseStart_1097623 : Nat := 118140960795 + 1097623 * 2 ^ 59
def prefixEnd_1097623 : Nat := 4983230072969 + 3 ^ 40 * 1097623 * 2
def baseEnd_1097623 : Nat := 375738784286709519109753

theorem tailTrace_1097623 : CollatzResearch.WordTrace tailWord_1097623 prefixEnd_1097623 375738784286709519109753 := by
  unfold tailWord_1097623
  simp only [CollatzResearch.WordTrace]
  refine ⟨40033599702506804929129523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26689066468337869952753015 40033599702506804929129523)
  ·
    refine ⟨60050399553760207393694285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40033599702506804929129523 60050399553760207393694285)
    ·
      refine ⟨22518899832660077772635357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60050399553760207393694285 22518899832660077772635357)
      ·
        refine ⟨8444587437247529164738259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22518899832660077772635357 8444587437247529164738259)
        ·
          refine ⟨12666881155871293747107389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8444587437247529164738259 12666881155871293747107389)
          ·
            refine ⟨4750080433451735155165271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12666881155871293747107389 4750080433451735155165271)
            ·
              refine ⟨7125120650177602732747907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750080433451735155165271 7125120650177602732747907)
              ·
                refine ⟨10687680975266404099121861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7125120650177602732747907 10687680975266404099121861)
                ·
                  refine ⟨2003940182862450768585349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10687680975266404099121861 2003940182862450768585349)
                  ·
                    refine ⟨375738784286709519109753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003940182862450768585349 375738784286709519109753)
                    ·
                      rfl

theorem cell22_1097623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_1097623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097623 prefixEnd_1097623 := by exact prefixLift 1097623
  have htrace : WordTrace (prefixWord ++ tailWord_1097623) baseStart_1097623 baseEnd_1097623 := by
    simpa [prefixWord, tailWord_1097623, baseEnd_1097623] using wordTrace_append hprefix tailTrace_1097623
  have hstable : (prefixWord ++ tailWord_1097623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097623).length < 2 ^ (prefixWord ++ tailWord_1097623).sum := by decide
  have hdescent : baseEnd_1097623 < baseStart_1097623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097687 : List Nat := [1, 1, 3, 2, 1, 1, 5, 4, 1, 3]
def baseStart_1097687 : Nat := 118140960795 + 1097687 * 2 ^ 59
def prefixEnd_1097687 : Nat := 4983230072969 + 3 ^ 40 * 1097687 * 2
def baseEnd_1097687 : Nat := 375760692794634685509557

theorem tailTrace_1097687 : CollatzResearch.WordTrace tailWord_1097687 prefixEnd_1097687 375760692794634685509557 := by
  unfold tailWord_1097687
  simp only [CollatzResearch.WordTrace]
  refine ⟨40035933974274943859459315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26690622649516629239639543 40035933974274943859459315)
  ·
    refine ⟨60053900961412415789188973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40035933974274943859459315 60053900961412415789188973)
    ·
      refine ⟨22520212860529655920945865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60053900961412415789188973 22520212860529655920945865)
      ·
        refine ⟨16890159645397241940709399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22520212860529655920945865 16890159645397241940709399)
        ·
          refine ⟨25335239468095862911064099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16890159645397241940709399 25335239468095862911064099)
          ·
            refine ⟨38002859202143794366596149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25335239468095862911064099 38002859202143794366596149)
            ·
              refine ⟨3562768050200980721868389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38002859202143794366596149 3562768050200980721868389)
              ·
                refine ⟨668019009412683885350323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3562768050200980721868389 668019009412683885350323)
                ·
                  refine ⟨1002028514119025828025485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668019009412683885350323 1002028514119025828025485)
                  ·
                    refine ⟨375760692794634685509557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002028514119025828025485 375760692794634685509557)
                    ·
                      rfl

theorem cell22_1097687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_1097687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097687 prefixEnd_1097687 := by exact prefixLift 1097687
  have htrace : WordTrace (prefixWord ++ tailWord_1097687) baseStart_1097687 baseEnd_1097687 := by
    simpa [prefixWord, tailWord_1097687, baseEnd_1097687] using wordTrace_append hprefix tailTrace_1097687
  have hstable : (prefixWord ++ tailWord_1097687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097687).length < 2 ^ (prefixWord ++ tailWord_1097687).sum := by decide
  have hdescent : baseEnd_1097687 < baseStart_1097687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097764 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_1097764 : Nat := 118140960795 + 1097764 * 2 ^ 59
def prefixEnd_1097764 : Nat := 4983230072969 + 3 ^ 40 * 1097764 * 2
def baseEnd_1097764 : Nat := 375787051468232151334321

theorem tailTrace_1097764 : CollatzResearch.WordTrace tailWord_1097764 prefixEnd_1097764 375787051468232151334321 := by
  unfold tailWord_1097764
  simp only [CollatzResearch.WordTrace]
  refine ⟨20019371197497993005006173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26692494929997324006674897 20019371197497993005006173)
  ·
    refine ⟨7507264199061747376877315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20019371197497993005006173 7507264199061747376877315)
    ·
      refine ⟨11260896298592621065315973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7507264199061747376877315 11260896298592621065315973)
      ·
        refine ⟨2111418055986116449746745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11260896298592621065315973 2111418055986116449746745)
        ·
          refine ⟨1583563541989587337310059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2111418055986116449746745 1583563541989587337310059)
          ·
            refine ⟨2375345312984381005965089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583563541989587337310059 2375345312984381005965089)
            ·
              refine ⟨1781508984738285754473817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375345312984381005965089 1781508984738285754473817)
              ·
                refine ⟨1336131738553714315855363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781508984738285754473817 1336131738553714315855363)
                ·
                  refine ⟨2004197607830571473783045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336131738553714315855363 2004197607830571473783045)
                  ·
                    refine ⟨375787051468232151334321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2004197607830571473783045 375787051468232151334321)
                    ·
                      rfl

theorem cell22_1097764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_1097764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097764 prefixEnd_1097764 := by exact prefixLift 1097764
  have htrace : WordTrace (prefixWord ++ tailWord_1097764) baseStart_1097764 baseEnd_1097764 := by
    simpa [prefixWord, tailWord_1097764, baseEnd_1097764] using wordTrace_append hprefix tailTrace_1097764
  have hstable : (prefixWord ++ tailWord_1097764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097764).length < 2 ^ (prefixWord ++ tailWord_1097764).sum := by decide
  have hdescent : baseEnd_1097764 < baseStart_1097764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097803 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 8]
def baseStart_1097803 : Nat := 118140960795 + 1097803 * 2 ^ 59
def prefixEnd_1097803 : Nat := 4983230072969 + 3 ^ 40 * 1097803 * 2
def baseEnd_1097803 : Nat := 375800401965249049609201

theorem tailTrace_1097803 : CollatzResearch.WordTrace tailWord_1097803 prefixEnd_1097803 375800401965249049609201 := by
  unfold tailWord_1097803
  simp only [CollatzResearch.WordTrace]
  refine ⟨40040164841854695670682063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26693443227903130447121375 40040164841854695670682063)
  ·
    refine ⟨60060247262782043506023095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40040164841854695670682063 60060247262782043506023095)
    ·
      refine ⟨90090370894173065259034643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60060247262782043506023095 90090370894173065259034643)
      ·
        refine ⟨135135556341259597888551965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90090370894173065259034643 135135556341259597888551965)
        ·
          refine ⟨50675833627972349208206987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135135556341259597888551965 50675833627972349208206987)
          ·
            refine ⟨76013750441958523812310481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50675833627972349208206987 76013750441958523812310481)
            ·
              refine ⟨57010312831468892859232861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76013750441958523812310481 57010312831468892859232861)
              ·
                refine ⟨21378867311800834822212323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57010312831468892859232861 21378867311800834822212323)
                ·
                  refine ⟨32068300967701252233318485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21378867311800834822212323 32068300967701252233318485)
                  ·
                    refine ⟨375800401965249049609201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32068300967701252233318485 375800401965249049609201)
                    ·
                      rfl

theorem cell22_1097803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_1097803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097803 prefixEnd_1097803 := by exact prefixLift 1097803
  have htrace : WordTrace (prefixWord ++ tailWord_1097803) baseStart_1097803 baseEnd_1097803 := by
    simpa [prefixWord, tailWord_1097803, baseEnd_1097803] using wordTrace_append hprefix tailTrace_1097803
  have hstable : (prefixWord ++ tailWord_1097803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097803).length < 2 ^ (prefixWord ++ tailWord_1097803).sum := by decide
  have hdescent : baseEnd_1097803 < baseStart_1097803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097852 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 5]
def baseStart_1097852 : Nat := 118140960795 + 1097852 * 2 ^ 59
def prefixEnd_1097852 : Nat := 4983230072969 + 3 ^ 40 * 1097852 * 2
def baseEnd_1097852 : Nat := 125272391888876418378017

theorem tailTrace_1097852 : CollatzResearch.WordTrace tailWord_1097852 prefixEnd_1097852 125272391888876418378017 := by
  unfold tailWord_1097852
  simp only [CollatzResearch.WordTrace]
  refine ⟨20020976009338588519607905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26694634679118118026143873 20020976009338588519607905)
  ·
    refine ⟨15015732007003941389705929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20020976009338588519607905 15015732007003941389705929)
    ·
      refine ⟨11261799005252956042279447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15015732007003941389705929 11261799005252956042279447)
      ·
        refine ⟨16892698507879434063419171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11261799005252956042279447 16892698507879434063419171)
        ·
          refine ⟨25339047761819151095128757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16892698507879434063419171 25339047761819151095128757)
          ·
            refine ⟨2375535727670545415168321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25339047761819151095128757 2375535727670545415168321)
            ·
              refine ⟨1781651795752909061376241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375535727670545415168321 1781651795752909061376241)
              ·
                refine ⟨1336238846814681796032181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781651795752909061376241 1336238846814681796032181)
                ·
                  refine ⟨125272391888876418378017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336238846814681796032181 125272391888876418378017)
                  ·
                    rfl

theorem cell22_1097852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_1097852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097852 prefixEnd_1097852 := by exact prefixLift 1097852
  have htrace : WordTrace (prefixWord ++ tailWord_1097852) baseStart_1097852 baseEnd_1097852 := by
    simpa [prefixWord, tailWord_1097852, baseEnd_1097852] using wordTrace_append hprefix tailTrace_1097852
  have hstable : (prefixWord ++ tailWord_1097852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097852).length < 2 ^ (prefixWord ++ tailWord_1097852).sum := by decide
  have hdescent : baseEnd_1097852 < baseStart_1097852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097865 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_1097865 : Nat := 118140960795 + 1097865 * 2 ^ 59
def prefixEnd_1097865 : Nat := 4983230072969 + 3 ^ 40 * 1097865 * 2
def baseEnd_1097865 : Nat := 375821625832301554559011

theorem tailTrace_1097865 : CollatzResearch.WordTrace tailWord_1097865 prefixEnd_1097865 375821625832301554559011 := by
  unfold tailWord_1097865
  simp only [CollatzResearch.WordTrace]
  refine ⟨40042426167630080259439049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26694950778420053506292699 40042426167630080259439049)
  ·
    refine ⟨30031819625722560194579287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40042426167630080259439049 30031819625722560194579287)
    ·
      refine ⟨45047729438583840291868931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30031819625722560194579287 45047729438583840291868931)
      ·
        refine ⟨67571594157875760437803397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45047729438583840291868931 67571594157875760437803397)
        ·
          refine ⟨12669673904601705082088137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67571594157875760437803397 12669673904601705082088137)
          ·
            refine ⟨9502255428451278811566103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12669673904601705082088137 9502255428451278811566103)
            ·
              refine ⟨14253383142676918217349155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9502255428451278811566103 14253383142676918217349155)
              ·
                refine ⟨21380074714015377326023733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14253383142676918217349155 21380074714015377326023733)
                ·
                  refine ⟨2004382004438941624314725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21380074714015377326023733 2004382004438941624314725)
                  ·
                    refine ⟨375821625832301554559011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2004382004438941624314725 375821625832301554559011)
                    ·
                      rfl

theorem cell22_1097865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_1097865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097865 prefixEnd_1097865 := by exact prefixLift 1097865
  have htrace : WordTrace (prefixWord ++ tailWord_1097865) baseStart_1097865 baseEnd_1097865 := by
    simpa [prefixWord, tailWord_1097865, baseEnd_1097865] using wordTrace_append hprefix tailTrace_1097865
  have hstable : (prefixWord ++ tailWord_1097865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097865).length < 2 ^ (prefixWord ++ tailWord_1097865).sum := by decide
  have hdescent : baseEnd_1097865 < baseStart_1097865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097912 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 4, 3]
def baseStart_1097912 : Nat := 118140960795 + 1097912 * 2 ^ 59
def prefixEnd_1097912 : Nat := 4983230072969 + 3 ^ 40 * 1097912 * 2
def baseEnd_1097912 : Nat := 375837714892809098633867

theorem tailTrace_1097912 : CollatzResearch.WordTrace tailWord_1097912 prefixEnd_1097912 375837714892809098633867 := by
  unfold tailWord_1097912
  simp only [CollatzResearch.WordTrace]
  refine ⟨20022070199229903643199995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26696093598973204857599993 20022070199229903643199995)
  ·
    refine ⟨30033105298844855464799993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20022070199229903643199995 30033105298844855464799993)
    ·
      refine ⟨22524828974133641598599995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30033105298844855464799993 22524828974133641598599995)
      ·
        refine ⟨33787243461200462397899993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22524828974133641598599995 33787243461200462397899993)
        ·
          refine ⟨25340432595900346798424995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33787243461200462397899993 25340432595900346798424995)
          ·
            refine ⟨38010648893850520197637493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25340432595900346798424995 38010648893850520197637493)
            ·
              refine ⟨3563498333798486268528515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38010648893850520197637493 3563498333798486268528515)
              ·
                refine ⟨5345247500697729402792773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563498333798486268528515 5345247500697729402792773)
                ·
                  refine ⟨1002233906380824263023645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5345247500697729402792773 1002233906380824263023645)
                  ·
                    refine ⟨375837714892809098633867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002233906380824263023645 375837714892809098633867)
                    ·
                      rfl

theorem cell22_1097912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_1097912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097912 prefixEnd_1097912 := by exact prefixLift 1097912
  have htrace : WordTrace (prefixWord ++ tailWord_1097912) baseStart_1097912 baseEnd_1097912 := by
    simpa [prefixWord, tailWord_1097912, baseEnd_1097912] using wordTrace_append hprefix tailTrace_1097912
  have hstable : (prefixWord ++ tailWord_1097912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097912).length < 2 ^ (prefixWord ++ tailWord_1097912).sum := by decide
  have hdescent : baseEnd_1097912 < baseStart_1097912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097987 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 5]
def baseStart_1097987 : Nat := 118140960795 + 1097987 * 2 ^ 59
def prefixEnd_1097987 : Nat := 4983230072969 + 3 ^ 40 * 1097987 * 2
def baseEnd_1097987 : Nat := 125287796308511301002879

theorem tailTrace_1097987 : CollatzResearch.WordTrace tailWord_1097987 prefixEnd_1097987 125287796308511301002879 := by
  unfold tailWord_1097987
  simp only [CollatzResearch.WordTrace]
  refine ⟨40046875873188095095380215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26697917248792063396920143 40046875873188095095380215)
  ·
    refine ⟨60070313809782142643070323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40046875873188095095380215 60070313809782142643070323)
    ·
      refine ⟨90105470714673213964605485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60070313809782142643070323 90105470714673213964605485)
      ·
        refine ⟨33789551518002455236727057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90105470714673213964605485 33789551518002455236727057)
        ·
          refine ⟨25342163638501841427545293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33789551518002455236727057 25342163638501841427545293)
          ·
            refine ⟨9503311364438190535329485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25342163638501841427545293 9503311364438190535329485)
            ·
              refine ⟨3563741761664321450748557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9503311364438190535329485 3563741761664321450748557)
              ·
                refine ⟨1336403160624120544030709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3563741761664321450748557 1336403160624120544030709)
                ·
                  refine ⟨125287796308511301002879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336403160624120544030709 125287796308511301002879)
                  ·
                    rfl

theorem cell22_1097987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 5].length) (baseStart_1097987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1097987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1097987 prefixEnd_1097987 := by exact prefixLift 1097987
  have htrace : WordTrace (prefixWord ++ tailWord_1097987) baseStart_1097987 baseEnd_1097987 := by
    simpa [prefixWord, tailWord_1097987, baseEnd_1097987] using wordTrace_append hprefix tailTrace_1097987
  have hstable : (prefixWord ++ tailWord_1097987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097987).length < 2 ^ (prefixWord ++ tailWord_1097987).sum := by decide
  have hdescent : baseEnd_1097987 < baseStart_1097987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098068 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1098068 : Nat := 118140960795 + 1098068 * 2 ^ 59
def prefixEnd_1098068 : Nat := 4983230072969 + 3 ^ 40 * 1098068 * 2
def baseEnd_1098068 : Nat := 375891116880876691733389

theorem tailTrace_1098068 : CollatzResearch.WordTrace tailWord_1098068 prefixEnd_1098068 375891116880876691733389 := by
  unfold tailWord_1098068
  simp only [CollatzResearch.WordTrace]
  refine ⟨20024915092947322964539429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26699886790596430619385905 20024915092947322964539429)
  ·
    refine ⟨3754671579927623055851143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20024915092947322964539429 3754671579927623055851143)
    ·
      refine ⟨5632007369891434583776715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3754671579927623055851143 5632007369891434583776715)
      ·
        refine ⟨8448011054837151875665073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5632007369891434583776715 8448011054837151875665073)
        ·
          refine ⟨6336008291127863906748805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8448011054837151875665073 6336008291127863906748805)
          ·
            refine ⟨1188001554586474482515401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6336008291127863906748805 1188001554586474482515401)
            ·
              refine ⟨891001165939855861886551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188001554586474482515401 891001165939855861886551)
              ·
                refine ⟨1336501748909783792829827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891001165939855861886551 1336501748909783792829827)
                ·
                  refine ⟨2004752623364675689244741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336501748909783792829827 2004752623364675689244741)
                  ·
                    refine ⟨375891116880876691733389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2004752623364675689244741 375891116880876691733389)
                    ·
                      rfl

theorem cell22_1098068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1098068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098068 prefixEnd_1098068 := by exact prefixLift 1098068
  have htrace : WordTrace (prefixWord ++ tailWord_1098068) baseStart_1098068 baseEnd_1098068 := by
    simpa [prefixWord, tailWord_1098068, baseEnd_1098068] using wordTrace_append hprefix tailTrace_1098068
  have hstable : (prefixWord ++ tailWord_1098068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098068).length < 2 ^ (prefixWord ++ tailWord_1098068).sum := by decide
  have hdescent : baseEnd_1098068 < baseStart_1098068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098098 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_1098098 : Nat := 118140960795 + 1098098 * 2 ^ 59
def prefixEnd_1098098 : Nat := 4983230072969 + 3 ^ 40 * 1098098 * 2
def baseEnd_1098098 : Nat := 375901386493966613483297

theorem tailTrace_1098098 : CollatzResearch.WordTrace tailWord_1098098 prefixEnd_1098098 375901386493966613483297 := by
  unfold tailWord_1098098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012731093946490263167737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26700616250523974035113965 10012731093946490263167737)
  ·
    refine ⟨7509548320459867697375803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10012731093946490263167737 7509548320459867697375803)
    ·
      refine ⟨11264322480689801546063705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509548320459867697375803 11264322480689801546063705)
      ·
        refine ⟨8448241860517351159547779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11264322480689801546063705 8448241860517351159547779)
        ·
          refine ⟨12672362790776026739321669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8448241860517351159547779 12672362790776026739321669)
          ·
            refine ⟨2376068023270505013622813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12672362790776026739321669 2376068023270505013622813)
            ·
              refine ⟨891025508726439380108555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2376068023270505013622813 891025508726439380108555)
              ·
                refine ⟨1336538263089659070162833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891025508726439380108555 1336538263089659070162833)
                ·
                  refine ⟨1002403697317244302622125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1336538263089659070162833 1002403697317244302622125)
                  ·
                    refine ⟨375901386493966613483297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002403697317244302622125 375901386493966613483297)
                    ·
                      rfl

theorem cell22_1098098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_1098098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098098 prefixEnd_1098098 := by exact prefixLift 1098098
  have htrace : WordTrace (prefixWord ++ tailWord_1098098) baseStart_1098098 baseEnd_1098098 := by
    simpa [prefixWord, tailWord_1098098, baseEnd_1098098] using wordTrace_append hprefix tailTrace_1098098
  have hstable : (prefixWord ++ tailWord_1098098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098098).length < 2 ^ (prefixWord ++ tailWord_1098098).sum := by decide
  have hdescent : baseEnd_1098098 < baseStart_1098098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098134 : List Nat := [5, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1098134 : Nat := 118140960795 + 1098134 * 2 ^ 59
def prefixEnd_1098134 : Nat := 4983230072969 + 3 ^ 40 * 1098134 * 2
def baseEnd_1098134 : Nat := 125304570009891506527729

theorem tailTrace_1098134 : CollatzResearch.WordTrace tailWord_1098134 prefixEnd_1098134 125304570009891506527729 := by
  unfold tailWord_1098134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503264837728471200061341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26701491602437026133987637 2503264837728471200061341)
  ·
    refine ⟨938724314148176700023003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2503264837728471200061341 938724314148176700023003)
    ·
      refine ⟨1408086471222265050034505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 938724314148176700023003 1408086471222265050034505)
      ·
        refine ⟨1056064853416698787525879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1408086471222265050034505 1056064853416698787525879)
        ·
          refine ⟨1584097280125048181288819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056064853416698787525879 1584097280125048181288819)
          ·
            refine ⟨2376145920187572271933229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584097280125048181288819 2376145920187572271933229)
            ·
              refine ⟨891054720070339601974961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2376145920187572271933229 891054720070339601974961)
              ·
                refine ⟨668291040052754701481221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891054720070339601974961 668291040052754701481221)
                ·
                  refine ⟨125304570009891506527729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668291040052754701481221 125304570009891506527729)
                  ·
                    rfl

theorem cell22_1098134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1098134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098134 prefixEnd_1098134 := by exact prefixLift 1098134
  have htrace : WordTrace (prefixWord ++ tailWord_1098134) baseStart_1098134 baseEnd_1098134 := by
    simpa [prefixWord, tailWord_1098134, baseEnd_1098134] using wordTrace_append hprefix tailTrace_1098134
  have hstable : (prefixWord ++ tailWord_1098134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098134).length < 2 ^ (prefixWord ++ tailWord_1098134).sum := by decide
  have hdescent : baseEnd_1098134 < baseStart_1098134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098194 : List Nat := [3, 2, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1098194 : Nat := 118140960795 + 1098194 * 2 ^ 59
def prefixEnd_1098194 : Nat := 4983230072969 + 3 ^ 40 * 1098194 * 2
def baseEnd_1098194 : Nat := 375934249255854363083003

theorem tailTrace_1098194 : CollatzResearch.WordTrace tailWord_1098194 prefixEnd_1098194 375934249255854363083003 := by
  unfold tailWord_1098194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10013606445859542362041409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26702950522292112965443757 10013606445859542362041409)
  ·
    refine ⟨7510204834394656771531057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10013606445859542362041409 7510204834394656771531057)
    ·
      refine ⟨5632653625795992578648293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7510204834394656771531057 5632653625795992578648293)
      ·
        refine ⟨1056122554836748608496555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5632653625795992578648293 1056122554836748608496555)
        ·
          refine ⟨1584183832255122912744833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056122554836748608496555 1584183832255122912744833)
          ·
            refine ⟨1188137874191342184558625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584183832255122912744833 1188137874191342184558625)
            ·
              refine ⟨891103405643506638418969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188137874191342184558625 891103405643506638418969)
              ·
                refine ⟨668327554232629978814227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891103405643506638418969 668327554232629978814227)
                ·
                  refine ⟨1002491331348944968221341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668327554232629978814227 1002491331348944968221341)
                  ·
                    refine ⟨375934249255854363083003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002491331348944968221341 375934249255854363083003)
                    ·
                      rfl

theorem cell22_1098194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1098194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098194 prefixEnd_1098194 := by exact prefixLift 1098194
  have htrace : WordTrace (prefixWord ++ tailWord_1098194) baseStart_1098194 baseEnd_1098194 := by
    simpa [prefixWord, tailWord_1098194, baseEnd_1098194] using wordTrace_append hprefix tailTrace_1098194
  have hstable : (prefixWord ++ tailWord_1098194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098194).length < 2 ^ (prefixWord ++ tailWord_1098194).sum := by decide
  have hdescent : baseEnd_1098194 < baseStart_1098194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098201 : List Nat := [1, 2, 1, 2, 4, 1, 3, 4, 4]
def baseStart_1098201 : Nat := 118140960795 + 1098201 * 2 ^ 59
def prefixEnd_1098201 : Nat := 4983230072969 + 3 ^ 40 * 1098201 * 2
def baseEnd_1098201 : Nat := 125312215166302892719327

theorem tailTrace_1098201 : CollatzResearch.WordTrace tailWord_1098201 prefixEnd_1098201 125312215166302892719327 := by
  unfold tailWord_1098201
  simp only [CollatzResearch.WordTrace]
  refine ⟨40054681094412809643670457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26703120729608539762446971 40054681094412809643670457)
  ·
    refine ⟨30041010820809607232752843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40054681094412809643670457 30041010820809607232752843)
    ·
      refine ⟨45061516231214410849129265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30041010820809607232752843 45061516231214410849129265)
      ·
        refine ⟨33796137173410808136846949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45061516231214410849129265 33796137173410808136846949)
        ·
          refine ⟨6336775720014526525658803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33796137173410808136846949 6336775720014526525658803)
          ·
            refine ⟨9505163580021789788488205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336775720014526525658803 9505163580021789788488205)
            ·
              refine ⟨3564436342508171170683077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9505163580021789788488205 3564436342508171170683077)
              ·
                refine ⟨668331814220282094503077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3564436342508171170683077 668331814220282094503077)
                ·
                  refine ⟨125312215166302892719327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668331814220282094503077 125312215166302892719327)
                  ·
                    rfl

theorem cell22_1098201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_1098201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098201 prefixEnd_1098201 := by exact prefixLift 1098201
  have htrace : WordTrace (prefixWord ++ tailWord_1098201) baseStart_1098201 baseEnd_1098201 := by
    simpa [prefixWord, tailWord_1098201, baseEnd_1098201] using wordTrace_append hprefix tailTrace_1098201
  have hstable : (prefixWord ++ tailWord_1098201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098201).length < 2 ^ (prefixWord ++ tailWord_1098201).sum := by decide
  have hdescent : baseEnd_1098201 < baseStart_1098201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098216 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1098216 : Nat := 118140960795 + 1098216 * 2 ^ 59
def prefixEnd_1098216 : Nat := 4983230072969 + 3 ^ 40 * 1098216 * 2
def baseEnd_1098216 : Nat := 375941780305453639032935

theorem tailTrace_1098216 : CollatzResearch.WordTrace tailWord_1098216 prefixEnd_1098216 375941780305453639032935 := by
  unfold tailWord_1098216
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027614094679233602733251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26703485459572311470311001 20027614094679233602733251)
  ·
    refine ⟨30041421142018850404099877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20027614094679233602733251 30041421142018850404099877)
    ·
      refine ⟨5632766464128534450768727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30041421142018850404099877 5632766464128534450768727)
      ·
        refine ⟨8449149696192801676153091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5632766464128534450768727 8449149696192801676153091)
        ·
          refine ⟨12673724544289202514229637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8449149696192801676153091 12673724544289202514229637)
          ·
            refine ⟨2376323352054225471418057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12673724544289202514229637 2376323352054225471418057)
            ·
              refine ⟨1782242514040669103563543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2376323352054225471418057 1782242514040669103563543)
              ·
                refine ⟨2673363771061003655345315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782242514040669103563543 2673363771061003655345315)
                ·
                  refine ⟨4010045656591505483017973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673363771061003655345315 4010045656591505483017973)
                  ·
                    refine ⟨375941780305453639032935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4010045656591505483017973 375941780305453639032935)
                    ·
                      rfl

theorem cell22_1098216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1098216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098216 prefixEnd_1098216 := by exact prefixLift 1098216
  have htrace : WordTrace (prefixWord ++ tailWord_1098216) baseStart_1098216 baseEnd_1098216 := by
    simpa [prefixWord, tailWord_1098216, baseEnd_1098216] using wordTrace_append hprefix tailTrace_1098216
  have hstable : (prefixWord ++ tailWord_1098216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098216).length < 2 ^ (prefixWord ++ tailWord_1098216).sum := by decide
  have hdescent : baseEnd_1098216 < baseStart_1098216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098289 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_1098289 : Nat := 118140960795 + 1098289 * 2 ^ 59
def prefixEnd_1098289 : Nat := 4983230072969 + 3 ^ 40 * 1098289 * 2
def baseEnd_1098289 : Nat := 375966769697305781957711

theorem tailTrace_1098289 : CollatzResearch.WordTrace tailWord_1098289 prefixEnd_1098289 375966769697305781957711 := by
  unfold tailWord_1098289
  simp only [CollatzResearch.WordTrace]
  refine ⟨40057890718094000672873921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26705260478729333781915947 40057890718094000672873921)
  ·
    refine ⟨30043418038570500504655441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40057890718094000672873921 30043418038570500504655441)
    ·
      refine ⟨22532563528927875378491581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30043418038570500504655441 22532563528927875378491581)
      ·
        refine ⟨8449711323347953266934343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22532563528927875378491581 8449711323347953266934343)
        ·
          refine ⟨12674566985021929900401515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8449711323347953266934343 12674566985021929900401515)
          ·
            refine ⟨19011850477532894850602273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12674566985021929900401515 19011850477532894850602273)
            ·
              refine ⟨14258887858149671137951705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19011850477532894850602273 14258887858149671137951705)
              ·
                refine ⟨10694165893612253353463779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14258887858149671137951705 10694165893612253353463779)
                ·
                  refine ⟨16041248840418380030195669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10694165893612253353463779 16041248840418380030195669)
                  ·
                    refine ⟨375966769697305781957711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16041248840418380030195669 375966769697305781957711)
                    ·
                      rfl

theorem cell22_1098289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_1098289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098289 prefixEnd_1098289 := by exact prefixLift 1098289
  have htrace : WordTrace (prefixWord ++ tailWord_1098289) baseStart_1098289 baseEnd_1098289 := by
    simpa [prefixWord, tailWord_1098289, baseEnd_1098289] using wordTrace_append hprefix tailTrace_1098289
  have hstable : (prefixWord ++ tailWord_1098289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098289).length < 2 ^ (prefixWord ++ tailWord_1098289).sum := by decide
  have hdescent : baseEnd_1098289 < baseStart_1098289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098351 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 6, 3]
def baseStart_1098351 : Nat := 118140960795 + 1098351 * 2 ^ 59
def prefixEnd_1098351 : Nat := 4983230072969 + 3 ^ 40 * 1098351 * 2
def baseEnd_1098351 : Nat := 375987993564358286907521

theorem tailTrace_1098351 : CollatzResearch.WordTrace tailWord_1098351 prefixEnd_1098351 375987993564358286907521 := by
  unfold tailWord_1098351
  simp only [CollatzResearch.WordTrace]
  refine ⟨40060152043869385261630907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26706768029246256841087271 40060152043869385261630907)
  ·
    refine ⟨60090228065804077892446361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40060152043869385261630907 60090228065804077892446361)
    ·
      refine ⟨45067671049353058419334771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60090228065804077892446361 45067671049353058419334771)
      ·
        refine ⟨67601506574029587629002157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45067671049353058419334771 67601506574029587629002157)
        ·
          refine ⟨25350564965261095360875809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67601506574029587629002157 25350564965261095360875809)
          ·
            refine ⟨19012923723945821520656857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25350564965261095360875809 19012923723945821520656857)
            ·
              refine ⟨14259692792959366140492643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19012923723945821520656857 14259692792959366140492643)
              ·
                refine ⟨21389539189439049210738965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14259692792959366140492643 21389539189439049210738965)
                ·
                  refine ⟨1002634649504955431753389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21389539189439049210738965 1002634649504955431753389)
                  ·
                    refine ⟨375987993564358286907521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002634649504955431753389 375987993564358286907521)
                    ·
                      rfl

theorem cell22_1098351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_1098351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098351 prefixEnd_1098351 := by exact prefixLift 1098351
  have htrace : WordTrace (prefixWord ++ tailWord_1098351) baseStart_1098351 baseEnd_1098351 := by
    simpa [prefixWord, tailWord_1098351, baseEnd_1098351] using wordTrace_append hprefix tailTrace_1098351
  have hstable : (prefixWord ++ tailWord_1098351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098351).length < 2 ^ (prefixWord ++ tailWord_1098351).sum := by decide
  have hdescent : baseEnd_1098351 < baseStart_1098351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098368 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 2, 3]
def baseStart_1098368 : Nat := 118140960795 + 1098368 * 2 ^ 59
def prefixEnd_1098368 : Nat := 4983230072969 + 3 ^ 40 * 1098368 * 2
def baseEnd_1098368 : Nat := 375993813011775909232469

theorem tailTrace_1098368 : CollatzResearch.WordTrace tailWord_1098368 prefixEnd_1098368 375993813011775909232469 := by
  unfold tailWord_1098368
  simp only [CollatzResearch.WordTrace]
  refine ⟨20030386042403898582499879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26707181389871864776666505 20030386042403898582499879)
  ·
    refine ⟨30045579063605847873749819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20030386042403898582499879 30045579063605847873749819)
    ·
      refine ⟨45068368595408771810624729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30045579063605847873749819 45068368595408771810624729)
      ·
        refine ⟨33801276446556578857968547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45068368595408771810624729 33801276446556578857968547)
        ·
          refine ⟨50701914669834868286952821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33801276446556578857968547 50701914669834868286952821)
          ·
            refine ⟨4753304500297018901901827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50701914669834868286952821 4753304500297018901901827)
            ·
              refine ⟨7129956750445528352852741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753304500297018901901827 7129956750445528352852741)
              ·
                refine ⟨1336866890708536566159889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7129956750445528352852741 1336866890708536566159889)
                ·
                  refine ⟨1002650168031402424619917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1336866890708536566159889 1002650168031402424619917)
                  ·
                    refine ⟨375993813011775909232469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002650168031402424619917 375993813011775909232469)
                    ·
                      rfl

theorem cell22_1098368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_1098368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098368 prefixEnd_1098368 := by exact prefixLift 1098368
  have htrace : WordTrace (prefixWord ++ tailWord_1098368) baseStart_1098368 baseEnd_1098368 := by
    simpa [prefixWord, tailWord_1098368, baseEnd_1098368] using wordTrace_append hprefix tailTrace_1098368
  have hstable : (prefixWord ++ tailWord_1098368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098368).length < 2 ^ (prefixWord ++ tailWord_1098368).sum := by decide
  have hdescent : baseEnd_1098368 < baseStart_1098368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098400 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 2, 4]
def baseStart_1098400 : Nat := 118140960795 + 1098400 * 2 ^ 59
def prefixEnd_1098400 : Nat := 4983230072969 + 3 ^ 40 * 1098400 * 2
def baseEnd_1098400 : Nat := 376004767265738492432371

theorem tailTrace_1098400 : CollatzResearch.WordTrace tailWord_1098400 prefixEnd_1098400 376004767265738492432371 := by
  unfold tailWord_1098400
  simp only [CollatzResearch.WordTrace]
  refine ⟨20030969610345933315082327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26707959480461244420109769 20030969610345933315082327)
  ·
    refine ⟨30046454415518899972623491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20030969610345933315082327 30046454415518899972623491)
    ·
      refine ⟨45069681623278349958935237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30046454415518899972623491 45069681623278349958935237)
      ·
        refine ⟨8450565304364690617300357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45069681623278349958935237 8450565304364690617300357)
        ·
          refine ⟨1584480994568379490743817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8450565304364690617300357 1584480994568379490743817)
          ·
            refine ⟨1188360745926284618057863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584480994568379490743817 1188360745926284618057863)
            ·
              refine ⟨1782541118889426927086795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188360745926284618057863 1782541118889426927086795)
              ·
                refine ⟨2673811678334140390630193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782541118889426927086795 2673811678334140390630193)
                ·
                  refine ⟨2005358758750605292972645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2673811678334140390630193 2005358758750605292972645)
                  ·
                    refine ⟨376004767265738492432371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2005358758750605292972645 376004767265738492432371)
                    ·
                      rfl

theorem cell22_1098400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_1098400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098400 prefixEnd_1098400 := by exact prefixLift 1098400
  have htrace : WordTrace (prefixWord ++ tailWord_1098400) baseStart_1098400 baseEnd_1098400 := by
    simpa [prefixWord, tailWord_1098400, baseEnd_1098400] using wordTrace_append hprefix tailTrace_1098400
  have hstable : (prefixWord ++ tailWord_1098400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098400).length < 2 ^ (prefixWord ++ tailWord_1098400).sum := by decide
  have hdescent : baseEnd_1098400 < baseStart_1098400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098426 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_1098426 : Nat := 118140960795 + 1098426 * 2 ^ 59
def prefixEnd_1098426 : Nat := 4983230072969 + 3 ^ 40 * 1098426 * 2
def baseEnd_1098426 : Nat := 125337889199027697094097

theorem tailTrace_1098426 : CollatzResearch.WordTrace tailWord_1098426 prefixEnd_1098426 125337889199027697094097 := by
  unfold tailWord_1098426
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015721879649418267652783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26708591679065115380407421 10015721879649418267652783)
  ·
    refine ⟨15023582819474127401479175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10015721879649418267652783 15023582819474127401479175)
    ·
      refine ⟨22535374229211191102218763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15023582819474127401479175 22535374229211191102218763)
      ·
        refine ⟨33803061343816786653328145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22535374229211191102218763 33803061343816786653328145)
        ·
          refine ⟨25352296007862589989996109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33803061343816786653328145 25352296007862589989996109)
          ·
            refine ⟨9507111002948471246248541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25352296007862589989996109 9507111002948471246248541)
            ·
              refine ⟨3565166626105676717343203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9507111002948471246248541 3565166626105676717343203)
              ·
                refine ⟨5347749939158515076014805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565166626105676717343203 5347749939158515076014805)
                ·
                  refine ⟨125337889199027697094097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5347749939158515076014805 125337889199027697094097)
                  ·
                    rfl

theorem cell22_1098426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_1098426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098426 prefixEnd_1098426 := by exact prefixLift 1098426
  have htrace : WordTrace (prefixWord ++ tailWord_1098426) baseStart_1098426 baseEnd_1098426 := by
    simpa [prefixWord, tailWord_1098426, baseEnd_1098426] using wordTrace_append hprefix tailTrace_1098426
  have hstable : (prefixWord ++ tailWord_1098426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098426).length < 2 ^ (prefixWord ++ tailWord_1098426).sum := by decide
  have hdescent : baseEnd_1098426 < baseStart_1098426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098430 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1098430 : Nat := 118140960795 + 1098430 * 2 ^ 59
def prefixEnd_1098430 : Nat := 4983230072969 + 3 ^ 40 * 1098430 * 2
def baseEnd_1098430 : Nat := 376015036878828414182279

theorem tailTrace_1098430 : CollatzResearch.WordTrace tailWord_1098430 prefixEnd_1098430 376015036878828414182279 := by
  unfold tailWord_1098430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007879176322897719219593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26708688940388787835837829 5007879176322897719219593)
  ·
    refine ⟨3755909382242173289414695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5007879176322897719219593 3755909382242173289414695)
    ·
      refine ⟨5633864073363259934122043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3755909382242173289414695 5633864073363259934122043)
      ·
        refine ⟨8450796110044889901183065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5633864073363259934122043 8450796110044889901183065)
        ·
          refine ⟨6338097082533667425887299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8450796110044889901183065 6338097082533667425887299)
          ·
            refine ⟨9507145623800501138830949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338097082533667425887299 9507145623800501138830949)
            ·
              refine ⟨1782589804462593963530803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9507145623800501138830949 1782589804462593963530803)
              ·
                refine ⟨2673884706693890945296205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782589804462593963530803 2673884706693890945296205)
                ·
                  refine ⟨1002706765010209104486077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2673884706693890945296205 1002706765010209104486077)
                  ·
                    refine ⟨376015036878828414182279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002706765010209104486077 376015036878828414182279)
                    ·
                      rfl

theorem cell22_1098430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1098430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098430 prefixEnd_1098430 := by exact prefixLift 1098430
  have htrace : WordTrace (prefixWord ++ tailWord_1098430) baseStart_1098430 baseEnd_1098430 := by
    simpa [prefixWord, tailWord_1098430, baseEnd_1098430] using wordTrace_append hprefix tailTrace_1098430
  have hstable : (prefixWord ++ tailWord_1098430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098430).length < 2 ^ (prefixWord ++ tailWord_1098430).sum := by decide
  have hdescent : baseEnd_1098430 < baseStart_1098430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098473 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_1098473 : Nat := 118140960795 + 1098473 * 2 ^ 59
def prefixEnd_1098473 : Nat := 4983230072969 + 3 ^ 40 * 1098473 * 2
def baseEnd_1098473 : Nat := 376029756657590635357147

theorem tailTrace_1098473 : CollatzResearch.WordTrace tailWord_1098473 prefixEnd_1098473 376029756657590635357147 := by
  unfold tailWord_1098473
  simp only [CollatzResearch.WordTrace]
  refine ⟨40064601749427400097572073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26709734499618266731714715 40064601749427400097572073)
  ·
    refine ⟨30048451312070550073179055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40064601749427400097572073 30048451312070550073179055)
    ·
      refine ⟨45072676968105825109768583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30048451312070550073179055 45072676968105825109768583)
      ·
        refine ⟨67609015452158737664652875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45072676968105825109768583 67609015452158737664652875)
        ·
          refine ⟨101413523178238106496979313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67609015452158737664652875 101413523178238106496979313)
          ·
            refine ⟨76060142383678579872734485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101413523178238106496979313 76060142383678579872734485)
            ·
              refine ⟨3565319174234933431534429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76060142383678579872734485 3565319174234933431534429)
              ·
                refine ⟨1336994690338100036825411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3565319174234933431534429 1336994690338100036825411)
                ·
                  refine ⟨2005492035507150055238117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336994690338100036825411 2005492035507150055238117)
                  ·
                    refine ⟨376029756657590635357147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2005492035507150055238117 376029756657590635357147)
                    ·
                      rfl

theorem cell22_1098473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_1098473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098473 prefixEnd_1098473 := by exact prefixLift 1098473
  have htrace : WordTrace (prefixWord ++ tailWord_1098473) baseStart_1098473 baseEnd_1098473 := by
    simpa [prefixWord, tailWord_1098473, baseEnd_1098473] using wordTrace_append hprefix tailTrace_1098473
  have hstable : (prefixWord ++ tailWord_1098473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098473).length < 2 ^ (prefixWord ++ tailWord_1098473).sum := by decide
  have hdescent : baseEnd_1098473 < baseStart_1098473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098501 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1098501 : Nat := 118140960795 + 1098501 * 2 ^ 59
def prefixEnd_1098501 : Nat := 4983230072969 + 3 ^ 40 * 1098501 * 2
def baseEnd_1098501 : Nat := 376039341629807895657061

theorem tailTrace_1098501 : CollatzResearch.WordTrace tailWord_1098501 prefixEnd_1098501 376039341629807895657061 := by
  unfold tailWord_1098501
  simp only [CollatzResearch.WordTrace]
  refine ⟨40065622993325960879591357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26710415328883973919727571 40065622993325960879591357)
  ·
    refine ⟨15024608622497235329846759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40065622993325960879591357 15024608622497235329846759)
    ·
      refine ⟨22536912933745852994770139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15024608622497235329846759 22536912933745852994770139)
      ·
        refine ⟨33805369400618779492155209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22536912933745852994770139 33805369400618779492155209)
        ·
          refine ⟨25354027050464084619116407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33805369400618779492155209 25354027050464084619116407)
          ·
            refine ⟨38031040575696126928674611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25354027050464084619116407 38031040575696126928674611)
            ·
              refine ⟨57046560863544190393011917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38031040575696126928674611 57046560863544190393011917)
              ·
                refine ⟨21392460323829071397379469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57046560863544190393011917 21392460323829071397379469)
                ·
                  refine ⟨8022172621435901774017301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21392460323829071397379469 8022172621435901774017301)
                  ·
                    refine ⟨376039341629807895657061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8022172621435901774017301 376039341629807895657061)
                    ·
                      rfl

theorem cell22_1098501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1098501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098501 prefixEnd_1098501 := by exact prefixLift 1098501
  have htrace : WordTrace (prefixWord ++ tailWord_1098501) baseStart_1098501 baseEnd_1098501 := by
    simpa [prefixWord, tailWord_1098501, baseEnd_1098501] using wordTrace_append hprefix tailTrace_1098501
  have hstable : (prefixWord ++ tailWord_1098501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098501).length < 2 ^ (prefixWord ++ tailWord_1098501).sum := by decide
  have hdescent : baseEnd_1098501 < baseStart_1098501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098578 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1098578 : Nat := 118140960795 + 1098578 * 2 ^ 59
def prefixEnd_1098578 : Nat := 4983230072969 + 3 ^ 40 * 1098578 * 2
def baseEnd_1098578 : Nat := 125355233434468453827275

theorem tailTrace_1098578 : CollatzResearch.WordTrace tailWord_1098578 prefixEnd_1098578 125355233434468453827275 := by
  unfold tailWord_1098578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017107853511750757536097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26712287609364668686762925 10017107853511750757536097)
  ·
    refine ⟨7512830890133813068152073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10017107853511750757536097 7512830890133813068152073)
    ·
      refine ⟨5634623167600359801114055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7512830890133813068152073 5634623167600359801114055)
      ·
        refine ⟨8451934751400539701671083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5634623167600359801114055 8451934751400539701671083)
        ·
          refine ⟨12677902127100809552506625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8451934751400539701671083 12677902127100809552506625)
          ·
            refine ⟨9508426595325607164379969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12677902127100809552506625 9508426595325607164379969)
            ·
              refine ⟨7131319946494205373284977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9508426595325607164379969 7131319946494205373284977)
              ·
                refine ⟨5348489959870654029963733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7131319946494205373284977 5348489959870654029963733)
                ·
                  refine ⟨125355233434468453827275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5348489959870654029963733 125355233434468453827275)
                  ·
                    rfl

theorem cell22_1098578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1098578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098578 prefixEnd_1098578 := by exact prefixLift 1098578
  have htrace : WordTrace (prefixWord ++ tailWord_1098578) baseStart_1098578 baseEnd_1098578 := by
    simpa [prefixWord, tailWord_1098578, baseEnd_1098578] using wordTrace_append hprefix tailTrace_1098578
  have hstable : (prefixWord ++ tailWord_1098578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098578).length < 2 ^ (prefixWord ++ tailWord_1098578).sum := by decide
  have hdescent : baseEnd_1098578 < baseStart_1098578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098595 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 5]
def baseStart_1098595 : Nat := 118140960795 + 1098595 * 2 ^ 59
def prefixEnd_1098595 : Nat := 4983230072969 + 3 ^ 40 * 1098595 * 2
def baseEnd_1098595 : Nat := 125357173250274327935591

theorem tailTrace_1098595 : CollatzResearch.WordTrace tailWord_1098595 prefixEnd_1098595 125357173250274327935591 := by
  unfold tailWord_1098595
  simp only [CollatzResearch.WordTrace]
  refine ⟨40069051454985414933513239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26712700969990276622342159 40069051454985414933513239)
  ·
    refine ⟨60103577182478122400269859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40069051454985414933513239 60103577182478122400269859)
    ·
      refine ⟨90155365773717183600404789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60103577182478122400269859 90155365773717183600404789)
      ·
        refine ⟨8452065541285985962537949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90155365773717183600404789 8452065541285985962537949)
        ·
          refine ⟨3169524577982244735951731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8452065541285985962537949 3169524577982244735951731)
          ·
            refine ⟨4754286866973367103927597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169524577982244735951731 4754286866973367103927597)
            ·
              refine ⟨1782857575115012663972849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4754286866973367103927597 1782857575115012663972849)
              ·
                refine ⟨1337143181336259497979637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782857575115012663972849 1337143181336259497979637)
                ·
                  refine ⟨125357173250274327935591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1337143181336259497979637 125357173250274327935591)
                  ·
                    rfl

theorem cell22_1098595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 5].length) (baseStart_1098595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098595 prefixEnd_1098595 := by exact prefixLift 1098595
  have htrace : WordTrace (prefixWord ++ tailWord_1098595) baseStart_1098595 baseEnd_1098595 := by
    simpa [prefixWord, tailWord_1098595, baseEnd_1098595] using wordTrace_append hprefix tailTrace_1098595
  have hstable : (prefixWord ++ tailWord_1098595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098595).length < 2 ^ (prefixWord ++ tailWord_1098595).sum := by decide
  have hdescent : baseEnd_1098595 < baseStart_1098595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098608 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_1098608 : Nat := 118140960795 + 1098608 * 2 ^ 59
def prefixEnd_1098608 : Nat := 4983230072969 + 3 ^ 40 * 1098608 * 2
def baseEnd_1098608 : Nat := 376075969916495283231733

theorem tailTrace_1098608 : CollatzResearch.WordTrace tailWord_1098608 prefixEnd_1098608 376075969916495283231733 := by
  unfold tailWord_1098608
  simp only [CollatzResearch.WordTrace]
  refine ⟨20034762801969159076868239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26713017069292212102490985 20034762801969159076868239)
  ·
    refine ⟨30052144202953738615302359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20034762801969159076868239 30052144202953738615302359)
    ·
      refine ⟨45078216304430607922953539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30052144202953738615302359 45078216304430607922953539)
      ·
        refine ⟨67617324456645911884430309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45078216304430607922953539 67617324456645911884430309)
        ·
          refine ⟨12678248335621108478330683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67617324456645911884430309 12678248335621108478330683)
          ·
            refine ⟨19017372503431662717496025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12678248335621108478330683 19017372503431662717496025)
            ·
              refine ⟨14263029377573747038122019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19017372503431662717496025 14263029377573747038122019)
              ·
                refine ⟨21394544066360620557183029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14263029377573747038122019 21394544066360620557183029)
                ·
                  refine ⟨2005738506221308177235909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21394544066360620557183029 2005738506221308177235909)
                  ·
                    refine ⟨376075969916495283231733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2005738506221308177235909 376075969916495283231733)
                    ·
                      rfl

theorem cell22_1098608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_1098608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098608 prefixEnd_1098608 := by exact prefixLift 1098608
  have htrace : WordTrace (prefixWord ++ tailWord_1098608) baseStart_1098608 baseEnd_1098608 := by
    simpa [prefixWord, tailWord_1098608, baseEnd_1098608] using wordTrace_append hprefix tailTrace_1098608
  have hstable : (prefixWord ++ tailWord_1098608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098608).length < 2 ^ (prefixWord ++ tailWord_1098608).sum := by decide
  have hdescent : baseEnd_1098608 < baseStart_1098608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098623 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 6]
def baseStart_1098623 : Nat := 118140960795 + 1098623 * 2 ^ 59
def prefixEnd_1098623 : Nat := 4983230072969 + 3 ^ 40 * 1098623 * 2
def baseEnd_1098623 : Nat := 125360368241013414702229

theorem tailTrace_1098623 : CollatzResearch.WordTrace tailWord_1098623 prefixEnd_1098623 125360368241013414702229 := by
  unfold tailWord_1098623
  simp only [CollatzResearch.WordTrace]
  refine ⟨40070072698883975715532523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26713381799255983810355015 40070072698883975715532523)
  ·
    refine ⟨60105109048325963573298785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40070072698883975715532523 60105109048325963573298785)
    ·
      refine ⟨45078831786244472679974089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60105109048325963573298785 45078831786244472679974089)
      ·
        refine ⟨33809123839683354509980567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45078831786244472679974089 33809123839683354509980567)
        ·
          refine ⟨50713685759525031764970851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33809123839683354509980567 50713685759525031764970851)
          ·
            refine ⟨76070528639287547647456277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50713685759525031764970851 76070528639287547647456277)
            ·
              refine ⟨3565806029966603795974513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76070528639287547647456277 3565806029966603795974513)
              ·
                refine ⟨2674354522474952846980885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3565806029966603795974513 2674354522474952846980885)
                ·
                  refine ⟨125360368241013414702229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2674354522474952846980885 125360368241013414702229)
                  ·
                    rfl

theorem cell22_1098623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 6].length) (baseStart_1098623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098623 prefixEnd_1098623 := by exact prefixLift 1098623
  have htrace : WordTrace (prefixWord ++ tailWord_1098623) baseStart_1098623 baseEnd_1098623 := by
    simpa [prefixWord, tailWord_1098623, baseEnd_1098623] using wordTrace_append hprefix tailTrace_1098623
  have hstable : (prefixWord ++ tailWord_1098623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098623).length < 2 ^ (prefixWord ++ tailWord_1098623).sum := by decide
  have hdescent : baseEnd_1098623 < baseStart_1098623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098657 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 6]
def baseStart_1098657 : Nat := 118140960795 + 1098657 * 2 ^ 59
def prefixEnd_1098657 : Nat := 4983230072969 + 3 ^ 40 * 1098657 * 2
def baseEnd_1098657 : Nat := 125364247872625162918861

theorem tailTrace_1098657 : CollatzResearch.WordTrace tailWord_1098657 prefixEnd_1098657 125364247872625162918861 := by
  unfold tailWord_1098657
  simp only [CollatzResearch.WordTrace]
  refine ⟨40071312780760799522270225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26714208520507199681513483 40071312780760799522270225)
  ·
    refine ⟨30053484585570599641702669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40071312780760799522270225 30053484585570599641702669)
    ·
      refine ⟨11270056719588974865638501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30053484585570599641702669 11270056719588974865638501)
      ·
        refine ⟨2113135634922932787307219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11270056719588974865638501 2113135634922932787307219)
        ·
          refine ⟨3169703452384399180960829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113135634922932787307219 3169703452384399180960829)
          ·
            refine ⟨1188638794644149692860311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3169703452384399180960829 1188638794644149692860311)
            ·
              refine ⟨1782958191966224539290467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188638794644149692860311 1782958191966224539290467)
              ·
                refine ⟨2674437287949336808935701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782958191966224539290467 2674437287949336808935701)
                ·
                  refine ⟨125364247872625162918861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2674437287949336808935701 125364247872625162918861)
                  ·
                    rfl

theorem cell22_1098657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_1098657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098657 prefixEnd_1098657 := by exact prefixLift 1098657
  have htrace : WordTrace (prefixWord ++ tailWord_1098657) baseStart_1098657 baseEnd_1098657 := by
    simpa [prefixWord, tailWord_1098657, baseEnd_1098657] using wordTrace_append hprefix tailTrace_1098657
  have hstable : (prefixWord ++ tailWord_1098657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098657).length < 2 ^ (prefixWord ++ tailWord_1098657).sum := by decide
  have hdescent : baseEnd_1098657 < baseStart_1098657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098676 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1098676 : Nat := 118140960795 + 1098676 * 2 ^ 59
def prefixEnd_1098676 : Nat := 4983230072969 + 3 ^ 40 * 1098676 * 2
def baseEnd_1098676 : Nat := 376099247706165772531525

theorem tailTrace_1098676 : CollatzResearch.WordTrace tailWord_1098676 prefixEnd_1098676 376099247706165772531525 := by
  unfold tailWord_1098676
  simp only [CollatzResearch.WordTrace]
  refine ⟨20036002883845982883605941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26714670511794643844807921 20036002883845982883605941)
  ·
    refine ⟨1878375270360560895338057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20036002883845982883605941 1878375270360560895338057)
    ·
      refine ⟨1408781452770420671503543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1878375270360560895338057 1408781452770420671503543)
      ·
        refine ⟨2113172179155631007255315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408781452770420671503543 2113172179155631007255315)
        ·
          refine ⟨3169758268733446510882973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113172179155631007255315 3169758268733446510882973)
          ·
            refine ⟨1188659350775042441581115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3169758268733446510882973 1188659350775042441581115)
            ·
              refine ⟨1782989026162563662371673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188659350775042441581115 1782989026162563662371673)
              ·
                refine ⟨1337241769621922746778755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782989026162563662371673 1337241769621922746778755)
                ·
                  refine ⟨2005862654432884120168133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337241769621922746778755 2005862654432884120168133)
                  ·
                    refine ⟨376099247706165772531525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2005862654432884120168133 376099247706165772531525)
                    ·
                      rfl

theorem cell22_1098676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1098676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098676 prefixEnd_1098676 := by exact prefixLift 1098676
  have htrace : WordTrace (prefixWord ++ tailWord_1098676) baseStart_1098676 baseEnd_1098676 := by
    simpa [prefixWord, tailWord_1098676, baseEnd_1098676] using wordTrace_append hprefix tailTrace_1098676
  have hstable : (prefixWord ++ tailWord_1098676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098676).length < 2 ^ (prefixWord ++ tailWord_1098676).sum := by decide
  have hdescent : baseEnd_1098676 < baseStart_1098676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098734 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1098734 : Nat := 118140960795 + 1098734 * 2 ^ 59
def prefixEnd_1098734 : Nat := 4983230072969 + 3 ^ 40 * 1098734 * 2
def baseEnd_1098734 : Nat := 376119102291472954581347

theorem tailTrace_1098734 : CollatzResearch.WordTrace tailWord_1098734 prefixEnd_1098734 376119102291472954581347 := by
  unfold tailWord_1098734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5009265150185230209102907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26716080800987894448548837 5009265150185230209102907)
  ·
    refine ⟨7513897725277845313654361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5009265150185230209102907 7513897725277845313654361)
    ·
      refine ⟨5635423293958383985240771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7513897725277845313654361 5635423293958383985240771)
      ·
        refine ⟨8453134940937575977861157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5635423293958383985240771 8453134940937575977861157)
        ·
          refine ⟨1584962801425795495848967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8453134940937575977861157 1584962801425795495848967)
          ·
            refine ⟨2377444202138693243773451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584962801425795495848967 2377444202138693243773451)
            ·
              refine ⟨3566166303208039865660177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377444202138693243773451 3566166303208039865660177)
              ·
                refine ⟨2674624727406029899245133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566166303208039865660177 2674624727406029899245133)
                ·
                  refine ⟨1002984272777261212216925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2674624727406029899245133 1002984272777261212216925)
                  ·
                    refine ⟨376119102291472954581347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002984272777261212216925 376119102291472954581347)
                    ·
                      rfl

theorem cell22_1098734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1098734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098734 prefixEnd_1098734 := by exact prefixLift 1098734
  have htrace : WordTrace (prefixWord ++ tailWord_1098734) baseStart_1098734 baseEnd_1098734 := by
    simpa [prefixWord, tailWord_1098734, baseEnd_1098734] using wordTrace_append hprefix tailTrace_1098734
  have hstable : (prefixWord ++ tailWord_1098734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098734).length < 2 ^ (prefixWord ++ tailWord_1098734).sum := by decide
  have hdescent : baseEnd_1098734 < baseStart_1098734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098809 : List Nat := [1, 2, 1, 5, 2, 1, 3, 3, 4]
def baseStart_1098809 : Nat := 118140960795 + 1098809 * 2 ^ 59
def prefixEnd_1098809 : Nat := 4983230072969 + 3 ^ 40 * 1098809 * 2
def baseEnd_1098809 : Nat := 125381592108065919652039

theorem tailTrace_1098809 : CollatzResearch.WordTrace tailWord_1098809 prefixEnd_1098809 125381592108065919652039 := by
  unfold tailWord_1098809
  simp only [CollatzResearch.WordTrace]
  refine ⟨40076856676210129481803481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26717904450806752987868987 40076856676210129481803481)
  ·
    refine ⟨30057642507157597111352611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40076856676210129481803481 30057642507157597111352611)
    ·
      refine ⟨45086463760736395667028917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30057642507157597111352611 45086463760736395667028917)
      ·
        refine ⟨4226855977569037093783961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45086463760736395667028917 4226855977569037093783961)
        ·
          refine ⟨3170141983176777820337971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4226855977569037093783961 3170141983176777820337971)
          ·
            refine ⟨4755212974765166730506957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170141983176777820337971 4755212974765166730506957)
            ·
              refine ⟨1783204865536937523940109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4755212974765166730506957 1783204865536937523940109)
              ·
                refine ⟨668701824576351571477541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783204865536937523940109 668701824576351571477541)
                ·
                  refine ⟨125381592108065919652039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668701824576351571477541 125381592108065919652039)
                  ·
                    rfl

theorem cell22_1098809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_1098809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098809 prefixEnd_1098809 := by exact prefixLift 1098809
  have htrace : WordTrace (prefixWord ++ tailWord_1098809) baseStart_1098809 baseEnd_1098809 := by
    simpa [prefixWord, tailWord_1098809, baseEnd_1098809] using wordTrace_append hprefix tailTrace_1098809
  have hstable : (prefixWord ++ tailWord_1098809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098809).length < 2 ^ (prefixWord ++ tailWord_1098809).sum := by decide
  have hdescent : baseEnd_1098809 < baseStart_1098809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098852 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_1098852 : Nat := 118140960795 + 1098852 * 2 ^ 59
def prefixEnd_1098852 : Nat := 4983230072969 + 3 ^ 40 * 1098852 * 2
def baseEnd_1098852 : Nat := 376159496102959980130985

theorem tailTrace_1098852 : CollatzResearch.WordTrace tailWord_1098852 prefixEnd_1098852 376159496102959980130985 := by
  unfold tailWord_1098852
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039212507527173912809405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26718950010036231883745873 20039212507527173912809405)
  ·
    refine ⟨7514704690322690217303527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20039212507527173912809405 7514704690322690217303527)
    ·
      refine ⟨11272057035484035325955291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7514704690322690217303527 11272057035484035325955291)
      ·
        refine ⟨16908085553226052988932937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272057035484035325955291 16908085553226052988932937)
        ·
          refine ⟨12681064164919539741699703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16908085553226052988932937 12681064164919539741699703)
          ·
            refine ⟨19021596247379309612549555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12681064164919539741699703 19021596247379309612549555)
            ·
              refine ⟨28532394371068964418824333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19021596247379309612549555 28532394371068964418824333)
              ·
                refine ⟨10699647889150861657059125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28532394371068964418824333 10699647889150861657059125)
                ·
                  refine ⟨1003091989607893280349293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10699647889150861657059125 1003091989607893280349293)
                  ·
                    refine ⟨376159496102959980130985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1003091989607893280349293 376159496102959980130985)
                    ·
                      rfl

theorem cell22_1098852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_1098852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098852 prefixEnd_1098852 := by exact prefixLift 1098852
  have htrace : WordTrace (prefixWord ++ tailWord_1098852) baseStart_1098852 baseEnd_1098852 := by
    simpa [prefixWord, tailWord_1098852, baseEnd_1098852] using wordTrace_append hprefix tailTrace_1098852
  have hstable : (prefixWord ++ tailWord_1098852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098852).length < 2 ^ (prefixWord ++ tailWord_1098852).sum := by decide
  have hdescent : baseEnd_1098852 < baseStart_1098852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098856 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1098856 : Nat := 118140960795 + 1098856 * 2 ^ 59
def prefixEnd_1098856 : Nat := 4983230072969 + 3 ^ 40 * 1098856 * 2
def baseEnd_1098856 : Nat := 376160865384705303030973

theorem tailTrace_1098856 : CollatzResearch.WordTrace tailWord_1098856 prefixEnd_1098856 376160865384705303030973 := by
  unfold tailWord_1098856
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039285453519928254382211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26719047271359904339176281 20039285453519928254382211)
  ·
    refine ⟨30058928180279892381573317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20039285453519928254382211 30058928180279892381573317)
    ·
      refine ⟨5636049033802479821544997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30058928180279892381573317 5636049033802479821544997)
      ·
        refine ⟨1056759193837964966539687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5636049033802479821544997 1056759193837964966539687)
        ·
          refine ⟨1585138790756947449809531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056759193837964966539687 1585138790756947449809531)
          ·
            refine ⟨2377708186135421174714297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585138790756947449809531 2377708186135421174714297)
            ·
              refine ⟨1783281139601565881035723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2377708186135421174714297 1783281139601565881035723)
              ·
                refine ⟨2674921709402348821553585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783281139601565881035723 2674921709402348821553585)
                ·
                  refine ⟨2006191282051761616165189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2674921709402348821553585 2006191282051761616165189)
                  ·
                    refine ⟨376160865384705303030973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2006191282051761616165189 376160865384705303030973)
                    ·
                      rfl

theorem cell22_1098856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1098856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098856 prefixEnd_1098856 := by exact prefixLift 1098856
  have htrace : WordTrace (prefixWord ++ tailWord_1098856) baseStart_1098856 baseEnd_1098856 := by
    simpa [prefixWord, tailWord_1098856, baseEnd_1098856] using wordTrace_append hprefix tailTrace_1098856
  have hstable : (prefixWord ++ tailWord_1098856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098856).length < 2 ^ (prefixWord ++ tailWord_1098856).sum := by decide
  have hdescent : baseEnd_1098856 < baseStart_1098856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098865 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 7]
def baseStart_1098865 : Nat := 118140960795 + 1098865 * 2 ^ 59
def prefixEnd_1098865 : Nat := 4983230072969 + 3 ^ 40 * 1098865 * 2
def baseEnd_1098865 : Nat := 125387982089544093185315

theorem tailTrace_1098865 : CollatzResearch.WordTrace tailWord_1098865 prefixEnd_1098865 125387982089544093185315 := by
  unfold tailWord_1098865
  simp only [CollatzResearch.WordTrace]
  refine ⟨40078899164007251045842049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26719266109338167363894699 40078899164007251045842049)
  ·
    refine ⟨30059174373005438284381537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40078899164007251045842049 30059174373005438284381537)
    ·
      refine ⟨22544380779754078713286153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30059174373005438284381537 22544380779754078713286153)
      ·
        refine ⟨16908285584815559034964615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22544380779754078713286153 16908285584815559034964615)
        ·
          refine ⟨25362428377223338552446923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16908285584815559034964615 25362428377223338552446923)
          ·
            refine ⟨38043642565835007828670385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25362428377223338552446923 38043642565835007828670385)
            ·
              refine ⟨28532731924376255871502789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38043642565835007828670385 28532731924376255871502789)
              ·
                refine ⟨5349887235820547975906773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28532731924376255871502789 5349887235820547975906773)
                ·
                  refine ⟨125387982089544093185315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5349887235820547975906773 125387982089544093185315)
                  ·
                    rfl

theorem cell22_1098865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_1098865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098865 prefixEnd_1098865 := by exact prefixLift 1098865
  have htrace : WordTrace (prefixWord ++ tailWord_1098865) baseStart_1098865 baseEnd_1098865 := by
    simpa [prefixWord, tailWord_1098865, baseEnd_1098865] using wordTrace_append hprefix tailTrace_1098865
  have hstable : (prefixWord ++ tailWord_1098865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098865).length < 2 ^ (prefixWord ++ tailWord_1098865).sum := by decide
  have hdescent : baseEnd_1098865 < baseStart_1098865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098912 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_1098912 : Nat := 118140960795 + 1098912 * 2 ^ 59
def prefixEnd_1098912 : Nat := 4983230072969 + 3 ^ 40 * 1098912 * 2
def baseEnd_1098912 : Nat := 376180035329139823630801

theorem tailTrace_1098912 : CollatzResearch.WordTrace tailWord_1098912 prefixEnd_1098912 376180035329139823630801 := by
  unfold tailWord_1098912
  simp only [CollatzResearch.WordTrace]
  refine ⟨20040306697418489036401495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26720408929891318715201993 20040306697418489036401495)
  ·
    refine ⟨30060460046127733554602243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20040306697418489036401495 30060460046127733554602243)
    ·
      refine ⟨45090690069191600331903365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30060460046127733554602243 45090690069191600331903365)
      ·
        refine ⟨8454504387973425062231881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45090690069191600331903365 8454504387973425062231881)
        ·
          refine ⟨6340878290980068796673911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8454504387973425062231881 6340878290980068796673911)
          ·
            refine ⟨9511317436470103195010867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6340878290980068796673911 9511317436470103195010867)
            ·
              refine ⟨14266976154705154792516301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9511317436470103195010867 14266976154705154792516301)
              ·
                refine ⟨5350116058014433047193613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14266976154705154792516301 5350116058014433047193613)
                ·
                  refine ⟨2006293521755412392697605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5350116058014433047193613 2006293521755412392697605)
                  ·
                    refine ⟨376180035329139823630801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2006293521755412392697605 376180035329139823630801)
                    ·
                      rfl

theorem cell22_1098912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_1098912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098912 prefixEnd_1098912 := by exact prefixLift 1098912
  have htrace : WordTrace (prefixWord ++ tailWord_1098912) baseStart_1098912 baseEnd_1098912 := by
    simpa [prefixWord, tailWord_1098912, baseEnd_1098912] using wordTrace_append hprefix tailTrace_1098912
  have hstable : (prefixWord ++ tailWord_1098912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098912).length < 2 ^ (prefixWord ++ tailWord_1098912).sum := by decide
  have hdescent : baseEnd_1098912 < baseStart_1098912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098944 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 6]
def baseStart_1098944 : Nat := 118140960795 + 1098944 * 2 ^ 59
def prefixEnd_1098944 : Nat := 4983230072969 + 3 ^ 40 * 1098944 * 2
def baseEnd_1098944 : Nat := 125396996527700802276901

theorem tailTrace_1098944 : CollatzResearch.WordTrace tailWord_1098944 prefixEnd_1098944 125396996527700802276901 := by
  unfold tailWord_1098944
  simp only [CollatzResearch.WordTrace]
  refine ⟨20040890265360523768983943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26721187020480698358645257 20040890265360523768983943)
  ·
    refine ⟨30061335398040785653475915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20040890265360523768983943 30061335398040785653475915)
    ·
      refine ⟨45092003097061178480213873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30061335398040785653475915 45092003097061178480213873)
      ·
        refine ⟨33819002322795883860160405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45092003097061178480213873 33819002322795883860160405)
        ·
          refine ⟨1585265733881057055945019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33819002322795883860160405 1585265733881057055945019)
          ·
            refine ⟨2377898600821585583917529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585265733881057055945019 2377898600821585583917529)
            ·
              refine ⟨1783423950616189187938147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2377898600821585583917529 1783423950616189187938147)
              ·
                refine ⟨2675135925924283781907221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783423950616189187938147 2675135925924283781907221)
                ·
                  refine ⟨125396996527700802276901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2675135925924283781907221 125396996527700802276901)
                  ·
                    rfl

theorem cell22_1098944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_1098944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098944 prefixEnd_1098944 := by exact prefixLift 1098944
  have htrace : WordTrace (prefixWord ++ tailWord_1098944) baseStart_1098944 baseEnd_1098944 := by
    simpa [prefixWord, tailWord_1098944, baseEnd_1098944] using wordTrace_append hprefix tailTrace_1098944
  have hstable : (prefixWord ++ tailWord_1098944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098944).length < 2 ^ (prefixWord ++ tailWord_1098944).sum := by decide
  have hdescent : baseEnd_1098944 < baseStart_1098944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098989 : List Nat := [1, 5, 1, 2, 2, 3, 8]
def baseStart_1098989 : Nat := 118140960795 + 1098989 * 2 ^ 59
def prefixEnd_1098989 : Nat := 4983230072969 + 3 ^ 40 * 1098989 * 2
def baseEnd_1098989 : Nat := 13933570148249529239095

theorem tailTrace_1098989 : CollatzResearch.WordTrace tailWord_1098989 prefixEnd_1098989 13933570148249529239095 := by
  unfold tailWord_1098989
  simp only [CollatzResearch.WordTrace]
  refine ⟨40083421815558020223356021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26722281210372013482237347 40083421815558020223356021)
  ·
    refine ⟨3757820795208564395939627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40083421815558020223356021 3757820795208564395939627)
    ·
      refine ⟨5636731192812846593909441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757820795208564395939627 5636731192812846593909441)
      ·
        refine ⟨4227548394609634945432081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5636731192812846593909441 4227548394609634945432081)
        ·
          refine ⟨3170661295957226209074061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4227548394609634945432081 3170661295957226209074061)
          ·
            refine ⟨1188997985983959828402773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3170661295957226209074061 1188997985983959828402773)
            ·
              refine ⟨13933570148249529239095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1188997985983959828402773 13933570148249529239095)
              ·
                rfl

theorem cell22_1098989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 8].length) (baseStart_1098989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1098989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1098989 prefixEnd_1098989 := by exact prefixLift 1098989
  have htrace : WordTrace (prefixWord ++ tailWord_1098989) baseStart_1098989 baseEnd_1098989 := by
    simpa [prefixWord, tailWord_1098989, baseEnd_1098989] using wordTrace_append hprefix tailTrace_1098989
  have hstable : (prefixWord ++ tailWord_1098989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098989).length < 2 ^ (prefixWord ++ tailWord_1098989).sum := by decide
  have hdescent : baseEnd_1098989 < baseStart_1098989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099002 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_1099002 : Nat := 118140960795 + 1099002 * 2 ^ 59
def prefixEnd_1099002 : Nat := 4983230072969 + 3 ^ 40 * 1099002 * 2
def baseEnd_1099002 : Nat := 376210844168409588880525

theorem tailTrace_1099002 : CollatzResearch.WordTrace tailWord_1099002 prefixEnd_1099002 376210844168409588880525 := by
  unfold tailWord_1099002
  simp only [CollatzResearch.WordTrace]
  refine ⟨10020973991127730860894815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26722597309673948962386173 10020973991127730860894815)
  ·
    refine ⟨15031460986691596291342223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10020973991127730860894815 15031460986691596291342223)
    ·
      refine ⟨22547191480037394437013335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15031460986691596291342223 22547191480037394437013335)
      ·
        refine ⟨33820787220056091655520003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22547191480037394437013335 33820787220056091655520003)
        ·
          refine ⟨50731180830084137483280005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33820787220056091655520003 50731180830084137483280005)
          ·
            refine ⟨9512096405640775778115001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50731180830084137483280005 9512096405640775778115001)
            ·
              refine ⟨7134072304230581833586251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9512096405640775778115001 7134072304230581833586251)
              ·
                refine ⟨10701108456345872750379377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7134072304230581833586251 10701108456345872750379377)
                ·
                  refine ⟨8025831342259404562784533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10701108456345872750379377 8025831342259404562784533)
                  ·
                    refine ⟨376210844168409588880525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8025831342259404562784533 376210844168409588880525)
                    ·
                      rfl

theorem cell22_1099002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_1099002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099002 prefixEnd_1099002 := by exact prefixLift 1099002
  have htrace : WordTrace (prefixWord ++ tailWord_1099002) baseStart_1099002 baseEnd_1099002 := by
    simpa [prefixWord, tailWord_1099002, baseEnd_1099002] using wordTrace_append hprefix tailTrace_1099002
  have hstable : (prefixWord ++ tailWord_1099002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099002).length < 2 ^ (prefixWord ++ tailWord_1099002).sum := by decide
  have hdescent : baseEnd_1099002 < baseStart_1099002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099079 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 6]
def baseStart_1099079 : Nat := 118140960795 + 1099079 * 2 ^ 59
def prefixEnd_1099079 : Nat := 4983230072969 + 3 ^ 40 * 1099079 * 2
def baseEnd_1099079 : Nat := 125412400947335684901763

theorem tailTrace_1099079 : CollatzResearch.WordTrace tailWord_1099079 prefixEnd_1099079 125412400947335684901763 := by
  unfold tailWord_1099079
  simp only [CollatzResearch.WordTrace]
  refine ⟨40086704385231965594132291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26724469590154643729421527 40086704385231965594132291)
  ·
    refine ⟨60130056577847948391198437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40086704385231965594132291 60130056577847948391198437)
    ·
      refine ⟨11274385608346490323349707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60130056577847948391198437 11274385608346490323349707)
      ·
        refine ⟨16911578412519735485024561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11274385608346490323349707 16911578412519735485024561)
        ·
          refine ⟨12683683809389801613768421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16911578412519735485024561 12683683809389801613768421)
          ·
            refine ⟨2378190714260587802581579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12683683809389801613768421 2378190714260587802581579)
            ·
              refine ⟨3567286071390881703872369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378190714260587802581579 3567286071390881703872369)
              ·
                refine ⟨2675464553543161277904277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3567286071390881703872369 2675464553543161277904277)
                ·
                  refine ⟨125412400947335684901763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2675464553543161277904277 125412400947335684901763)
                  ·
                    rfl

theorem cell22_1099079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 6].length) (baseStart_1099079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099079 prefixEnd_1099079 := by exact prefixLift 1099079
  have htrace : WordTrace (prefixWord ++ tailWord_1099079) baseStart_1099079 baseEnd_1099079 := by
    simpa [prefixWord, tailWord_1099079, baseEnd_1099079] using wordTrace_append hprefix tailTrace_1099079
  have hstable : (prefixWord ++ tailWord_1099079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099079).length < 2 ^ (prefixWord ++ tailWord_1099079).sum := by decide
  have hdescent : baseEnd_1099079 < baseStart_1099079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099096 : List Nat := [2, 1, 2, 2, 1, 1, 6, 3, 4]
def baseStart_1099096 : Nat := 118140960795 + 1099096 * 2 ^ 59
def prefixEnd_1099096 : Nat := 4983230072969 + 3 ^ 40 * 1099096 * 2
def baseEnd_1099096 : Nat := 125414340763141559010079

theorem tailTrace_1099096 : CollatzResearch.WordTrace tailWord_1099096 prefixEnd_1099096 125414340763141559010079 := by
  unfold tailWord_1099096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20043662213085188748750571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26724882950780251665000761 20043662213085188748750571)
  ·
    refine ⟨30065493319627783123125857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20043662213085188748750571 30065493319627783123125857)
    ·
      refine ⟨22549119989720837342344393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30065493319627783123125857 22549119989720837342344393)
      ·
        refine ⟨16911839992290628006758295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22549119989720837342344393 16911839992290628006758295)
        ·
          refine ⟨25367759988435942010137443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16911839992290628006758295 25367759988435942010137443)
          ·
            refine ⟨38051639982653913015206165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25367759988435942010137443 38051639982653913015206165)
            ·
              refine ⟨1783670624186902172587789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38051639982653913015206165 1783670624186902172587789)
              ·
                refine ⟨668876484070088314720421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783670624186902172587789 668876484070088314720421)
                ·
                  refine ⟨125414340763141559010079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668876484070088314720421 125414340763141559010079)
                  ·
                    rfl

theorem cell22_1099096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_1099096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099096 prefixEnd_1099096 := by exact prefixLift 1099096
  have htrace : WordTrace (prefixWord ++ tailWord_1099096) baseStart_1099096 baseEnd_1099096 := by
    simpa [prefixWord, tailWord_1099096, baseEnd_1099096] using wordTrace_append hprefix tailTrace_1099096
  have hstable : (prefixWord ++ tailWord_1099096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099096).length < 2 ^ (prefixWord ++ tailWord_1099096).sum := by decide
  have hdescent : baseEnd_1099096 < baseStart_1099096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099109 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_1099109 : Nat := 118140960795 + 1099109 * 2 ^ 59
def prefixEnd_1099109 : Nat := 4983230072969 + 3 ^ 40 * 1099109 * 2
def baseEnd_1099109 : Nat := 376247472455096976455197

theorem tailTrace_1099109 : CollatzResearch.WordTrace tailWord_1099109 prefixEnd_1099109 376247472455096976455197 := by
  unfold tailWord_1099109
  simp only [CollatzResearch.WordTrace]
  refine ⟨40087798575123280717724381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26725199050082187145149587 40087798575123280717724381)
  ·
    refine ⟨15032924465671230269146643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40087798575123280717724381 15032924465671230269146643)
    ·
      refine ⟨22549386698506845403719965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15032924465671230269146643 22549386698506845403719965)
      ·
        refine ⟨8456020011940067026394987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22549386698506845403719965 8456020011940067026394987)
        ·
          refine ⟨12684030017910100539592481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8456020011940067026394987 12684030017910100539592481)
          ·
            refine ⟨9513022513432575404694361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12684030017910100539592481 9513022513432575404694361)
            ·
              refine ⟨7134766885074431553520771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9513022513432575404694361 7134766885074431553520771)
              ·
                refine ⟨10702150327611647330281157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7134766885074431553520771 10702150327611647330281157)
                ·
                  refine ⟨2006653186427183874427717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10702150327611647330281157 2006653186427183874427717)
                  ·
                    refine ⟨376247472455096976455197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2006653186427183874427717 376247472455096976455197)
                    ·
                      rfl

theorem cell22_1099109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_1099109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099109 prefixEnd_1099109 := by exact prefixLift 1099109
  have htrace : WordTrace (prefixWord ++ tailWord_1099109) baseStart_1099109 baseEnd_1099109 := by
    simpa [prefixWord, tailWord_1099109, baseEnd_1099109] using wordTrace_append hprefix tailTrace_1099109
  have hstable : (prefixWord ++ tailWord_1099109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099109).length < 2 ^ (prefixWord ++ tailWord_1099109).sum := by decide
  have hdescent : baseEnd_1099109 < baseStart_1099109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099261 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1099261 : Nat := 118140960795 + 1099261 * 2 ^ 59
def prefixEnd_1099261 : Nat := 4983230072969 + 3 ^ 40 * 1099261 * 2
def baseEnd_1099261 : Nat := 376299505161419246654731

theorem tailTrace_1099261 : CollatzResearch.WordTrace tailWord_1099261 prefixEnd_1099261 376299505161419246654731 := by
  unfold tailWord_1099261
  simp only [CollatzResearch.WordTrace]
  refine ⟨40093342470572610677257637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26728894980381740451505091 40093342470572610677257637)
  ·
    refine ⟨7517501713232364501985807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40093342470572610677257637 7517501713232364501985807)
    ·
      refine ⟨11276252569848546752978711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517501713232364501985807 11276252569848546752978711)
      ·
        refine ⟨16914378854772820129468067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11276252569848546752978711 16914378854772820129468067)
        ·
          refine ⟨25371568282159230194202101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16914378854772820129468067 25371568282159230194202101)
          ·
            refine ⟨2378584526452427830706447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25371568282159230194202101 2378584526452427830706447)
            ·
              refine ⟨3567876789678641746059671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378584526452427830706447 3567876789678641746059671)
              ·
                refine ⟨5351815184517962619089507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567876789678641746059671 5351815184517962619089507)
                ·
                  refine ⟨8027722776776943928634261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5351815184517962619089507 8027722776776943928634261)
                  ·
                    refine ⟨376299505161419246654731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8027722776776943928634261 376299505161419246654731)
                    ·
                      rfl

theorem cell22_1099261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1099261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099261 prefixEnd_1099261 := by exact prefixLift 1099261
  have htrace : WordTrace (prefixWord ++ tailWord_1099261) baseStart_1099261 baseEnd_1099261 := by
    simpa [prefixWord, tailWord_1099261, baseEnd_1099261] using wordTrace_append hprefix tailTrace_1099261
  have hstable : (prefixWord ++ tailWord_1099261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099261).length < 2 ^ (prefixWord ++ tailWord_1099261).sum := by decide
  have hdescent : baseEnd_1099261 < baseStart_1099261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099265 : List Nat := [1, 2, 4, 1, 4, 1, 2, 3, 4]
def baseStart_1099265 : Nat := 118140960795 + 1099265 * 2 ^ 59
def prefixEnd_1099265 : Nat := 4983230072969 + 3 ^ 40 * 1099265 * 2
def baseEnd_1099265 : Nat := 125433624814388189851573

theorem tailTrace_1099265 : CollatzResearch.WordTrace tailWord_1099265 prefixEnd_1099265 125433624814388189851573 := by
  unfold tailWord_1099265
  simp only [CollatzResearch.WordTrace]
  refine ⟨40093488362558119360403249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26728992241705412906935499 40093488362558119360403249)
  ·
    refine ⟨30070116271918589520302437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40093488362558119360403249 30070116271918589520302437)
    ·
      refine ⟨5638146800984735535056707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30070116271918589520302437 5638146800984735535056707)
      ·
        refine ⟨8457220201477103302585061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5638146800984735535056707 8457220201477103302585061)
        ·
          refine ⟨1585728787776956869234699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8457220201477103302585061 1585728787776956869234699)
          ·
            refine ⟨2378593181665435303852049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585728787776956869234699 2378593181665435303852049)
            ·
              refine ⟨1783944886249076477889037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2378593181665435303852049 1783944886249076477889037)
              ·
                refine ⟨668979332343403679208389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783944886249076477889037 668979332343403679208389)
                ·
                  refine ⟨125433624814388189851573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668979332343403679208389 125433624814388189851573)
                  ·
                    rfl

theorem cell22_1099265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_1099265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099265 prefixEnd_1099265 := by exact prefixLift 1099265
  have htrace : WordTrace (prefixWord ++ tailWord_1099265) baseStart_1099265 baseEnd_1099265 := by
    simpa [prefixWord, tailWord_1099265, baseEnd_1099265] using wordTrace_append hprefix tailTrace_1099265
  have hstable : (prefixWord ++ tailWord_1099265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099265).length < 2 ^ (prefixWord ++ tailWord_1099265).sum := by decide
  have hdescent : baseEnd_1099265 < baseStart_1099265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099276 : List Nat := [2, 2, 1, 2, 5, 1, 9]
def baseStart_1099276 : Nat := 118140960795 + 1099276 * 2 ^ 59
def prefixEnd_1099276 : Nat := 4983230072969 + 3 ^ 40 * 1099276 * 2
def baseEnd_1099276 : Nat := 13937208887702378056655

theorem tailTrace_1099276 : CollatzResearch.WordTrace tailWord_1099276 prefixEnd_1099276 13937208887702378056655 := by
  unfold tailWord_1099276
  simp only [CollatzResearch.WordTrace]
  refine ⟨20046944782759134119526841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26729259710345512159369121 20046944782759134119526841)
  ·
    refine ⟨15035208587069350589645131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20046944782759134119526841 15035208587069350589645131)
    ·
      refine ⟨22552812880604025884467697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15035208587069350589645131 22552812880604025884467697)
      ·
        refine ⟨16914609660453019413350773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22552812880604025884467697 16914609660453019413350773)
        ·
          refine ⟨1585744655667470570001635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16914609660453019413350773 1585744655667470570001635)
          ·
            refine ⟨2378616983501205855002453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585744655667470570001635 2378616983501205855002453)
            ·
              refine ⟨13937208887702378056655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2378616983501205855002453 13937208887702378056655)
              ·
                rfl

theorem cell22_1099276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 9].length) (baseStart_1099276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099276 prefixEnd_1099276 := by exact prefixLift 1099276
  have htrace : WordTrace (prefixWord ++ tailWord_1099276) baseStart_1099276 baseEnd_1099276 := by
    simpa [prefixWord, tailWord_1099276, baseEnd_1099276] using wordTrace_append hprefix tailTrace_1099276
  have hstable : (prefixWord ++ tailWord_1099276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099276).length < 2 ^ (prefixWord ++ tailWord_1099276).sum := by decide
  have hdescent : baseEnd_1099276 < baseStart_1099276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099310 : List Nat := [4, 1, 3, 1, 2, 3, 2, 6]
def baseStart_1099310 : Nat := 118140960795 + 1099310 * 2 ^ 59
def prefixEnd_1099310 : Nat := 4983230072969 + 3 ^ 40 * 1099310 * 2
def baseEnd_1099310 : Nat := 41812919873644383575509

theorem tailTrace_1099310 : CollatzResearch.WordTrace tailWord_1099310 prefixEnd_1099310 41812919873644383575509 := by
  unfold tailWord_1099310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011891205924386505723923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26730086431596728030527589 5011891205924386505723923)
  ·
    refine ⟨7517836808886579758585885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5011891205924386505723923 7517836808886579758585885)
    ·
      refine ⟨2819188803332467409469707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7517836808886579758585885 2819188803332467409469707)
      ·
        refine ⟨4228783204998701114204561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819188803332467409469707 4228783204998701114204561)
        ·
          refine ⟨3171587403749025835653421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4228783204998701114204561 3171587403749025835653421)
          ·
            refine ⟨1189345276405884688370033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3171587403749025835653421 1189345276405884688370033)
            ·
              refine ⟨892008957304413516277525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189345276405884688370033 892008957304413516277525)
              ·
                refine ⟨41812919873644383575509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 892008957304413516277525 41812919873644383575509)
                ·
                  rfl

theorem cell22_1099310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_1099310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099310 prefixEnd_1099310 := by exact prefixLift 1099310
  have htrace : WordTrace (prefixWord ++ tailWord_1099310) baseStart_1099310 baseEnd_1099310 := by
    simpa [prefixWord, tailWord_1099310, baseEnd_1099310] using wordTrace_append hprefix tailTrace_1099310
  have hstable : (prefixWord ++ tailWord_1099310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099310).length < 2 ^ (prefixWord ++ tailWord_1099310).sum := by decide
  have hdescent : baseEnd_1099310 < baseStart_1099310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099321 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 7]
def baseStart_1099321 : Nat := 118140960795 + 1099321 * 2 ^ 59
def prefixEnd_1099321 : Nat := 4983230072969 + 3 ^ 40 * 1099321 * 2
def baseEnd_1099321 : Nat := 125440014795866363384849

theorem tailTrace_1099321 : CollatzResearch.WordTrace tailWord_1099321 prefixEnd_1099321 125440014795866363384849 := by
  unfold tailWord_1099321
  simp only [CollatzResearch.WordTrace]
  refine ⟨40095530850355240924441817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26730353900236827282961211 40095530850355240924441817)
  ·
    refine ⟨30071648137766430693331363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40095530850355240924441817 30071648137766430693331363)
    ·
      refine ⟨45107472206649646039997045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30071648137766430693331363 45107472206649646039997045)
      ·
        refine ⟨4228825519373404316249723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45107472206649646039997045 4228825519373404316249723)
        ·
          refine ⟨6343238279060106474374585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228825519373404316249723 6343238279060106474374585)
          ·
            refine ⟨4757428709295079855780939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343238279060106474374585 4757428709295079855780939)
            ·
              refine ⟨7136143063942619783671409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757428709295079855780939 7136143063942619783671409)
              ·
                refine ⟨5352107297956964837753557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7136143063942619783671409 5352107297956964837753557)
                ·
                  refine ⟨125440014795866363384849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5352107297956964837753557 125440014795866363384849)
                  ·
                    rfl

theorem cell22_1099321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_1099321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099321 prefixEnd_1099321 := by exact prefixLift 1099321
  have htrace : WordTrace (prefixWord ++ tailWord_1099321) baseStart_1099321 baseEnd_1099321 := by
    simpa [prefixWord, tailWord_1099321, baseEnd_1099321] using wordTrace_append hprefix tailTrace_1099321
  have hstable : (prefixWord ++ tailWord_1099321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099321).length < 2 ^ (prefixWord ++ tailWord_1099321).sum := by decide
  have hdescent : baseEnd_1099321 < baseStart_1099321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099383 : List Nat := [1, 1, 3, 1, 1, 3, 1, 7, 4]
def baseStart_1099383 : Nat := 118140960795 + 1099383 * 2 ^ 59
def prefixEnd_1099383 : Nat := 4983230072969 + 3 ^ 40 * 1099383 * 2
def baseEnd_1099383 : Nat := 125447089418217198368119

theorem tailTrace_1099383 : CollatzResearch.WordTrace tailWord_1099383 prefixEnd_1099383 125447089418217198368119 := by
  unfold tailWord_1099383
  simp only [CollatzResearch.WordTrace]
  refine ⟨40097792176130625513198803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26731861450753750342132535 40097792176130625513198803)
  ·
    refine ⟨60146688264195938269798205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40097792176130625513198803 60146688264195938269798205)
    ·
      refine ⟨22555008099073476851174327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60146688264195938269798205 22555008099073476851174327)
      ·
        refine ⟨33832512148610215276761491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22555008099073476851174327 33832512148610215276761491)
        ·
          refine ⟨50748768222915322915142237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33832512148610215276761491 50748768222915322915142237)
          ·
            refine ⟨19030788083593246093178339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50748768222915322915142237 19030788083593246093178339)
            ·
              refine ⟨28546182125389869139767509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19030788083593246093178339 28546182125389869139767509)
              ·
                refine ⟨669051143563825057963301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28546182125389869139767509 669051143563825057963301)
                ·
                  refine ⟨125447089418217198368119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669051143563825057963301 125447089418217198368119)
                  ·
                    rfl

theorem cell22_1099383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 4].length) (baseStart_1099383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099383 prefixEnd_1099383 := by exact prefixLift 1099383
  have htrace : WordTrace (prefixWord ++ tailWord_1099383) baseStart_1099383 baseEnd_1099383 := by
    simpa [prefixWord, tailWord_1099383, baseEnd_1099383] using wordTrace_append hprefix tailTrace_1099383
  have hstable : (prefixWord ++ tailWord_1099383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099383).length < 2 ^ (prefixWord ++ tailWord_1099383).sum := by decide
  have hdescent : baseEnd_1099383 < baseStart_1099383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099385 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 1, 4]
def baseStart_1099385 : Nat := 118140960795 + 1099385 * 2 ^ 59
def prefixEnd_1099385 : Nat := 4983230072969 + 3 ^ 40 * 1099385 * 2
def baseEnd_1099385 : Nat := 376341952895524256554351

theorem tailTrace_1099385 : CollatzResearch.WordTrace tailWord_1099385 prefixEnd_1099385 376341952895524256554351 := by
  unfold tailWord_1099385
  simp only [CollatzResearch.WordTrace]
  refine ⟨40097865122123379854771609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26731910081415586569847739 40097865122123379854771609)
  ·
    refine ⟨30073398841592534891078707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40097865122123379854771609 30073398841592534891078707)
    ·
      refine ⟨45110098262388802336618061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30073398841592534891078707 45110098262388802336618061)
      ·
        refine ⟨16916286848395800876231773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45110098262388802336618061 16916286848395800876231773)
        ·
          refine ⟨6343607568148425328586915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16916286848395800876231773 6343607568148425328586915)
          ·
            refine ⟨9515411352222637992880373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343607568148425328586915 9515411352222637992880373)
            ·
              refine ⟨892069814270872311832535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9515411352222637992880373 892069814270872311832535)
              ·
                refine ⟨1338104721406308467748803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892069814270872311832535 1338104721406308467748803)
                ·
                  refine ⟨2007157082109462701623205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338104721406308467748803 2007157082109462701623205)
                  ·
                    refine ⟨376341952895524256554351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2007157082109462701623205 376341952895524256554351)
                    ·
                      rfl

theorem cell22_1099385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_1099385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099385 prefixEnd_1099385 := by exact prefixLift 1099385
  have htrace : WordTrace (prefixWord ++ tailWord_1099385) baseStart_1099385 baseEnd_1099385 := by
    simpa [prefixWord, tailWord_1099385, baseEnd_1099385] using wordTrace_append hprefix tailTrace_1099385
  have hstable : (prefixWord ++ tailWord_1099385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099385).length < 2 ^ (prefixWord ++ tailWord_1099385).sum := by decide
  have hdescent : baseEnd_1099385 < baseStart_1099385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099415 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 2, 3]
def baseStart_1099415 : Nat := 118140960795 + 1099415 * 2 ^ 59
def prefixEnd_1099415 : Nat := 4983230072969 + 3 ^ 40 * 1099415 * 2
def baseEnd_1099415 : Nat := 376352222508614178304259

theorem tailTrace_1099415 : CollatzResearch.WordTrace tailWord_1099415 prefixEnd_1099415 376352222508614178304259 := by
  unfold tailWord_1099415
  simp only [CollatzResearch.WordTrace]
  refine ⟨40098959312014694978363699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26732639541343129985575799 40098959312014694978363699)
  ·
    refine ⟨60148438968022042467545549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40098959312014694978363699 60148438968022042467545549)
    ·
      refine ⟨22555664613008265925329581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60148438968022042467545549 22555664613008265925329581)
      ·
        refine ⟨8458374229878099721998593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22555664613008265925329581 8458374229878099721998593)
        ·
          refine ⟨6343780672408574791498945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8458374229878099721998593 6343780672408574791498945)
          ·
            refine ⟨4757835504306431093624209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343780672408574791498945 4757835504306431093624209)
            ·
              refine ⟨3568376628229823320218157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4757835504306431093624209 3568376628229823320218157)
              ·
                refine ⟨1338141235586183745081809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3568376628229823320218157 1338141235586183745081809)
                ·
                  refine ⟨1003605926689637808811357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1338141235586183745081809 1003605926689637808811357)
                  ·
                    refine ⟨376352222508614178304259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1003605926689637808811357 376352222508614178304259)
                    ·
                      rfl

theorem cell22_1099415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_1099415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099415 prefixEnd_1099415 := by exact prefixLift 1099415
  have htrace : WordTrace (prefixWord ++ tailWord_1099415) baseStart_1099415 baseEnd_1099415 := by
    simpa [prefixWord, tailWord_1099415, baseEnd_1099415] using wordTrace_append hprefix tailTrace_1099415
  have hstable : (prefixWord ++ tailWord_1099415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099415).length < 2 ^ (prefixWord ++ tailWord_1099415).sum := by decide
  have hdescent : baseEnd_1099415 < baseStart_1099415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099443 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 5, 3]
def baseStart_1099443 : Nat := 118140960795 + 1099443 * 2 ^ 59
def prefixEnd_1099443 : Nat := 4983230072969 + 3 ^ 40 * 1099443 * 2
def baseEnd_1099443 : Nat := 376361807480831438604173

theorem tailTrace_1099443 : CollatzResearch.WordTrace tailWord_1099443 prefixEnd_1099443 376361807480831438604173 := by
  unfold tailWord_1099443
  simp only [CollatzResearch.WordTrace]
  refine ⟨40099980555913255760382983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26733320370608837173588655 40099980555913255760382983)
  ·
    refine ⟨60149970833869883640574475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40099980555913255760382983 60149970833869883640574475)
    ·
      refine ⟨90224956250804825460861713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60149970833869883640574475 90224956250804825460861713)
      ·
        refine ⟨67668717188103619095646285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90224956250804825460861713 67668717188103619095646285)
        ·
          refine ⟨25375768945538857160867357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67668717188103619095646285 25375768945538857160867357)
          ·
            refine ⟨9515913354577071435325259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25375768945538857160867357 9515913354577071435325259)
            ·
              refine ⟨14273870031865607152987889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9515913354577071435325259 14273870031865607152987889)
              ·
                refine ⟨10705402523899205364740917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14273870031865607152987889 10705402523899205364740917)
                ·
                  refine ⟨1003631486615550502944461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10705402523899205364740917 1003631486615550502944461)
                  ·
                    refine ⟨376361807480831438604173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1003631486615550502944461 376361807480831438604173)
                    ·
                      rfl

theorem cell22_1099443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 3].length) (baseStart_1099443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099443 prefixEnd_1099443 := by exact prefixLift 1099443
  have htrace : WordTrace (prefixWord ++ tailWord_1099443) baseStart_1099443 baseEnd_1099443 := by
    simpa [prefixWord, tailWord_1099443, baseEnd_1099443] using wordTrace_append hprefix tailTrace_1099443
  have hstable : (prefixWord ++ tailWord_1099443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099443).length < 2 ^ (prefixWord ++ tailWord_1099443).sum := by decide
  have hdescent : baseEnd_1099443 < baseStart_1099443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099569 : List Nat := [1, 2, 2, 3, 2, 4, 2, 2, 4]
def baseStart_1099569 : Nat := 118140960795 + 1099569 * 2 ^ 59
def prefixEnd_1099569 : Nat := 4983230072969 + 3 ^ 40 * 1099569 * 2
def baseEnd_1099569 : Nat := 125468313285269703317929

theorem tailTrace_1099569 : CollatzResearch.WordTrace tailWord_1099569 prefixEnd_1099569 125468313285269703317929 := by
  unfold tailWord_1099569
  simp only [CollatzResearch.WordTrace]
  refine ⟨40104576153456779279469761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26736384102304519519646507 40104576153456779279469761)
  ·
    refine ⟨30078432115092584459602321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40104576153456779279469761 30078432115092584459602321)
    ·
      refine ⟨22558824086319438344701741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30078432115092584459602321 22558824086319438344701741)
      ·
        refine ⟨8459559032369789379263153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22558824086319438344701741 8459559032369789379263153)
        ·
          refine ⟨6344669274277342034447365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8459559032369789379263153 6344669274277342034447365)
          ·
            refine ⟨1189625488927001631458881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6344669274277342034447365 1189625488927001631458881)
            ·
              refine ⟨892219116695251223594161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189625488927001631458881 892219116695251223594161)
              ·
                refine ⟨669164337521438417695621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892219116695251223594161 669164337521438417695621)
                ·
                  refine ⟨125468313285269703317929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669164337521438417695621 125468313285269703317929)
                  ·
                    rfl

theorem cell22_1099569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_1099569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099569 prefixEnd_1099569 := by exact prefixLift 1099569
  have htrace : WordTrace (prefixWord ++ tailWord_1099569) baseStart_1099569 baseEnd_1099569 := by
    simpa [prefixWord, tailWord_1099569, baseEnd_1099569] using wordTrace_append hprefix tailTrace_1099569
  have hstable : (prefixWord ++ tailWord_1099569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099569).length < 2 ^ (prefixWord ++ tailWord_1099569).sum := by decide
  have hdescent : baseEnd_1099569 < baseStart_1099569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099593 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_1099593 : Nat := 118140960795 + 1099593 * 2 ^ 59
def prefixEnd_1099593 : Nat := 4983230072969 + 3 ^ 40 * 1099593 * 2
def baseEnd_1099593 : Nat := 376413155546281047353713

theorem tailTrace_1099593 : CollatzResearch.WordTrace tailWord_1099593 prefixEnd_1099593 376413155546281047353713 := by
  unfold tailWord_1099593
  simp only [CollatzResearch.WordTrace]
  refine ⟨40105451505369831378343433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26736967670246554252228955 40105451505369831378343433)
  ·
    refine ⟨30079088629027373533757575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40105451505369831378343433 30079088629027373533757575)
    ·
      refine ⟨45118632943541060300636363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30079088629027373533757575 45118632943541060300636363)
      ·
        refine ⟨67677949415311590450954545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45118632943541060300636363 67677949415311590450954545)
        ·
          refine ⟨50758462061483692838215909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67677949415311590450954545 50758462061483692838215909)
          ·
            refine ⟨9517211636528192407165483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50758462061483692838215909 9517211636528192407165483)
            ·
              refine ⟨14275817454792288610748225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9517211636528192407165483 14275817454792288610748225)
              ·
                refine ⟨10706863091094216458061169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14275817454792288610748225 10706863091094216458061169)
                ·
                  refine ⟨8030147318320662343545877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10706863091094216458061169 8030147318320662343545877)
                  ·
                    refine ⟨376413155546281047353713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8030147318320662343545877 376413155546281047353713)
                    ·
                      rfl

theorem cell22_1099593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_1099593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099593 prefixEnd_1099593 := by exact prefixLift 1099593
  have htrace : WordTrace (prefixWord ++ tailWord_1099593) baseStart_1099593 baseEnd_1099593 := by
    simpa [prefixWord, tailWord_1099593, baseEnd_1099593] using wordTrace_append hprefix tailTrace_1099593
  have hstable : (prefixWord ++ tailWord_1099593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099593).length < 2 ^ (prefixWord ++ tailWord_1099593).sum := by decide
  have hdescent : baseEnd_1099593 < baseStart_1099593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099629 : List Nat := [1, 5, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_1099629 : Nat := 118140960795 + 1099629 * 2 ^ 59
def prefixEnd_1099629 : Nat := 4983230072969 + 3 ^ 40 * 1099629 * 2
def baseEnd_1099629 : Nat := 376425479081988953453603

theorem tailTrace_1099629 : CollatzResearch.WordTrace tailWord_1099629 prefixEnd_1099629 376425479081988953453603 := by
  unfold tailWord_1099629
  simp only [CollatzResearch.WordTrace]
  refine ⟨40106764533239409526653941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26737843022159606351102627 40106764533239409526653941)
  ·
    refine ⟨3760009174991194643123807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40106764533239409526653941 3760009174991194643123807)
    ·
      refine ⟨5640013762486791964685711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3760009174991194643123807 5640013762486791964685711)
      ·
        refine ⟨8460020643730187947028567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5640013762486791964685711 8460020643730187947028567)
        ·
          refine ⟨12690030965595281920542851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8460020643730187947028567 12690030965595281920542851)
          ·
            refine ⟨19035046448392922880814277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12690030965595281920542851 19035046448392922880814277)
            ·
              refine ⟨3569071209073673040152677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19035046448392922880814277 3569071209073673040152677)
              ·
                refine ⟨669200851701313695028627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3569071209073673040152677 669200851701313695028627)
                ·
                  refine ⟨1003801277551970542542941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669200851701313695028627 1003801277551970542542941)
                  ·
                    refine ⟨376425479081988953453603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1003801277551970542542941 376425479081988953453603)
                    ·
                      rfl

theorem cell22_1099629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_1099629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099629 prefixEnd_1099629 := by exact prefixLift 1099629
  have htrace : WordTrace (prefixWord ++ tailWord_1099629) baseStart_1099629 baseEnd_1099629 := by
    simpa [prefixWord, tailWord_1099629, baseEnd_1099629] using wordTrace_append hprefix tailTrace_1099629
  have hstable : (prefixWord ++ tailWord_1099629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099629).length < 2 ^ (prefixWord ++ tailWord_1099629).sum := by decide
  have hdescent : baseEnd_1099629 < baseStart_1099629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099687 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 6]
def baseStart_1099687 : Nat := 118140960795 + 1099687 * 2 ^ 59
def prefixEnd_1099687 : Nat := 4983230072969 + 3 ^ 40 * 1099687 * 2
def baseEnd_1099687 : Nat := 125481777889098711834475

theorem tailTrace_1099687 : CollatzResearch.WordTrace tailWord_1099687 prefixEnd_1099687 125481777889098711834475 := by
  unfold tailWord_1099687
  simp only [CollatzResearch.WordTrace]
  refine ⟨40108879967029285432265315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26739253311352856954843543 40108879967029285432265315)
  ·
    refine ⟨60163319950543928148397973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40108879967029285432265315 60163319950543928148397973)
    ·
      refine ⟨2820155622681746631956155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60163319950543928148397973 2820155622681746631956155)
      ·
        refine ⟨4230233434022619947934233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820155622681746631956155 4230233434022619947934233)
        ·
          refine ⟨3172675075516964960950675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4230233434022619947934233 3172675075516964960950675)
          ·
            refine ⟨4759012613275447441426013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3172675075516964960950675 4759012613275447441426013)
            ·
              refine ⟨1784629729978292790534755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4759012613275447441426013 1784629729978292790534755)
              ·
                refine ⟨2676944594967439185802133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784629729978292790534755 2676944594967439185802133)
                ·
                  refine ⟨125481777889098711834475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2676944594967439185802133 125481777889098711834475)
                  ·
                    rfl

theorem cell22_1099687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 6].length) (baseStart_1099687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099687 prefixEnd_1099687 := by exact prefixLift 1099687
  have htrace : WordTrace (prefixWord ++ tailWord_1099687) baseStart_1099687 baseEnd_1099687 := by
    simpa [prefixWord, tailWord_1099687, baseEnd_1099687] using wordTrace_append hprefix tailTrace_1099687
  have hstable : (prefixWord ++ tailWord_1099687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099687).length < 2 ^ (prefixWord ++ tailWord_1099687).sum := by decide
  have hdescent : baseEnd_1099687 < baseStart_1099687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099738 : List Nat := [3, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_1099738 : Nat := 118140960795 + 1099738 * 2 ^ 59
def prefixEnd_1099738 : Nat := 4983230072969 + 3 ^ 40 * 1099738 * 2
def baseEnd_1099738 : Nat := 125487597336516334159423

theorem tailTrace_1099738 : CollatzResearch.WordTrace tailWord_1099738 prefixEnd_1099738 125487597336516334159423 := by
  unfold tailWord_1099738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027685022461130285592967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26740493393229680761581245 10027685022461130285592967)
  ·
    refine ⟨15041527533691695428389451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10027685022461130285592967 15041527533691695428389451)
    ·
      refine ⟨22562291300537543142584177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15041527533691695428389451 22562291300537543142584177)
      ·
        refine ⟨16921718475403157356938133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22562291300537543142584177 16921718475403157356938133)
        ·
          refine ⟨793205553534523001106475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16921718475403157356938133 793205553534523001106475)
          ·
            refine ⟨1189808330301784501659713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793205553534523001106475 1189808330301784501659713)
            ·
              refine ⟨892356247726338376244785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189808330301784501659713 892356247726338376244785)
              ·
                refine ⟨669267185794753782183589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892356247726338376244785 669267185794753782183589)
                ·
                  refine ⟨125487597336516334159423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669267185794753782183589 125487597336516334159423)
                  ·
                    rfl

theorem cell22_1099738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_1099738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099738 prefixEnd_1099738 := by exact prefixLift 1099738
  have htrace : WordTrace (prefixWord ++ tailWord_1099738) baseStart_1099738 baseEnd_1099738 := by
    simpa [prefixWord, tailWord_1099738, baseEnd_1099738] using wordTrace_append hprefix tailTrace_1099738
  have hstable : (prefixWord ++ tailWord_1099738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099738).length < 2 ^ (prefixWord ++ tailWord_1099738).sum := by decide
  have hdescent : baseEnd_1099738 < baseStart_1099738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099745 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1099745 : Nat := 118140960795 + 1099745 * 2 ^ 59
def prefixEnd_1099745 : Nat := 4983230072969 + 3 ^ 40 * 1099745 * 2
def baseEnd_1099745 : Nat := 376465188252603317553247

theorem tailTrace_1099745 : CollatzResearch.WordTrace tailWord_1099745 prefixEnd_1099745 376465188252603317553247 := by
  unfold tailWord_1099745
  simp only [CollatzResearch.WordTrace]
  refine ⟨40110995400819161337876689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26740663600546107558584459 40110995400819161337876689)
  ·
    refine ⟨30083246550614371003407517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40110995400819161337876689 30083246550614371003407517)
    ·
      refine ⟨11281217456480389126277819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30083246550614371003407517 11281217456480389126277819)
      ·
        refine ⟨16921826184720583689416729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11281217456480389126277819 16921826184720583689416729)
        ·
          refine ⟨12691369638540437767062547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16921826184720583689416729 12691369638540437767062547)
          ·
            refine ⟨19037054457810656650593821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12691369638540437767062547 19037054457810656650593821)
            ·
              refine ⟨7138895421678996243972683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19037054457810656650593821 7138895421678996243972683)
              ·
                refine ⟨10708343132518494365959025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7138895421678996243972683 10708343132518494365959025)
                ·
                  refine ⟨8031257349388870774469269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10708343132518494365959025 8031257349388870774469269)
                  ·
                    refine ⟨376465188252603317553247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8031257349388870774469269 376465188252603317553247)
                    ·
                      rfl

theorem cell22_1099745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1099745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099745 prefixEnd_1099745 := by exact prefixLift 1099745
  have htrace : WordTrace (prefixWord ++ tailWord_1099745) baseStart_1099745 baseEnd_1099745 := by
    simpa [prefixWord, tailWord_1099745, baseEnd_1099745] using wordTrace_append hprefix tailTrace_1099745
  have hstable : (prefixWord ++ tailWord_1099745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099745).length < 2 ^ (prefixWord ++ tailWord_1099745).sum := by decide
  have hdescent : baseEnd_1099745 < baseStart_1099745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099781 : List Nat := [1, 3, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_1099781 : Nat := 118140960795 + 1099781 * 2 ^ 59
def prefixEnd_1099781 : Nat := 4983230072969 + 3 ^ 40 * 1099781 * 2
def baseEnd_1099781 : Nat := 376477511788311223653137

theorem tailTrace_1099781 : CollatzResearch.WordTrace tailWord_1099781 prefixEnd_1099781 376477511788311223653137 := by
  unfold tailWord_1099781
  simp only [CollatzResearch.WordTrace]
  refine ⟨40112308428688739486187197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26741538952459159657458131 40112308428688739486187197)
  ·
    refine ⟨15042115660758277307320199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40112308428688739486187197 15042115660758277307320199)
    ·
      refine ⟨22563173491137415960980299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15042115660758277307320199 22563173491137415960980299)
      ·
        refine ⟨33844760236706123941470449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22563173491137415960980299 33844760236706123941470449)
        ·
          refine ⟨25383570177529592956102837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33844760236706123941470449 25383570177529592956102837)
          ·
            refine ⟨2379709704143399339634641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25383570177529592956102837 2379709704143399339634641)
            ·
              refine ⟨1784782278107549504725981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379709704143399339634641 1784782278107549504725981)
              ·
                refine ⟨669293354290331064272243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1784782278107549504725981 669293354290331064272243)
                ·
                  refine ⟨1003940031435496596408365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669293354290331064272243 1003940031435496596408365)
                  ·
                    refine ⟨376477511788311223653137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1003940031435496596408365 376477511788311223653137)
                    ·
                      rfl

theorem cell22_1099781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_1099781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099781 prefixEnd_1099781 := by exact prefixLift 1099781
  have htrace : WordTrace (prefixWord ++ tailWord_1099781) baseStart_1099781 baseEnd_1099781 := by
    simpa [prefixWord, tailWord_1099781, baseEnd_1099781] using wordTrace_append hprefix tailTrace_1099781
  have hstable : (prefixWord ++ tailWord_1099781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099781).length < 2 ^ (prefixWord ++ tailWord_1099781).sum := by decide
  have hdescent : baseEnd_1099781 < baseStart_1099781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099824 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_1099824 : Nat := 118140960795 + 1099824 * 2 ^ 59
def prefixEnd_1099824 : Nat := 4983230072969 + 3 ^ 40 * 1099824 * 2
def baseEnd_1099824 : Nat := 376492231567073444828005

theorem tailTrace_1099824 : CollatzResearch.WordTrace tailWord_1099824 prefixEnd_1099824 376492231567073444828005 := by
  unfold tailWord_1099824
  simp only [CollatzResearch.WordTrace]
  refine ⟨20056938383766478915001263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26742584511688638553335017 20056938383766478915001263)
  ·
    refine ⟨30085407575649718372501895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20056938383766478915001263 30085407575649718372501895)
    ·
      refine ⟨45128111363474577558752843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30085407575649718372501895 45128111363474577558752843)
      ·
        refine ⟨67692167045211866338129265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45128111363474577558752843 67692167045211866338129265)
        ·
          refine ⟨50769125283908899753596949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67692167045211866338129265 50769125283908899753596949)
          ·
            refine ⟨2379802747683229675949857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50769125283908899753596949 2379802747683229675949857)
            ·
              refine ⟨1784852060762422256962393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379802747683229675949857 1784852060762422256962393)
              ·
                refine ⟨1338639045571816692721795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784852060762422256962393 1338639045571816692721795)
                ·
                  refine ⟨2007958568357725039082693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338639045571816692721795 2007958568357725039082693)
                  ·
                    refine ⟨376492231567073444828005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2007958568357725039082693 376492231567073444828005)
                    ·
                      rfl

theorem cell22_1099824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_1099824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099824 prefixEnd_1099824 := by exact prefixLift 1099824
  have htrace : WordTrace (prefixWord ++ tailWord_1099824) baseStart_1099824 baseEnd_1099824 := by
    simpa [prefixWord, tailWord_1099824, baseEnd_1099824] using wordTrace_append hprefix tailTrace_1099824
  have hstable : (prefixWord ++ tailWord_1099824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099824).length < 2 ^ (prefixWord ++ tailWord_1099824).sum := by decide
  have hdescent : baseEnd_1099824 < baseStart_1099824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099837 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1099837 : Nat := 118140960795 + 1099837 * 2 ^ 59
def prefixEnd_1099837 : Nat := 4983230072969 + 3 ^ 40 * 1099837 * 2
def baseEnd_1099837 : Nat := 376496681732745744252965

theorem tailTrace_1099837 : CollatzResearch.WordTrace tailWord_1099837 prefixEnd_1099837 376496681732745744252965 := by
  unfold tailWord_1099837
  simp only [CollatzResearch.WordTrace]
  refine ⟨40114350916485861050225765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26742900610990574033483843 40114350916485861050225765)
  ·
    refine ⟨7521440796841098946917331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40114350916485861050225765 7521440796841098946917331)
    ·
      refine ⟨11282161195261648420375997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7521440796841098946917331 11282161195261648420375997)
      ·
        refine ⟨4230810448223118157640999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11282161195261648420375997 4230810448223118157640999)
        ·
          refine ⟨6346215672334677236461499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230810448223118157640999 6346215672334677236461499)
          ·
            refine ⟨9519323508502015854692249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6346215672334677236461499 9519323508502015854692249)
            ·
              refine ⟨7139492631376511891019187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9519323508502015854692249 7139492631376511891019187)
              ·
                refine ⟨10709238947064767836528781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139492631376511891019187 10709238947064767836528781)
                ·
                  refine ⟨4015964605149287938698293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10709238947064767836528781 4015964605149287938698293)
                  ·
                    refine ⟨376496681732745744252965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4015964605149287938698293 376496681732745744252965)
                    ·
                      rfl

theorem cell22_1099837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1099837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099837 prefixEnd_1099837 := by exact prefixLift 1099837
  have htrace : WordTrace (prefixWord ++ tailWord_1099837) baseStart_1099837 baseEnd_1099837 := by
    simpa [prefixWord, tailWord_1099837, baseEnd_1099837] using wordTrace_append hprefix tailTrace_1099837
  have hstable : (prefixWord ++ tailWord_1099837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099837).length < 2 ^ (prefixWord ++ tailWord_1099837).sum := by decide
  have hdescent : baseEnd_1099837 < baseStart_1099837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099839 : List Nat := [1, 1, 2, 2, 3, 1, 5, 3, 4]
def baseStart_1099839 : Nat := 118140960795 + 1099839 * 2 ^ 59
def prefixEnd_1099839 : Nat := 4983230072969 + 3 ^ 40 * 1099839 * 2
def baseEnd_1099839 : Nat := 125499122124539468567653

theorem tailTrace_1099839 : CollatzResearch.WordTrace tailWord_1099839 prefixEnd_1099839 125499122124539468567653 := by
  unfold tailWord_1099839
  simp only [CollatzResearch.WordTrace]
  refine ⟨40114423862478615391798571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26742949241652410261199047 40114423862478615391798571)
  ·
    refine ⟨60171635793717923087697857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40114423862478615391798571 60171635793717923087697857)
    ·
      refine ⟨45128726845288442315773393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60171635793717923087697857 45128726845288442315773393)
      ·
        refine ⟨33846545133966331736830045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45128726845288442315773393 33846545133966331736830045)
        ·
          refine ⟨12692454425237374401311267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33846545133966331736830045 12692454425237374401311267)
          ·
            refine ⟨19038681637856061601966901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12692454425237374401311267 19038681637856061601966901)
            ·
              refine ⟨1784876403549005775184397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19038681637856061601966901 1784876403549005775184397)
              ·
                refine ⟨669328651330877165694149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1784876403549005775184397 669328651330877165694149)
                ·
                  refine ⟨125499122124539468567653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669328651330877165694149 125499122124539468567653)
                  ·
                    rfl

theorem cell22_1099839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 4].length) (baseStart_1099839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099839 prefixEnd_1099839 := by exact prefixLift 1099839
  have htrace : WordTrace (prefixWord ++ tailWord_1099839) baseStart_1099839 baseEnd_1099839 := by
    simpa [prefixWord, tailWord_1099839, baseEnd_1099839] using wordTrace_append hprefix tailTrace_1099839
  have hstable : (prefixWord ++ tailWord_1099839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099839).length < 2 ^ (prefixWord ++ tailWord_1099839).sum := by decide
  have hdescent : baseEnd_1099839 < baseStart_1099839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099852 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_1099852 : Nat := 118140960795 + 1099852 * 2 ^ 59
def prefixEnd_1099852 : Nat := 4983230072969 + 3 ^ 40 * 1099852 * 2
def baseEnd_1099852 : Nat := 376501816539290705127919

theorem tailTrace_1099852 : CollatzResearch.WordTrace tailWord_1099852 prefixEnd_1099852 376501816539290705127919 := by
  unfold tailWord_1099852
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057449005715759306010905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26743265340954345741347873 20057449005715759306010905)
  ·
    refine ⟨15043086754286819479508179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20057449005715759306010905 15043086754286819479508179)
    ·
      refine ⟨22564630131430229219262269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15043086754286819479508179 22564630131430229219262269)
      ·
        refine ⟨8461736299286335957223351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22564630131430229219262269 8461736299286335957223351)
        ·
          refine ⟨12692604448929503935835027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8461736299286335957223351 12692604448929503935835027)
          ·
            refine ⟨19038906673394255903752541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12692604448929503935835027 19038906673394255903752541)
            ·
              refine ⟨7139590002522845963907203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19038906673394255903752541 7139590002522845963907203)
              ·
                refine ⟨10709385003784268945860805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139590002522845963907203 10709385003784268945860805)
                ·
                  refine ⟨2008009688209550427348901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10709385003784268945860805 2008009688209550427348901)
                  ·
                    refine ⟨376501816539290705127919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008009688209550427348901 376501816539290705127919)
                    ·
                      rfl

theorem cell22_1099852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_1099852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099852 prefixEnd_1099852 := by exact prefixLift 1099852
  have htrace : WordTrace (prefixWord ++ tailWord_1099852) baseStart_1099852 baseEnd_1099852 := by
    simpa [prefixWord, tailWord_1099852, baseEnd_1099852] using wordTrace_append hprefix tailTrace_1099852
  have hstable : (prefixWord ++ tailWord_1099852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099852).length < 2 ^ (prefixWord ++ tailWord_1099852).sum := by decide
  have hdescent : baseEnd_1099852 < baseStart_1099852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099854 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_1099854 : Nat := 118140960795 + 1099854 * 2 ^ 59
def prefixEnd_1099854 : Nat := 4983230072969 + 3 ^ 40 * 1099854 * 2
def baseEnd_1099854 : Nat := 376502501180163366577913

theorem tailTrace_1099854 : CollatzResearch.WordTrace tailWord_1099854 prefixEnd_1099854 376502501180163366577913 := by
  unfold tailWord_1099854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014371369678034119199327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26743313971616181969063077 5014371369678034119199327)
  ·
    refine ⟨7521557054517051178798991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5014371369678034119199327 7521557054517051178798991)
    ·
      refine ⟨11282335581775576768198487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7521557054517051178798991 11282335581775576768198487)
      ·
        refine ⟨16923503372663365152297731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11282335581775576768198487 16923503372663365152297731)
        ·
          refine ⟨25385255058995047728446597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16923503372663365152297731 25385255058995047728446597)
          ·
            refine ⟨4759735323561571449083737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25385255058995047728446597 4759735323561571449083737)
            ·
              refine ⟨3569801492671178586812803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759735323561571449083737 3569801492671178586812803)
              ·
                refine ⟨5354702239006767880219205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569801492671178586812803 5354702239006767880219205)
                ·
                  refine ⟨1004006669813768977541101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5354702239006767880219205 1004006669813768977541101)
                  ·
                    refine ⟨376502501180163366577913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1004006669813768977541101 376502501180163366577913)
                    ·
                      rfl

theorem cell22_1099854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_1099854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1099854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1099854 prefixEnd_1099854 := by exact prefixLift 1099854
  have htrace : WordTrace (prefixWord ++ tailWord_1099854) baseStart_1099854 baseEnd_1099854 := by
    simpa [prefixWord, tailWord_1099854, baseEnd_1099854] using wordTrace_append hprefix tailTrace_1099854
  have hstable : (prefixWord ++ tailWord_1099854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099854).length < 2 ^ (prefixWord ++ tailWord_1099854).sum := by decide
  have hdescent : baseEnd_1099854 < baseStart_1099854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100004 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1100004 : Nat := 118140960795 + 1100004 * 2 ^ 59
def prefixEnd_1100004 : Nat := 4983230072969 + 3 ^ 40 * 1100004 * 2
def baseEnd_1100004 : Nat := 376553849245612975327453

theorem tailTrace_1100004 : CollatzResearch.WordTrace tailWord_1100004 prefixEnd_1100004 376553849245612975327453 := by
  unfold tailWord_1100004
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060220953440424285777533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26746961271253899047703377 20060220953440424285777533)
  ·
    refine ⟨7522582857540159107166575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20060220953440424285777533 7522582857540159107166575)
    ·
      refine ⟨11283874286310238660749863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7522582857540159107166575 11283874286310238660749863)
      ·
        refine ⟨16925811429465357991124795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11283874286310238660749863 16925811429465357991124795)
        ·
          refine ⟨25388717144198036986687193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16925811429465357991124795 25388717144198036986687193)
          ·
            refine ⟨19041537858148527740015395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25388717144198036986687193 19041537858148527740015395)
            ·
              refine ⟨28562306787222791610023093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19041537858148527740015395 28562306787222791610023093)
              ·
                refine ⟨2677716261302136713439665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28562306787222791610023093 2677716261302136713439665)
                ·
                  refine ⟨2008287195976602535079749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677716261302136713439665 2008287195976602535079749)
                  ·
                    refine ⟨376553849245612975327453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008287195976602535079749 376553849245612975327453)
                    ·
                      rfl

theorem cell22_1100004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1100004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100004 prefixEnd_1100004 := by exact prefixLift 1100004
  have htrace : WordTrace (prefixWord ++ tailWord_1100004) baseStart_1100004 baseEnd_1100004 := by
    simpa [prefixWord, tailWord_1100004, baseEnd_1100004] using wordTrace_append hprefix tailTrace_1100004
  have hstable : (prefixWord ++ tailWord_1100004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100004).length < 2 ^ (prefixWord ++ tailWord_1100004).sum := by decide
  have hdescent : baseEnd_1100004 < baseStart_1100004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100008 : List Nat := [2, 1, 4, 1, 2, 4, 1, 3, 4]
def baseStart_1100008 : Nat := 118140960795 + 1100008 * 2 ^ 59
def prefixEnd_1100008 : Nat := 4983230072969 + 3 ^ 40 * 1100008 * 2
def baseEnd_1100008 : Nat := 125518406175786099409147

theorem tailTrace_1100008 : CollatzResearch.WordTrace tailWord_1100008 prefixEnd_1100008 125518406175786099409147 := by
  unfold tailWord_1100008
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060293899433178627350339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26747058532577571503133785 20060293899433178627350339)
  ·
    refine ⟨30090440849149767941025509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20060293899433178627350339 30090440849149767941025509)
    ·
      refine ⟨5641957659215581488942283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30090440849149767941025509 5641957659215581488942283)
      ·
        refine ⟨8462936488823372233413425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641957659215581488942283 8462936488823372233413425)
        ·
          refine ⟨6347202366617529175060069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8462936488823372233413425 6347202366617529175060069)
          ·
            refine ⟨1190100443740786720323763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6347202366617529175060069 1190100443740786720323763)
            ·
              refine ⟨1785150665611180080485645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190100443740786720323763 1785150665611180080485645)
              ·
                refine ⟨669431499604192530182117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1785150665611180080485645 669431499604192530182117)
                ·
                  refine ⟨125518406175786099409147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669431499604192530182117 125518406175786099409147)
                  ·
                    rfl

theorem cell22_1100008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_1100008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100008 prefixEnd_1100008 := by exact prefixLift 1100008
  have htrace : WordTrace (prefixWord ++ tailWord_1100008) baseStart_1100008 baseEnd_1100008 := by
    simpa [prefixWord, tailWord_1100008, baseEnd_1100008] using wordTrace_append hprefix tailTrace_1100008
  have hstable : (prefixWord ++ tailWord_1100008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100008).length < 2 ^ (prefixWord ++ tailWord_1100008).sum := by decide
  have hdescent : baseEnd_1100008 < baseStart_1100008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100036 : List Nat := [2, 3, 2, 2, 3, 1, 2, 7]
def baseStart_1100036 : Nat := 118140960795 + 1100036 * 2 ^ 59
def prefixEnd_1100036 : Nat := 4983230072969 + 3 ^ 40 * 1100036 * 2
def baseEnd_1100036 : Nat := 41840533722175062058595

theorem tailTrace_1100036 : CollatzResearch.WordTrace tailWord_1100036 prefixEnd_1100036 41840533722175062058595 := by
  unfold tailWord_1100036
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060804521382459018359981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26747739361843278691146641 20060804521382459018359981)
  ·
    refine ⟨7522801695518422131884993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20060804521382459018359981 7522801695518422131884993)
    ·
      refine ⟨5642101271638816598913745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7522801695518422131884993 5642101271638816598913745)
      ·
        refine ⟨4231575953729112449185309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5642101271638816598913745 4231575953729112449185309)
        ·
          refine ⟨1586840982648417168444491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4231575953729112449185309 1586840982648417168444491)
          ·
            refine ⟨2380261473972625752666737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586840982648417168444491 2380261473972625752666737)
            ·
              refine ⟨1785196105479469314500053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2380261473972625752666737 1785196105479469314500053)
              ·
                refine ⟨41840533722175062058595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1785196105479469314500053 41840533722175062058595)
                ·
                  rfl

theorem cell22_1100036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 7].length) (baseStart_1100036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100036 prefixEnd_1100036 := by exact prefixLift 1100036
  have htrace : WordTrace (prefixWord ++ tailWord_1100036) baseStart_1100036 baseEnd_1100036 := by
    simpa [prefixWord, tailWord_1100036, baseEnd_1100036] using wordTrace_append hprefix tailTrace_1100036
  have hstable : (prefixWord ++ tailWord_1100036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100036).length < 2 ^ (prefixWord ++ tailWord_1100036).sum := by decide
  have hdescent : baseEnd_1100036 < baseStart_1100036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100040 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 2, 3]
def baseStart_1100040 : Nat := 118140960795 + 1100040 * 2 ^ 59
def prefixEnd_1100040 : Nat := 4983230072969 + 3 ^ 40 * 1100040 * 2
def baseEnd_1100040 : Nat := 376566172781320881427343

theorem tailTrace_1100040 : CollatzResearch.WordTrace tailWord_1100040 prefixEnd_1100040 376566172781320881427343 := by
  unfold tailWord_1100040
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060877467375213359932787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26747836623166951146577049 20060877467375213359932787)
  ·
    refine ⟨30091316201062820039899181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20060877467375213359932787 30091316201062820039899181)
    ·
      refine ⟨11284243575398557514962193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30091316201062820039899181 11284243575398557514962193)
      ·
        refine ⟨8463182681548918136221645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11284243575398557514962193 8463182681548918136221645)
        ·
          refine ⟨3173693505580844301083117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8463182681548918136221645 3173693505580844301083117)
          ·
            refine ⟨1190135064592816612906169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3173693505580844301083117 1190135064592816612906169)
            ·
              refine ⟨892601298444612459679627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190135064592816612906169 892601298444612459679627)
              ·
                refine ⟨1338901947666918689519441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892601298444612459679627 1338901947666918689519441)
                ·
                  refine ⟨1004176460750189017139581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1338901947666918689519441 1004176460750189017139581)
                  ·
                    refine ⟨376566172781320881427343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1004176460750189017139581 376566172781320881427343)
                    ·
                      rfl

theorem cell22_1100040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_1100040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100040 prefixEnd_1100040 := by exact prefixLift 1100040
  have htrace : WordTrace (prefixWord ++ tailWord_1100040) baseStart_1100040 baseEnd_1100040 := by
    simpa [prefixWord, tailWord_1100040, baseEnd_1100040] using wordTrace_append hprefix tailTrace_1100040
  have hstable : (prefixWord ++ tailWord_1100040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100040).length < 2 ^ (prefixWord ++ tailWord_1100040).sum := by decide
  have hdescent : baseEnd_1100040 < baseStart_1100040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100128 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_1100128 : Nat := 118140960795 + 1100128 * 2 ^ 59
def prefixEnd_1100128 : Nat := 4983230072969 + 3 ^ 40 * 1100128 * 2
def baseEnd_1100128 : Nat := 376596296979717985227073

theorem tailTrace_1100128 : CollatzResearch.WordTrace tailWord_1100128 prefixEnd_1100128 376596296979717985227073 := by
  unfold tailWord_1100128
  simp only [CollatzResearch.WordTrace]
  refine ⟨20062482279215808874534519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26749976372287745166046025 20062482279215808874534519)
  ·
    refine ⟨30093723418823713311801779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20062482279215808874534519 30093723418823713311801779)
    ·
      refine ⟨45140585128235569967702669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30093723418823713311801779 45140585128235569967702669)
      ·
        refine ⟨16927719423088338737888501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45140585128235569967702669 16927719423088338737888501)
        ·
          refine ⟨1586973695914531756677047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16927719423088338737888501 1586973695914531756677047)
          ·
            refine ⟨2380460543871797635015571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586973695914531756677047 2380460543871797635015571)
            ·
              refine ⟨3570690815807696452523357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380460543871797635015571 3570690815807696452523357)
              ·
                refine ⟨1339009055927886169696259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3570690815807696452523357 1339009055927886169696259)
                ·
                  refine ⟨2008513583891829254544389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339009055927886169696259 2008513583891829254544389)
                  ·
                    refine ⟨376596296979717985227073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008513583891829254544389 376596296979717985227073)
                    ·
                      rfl

theorem cell22_1100128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_1100128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100128 prefixEnd_1100128 := by exact prefixLift 1100128
  have htrace : WordTrace (prefixWord ++ tailWord_1100128) baseStart_1100128 baseEnd_1100128 := by
    simpa [prefixWord, tailWord_1100128, baseEnd_1100128] using wordTrace_append hprefix tailTrace_1100128
  have hstable : (prefixWord ++ tailWord_1100128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100128).length < 2 ^ (prefixWord ++ tailWord_1100128).sum := by decide
  have hdescent : baseEnd_1100128 < baseStart_1100128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100162 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1100162 : Nat := 118140960795 + 1100162 * 2 ^ 59
def prefixEnd_1100162 : Nat := 4983230072969 + 3 ^ 40 * 1100162 * 2
def baseEnd_1100162 : Nat := 376607935874553229876969

theorem tailTrace_1100162 : CollatzResearch.WordTrace tailWord_1100162 prefixEnd_1100162 376607935874553229876969 := by
  unfold tailWord_1100162
  simp only [CollatzResearch.WordTrace]
  refine ⟨10031551160077110388951685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26750803093538961037204493 10031551160077110388951685)
  ·
    refine ⟨1880915842514458197928441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10031551160077110388951685 1880915842514458197928441)
    ·
      refine ⟨1410686881885843648446331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1880915842514458197928441 1410686881885843648446331)
      ·
        refine ⟨2116030322828765472669497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410686881885843648446331 2116030322828765472669497)
        ·
          refine ⟨1587022742121574104502123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2116030322828765472669497 1587022742121574104502123)
          ·
            refine ⟨2380534113182361156753185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587022742121574104502123 2380534113182361156753185)
            ·
              refine ⟨1785400584886770867564889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2380534113182361156753185 1785400584886770867564889)
              ·
                refine ⟨1339050438665078150673667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785400584886770867564889 1339050438665078150673667)
                ·
                  refine ⟨2008575657997617226010501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339050438665078150673667 2008575657997617226010501)
                  ·
                    refine ⟨376607935874553229876969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008575657997617226010501 376607935874553229876969)
                    ·
                      rfl

theorem cell22_1100162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1100162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100162 prefixEnd_1100162 := by exact prefixLift 1100162
  have htrace : WordTrace (prefixWord ++ tailWord_1100162) baseStart_1100162 baseEnd_1100162 := by
    simpa [prefixWord, tailWord_1100162, baseEnd_1100162] using wordTrace_append hprefix tailTrace_1100162
  have hstable : (prefixWord ++ tailWord_1100162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100162).length < 2 ^ (prefixWord ++ tailWord_1100162).sum := by decide
  have hdescent : baseEnd_1100162 < baseStart_1100162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100171 : List Nat := [1, 1, 1, 1, 4, 4, 4, 6]
def baseStart_1100171 : Nat := 118140960795 + 1100171 * 2 ^ 59
def prefixEnd_1100171 : Nat := 4983230072969 + 3 ^ 40 * 1100171 * 2
def baseEnd_1100171 : Nat := 41845668528720022933549

theorem tailTrace_1100171 : CollatzResearch.WordTrace tailWord_1100171 prefixEnd_1100171 41845668528720022933549 := by
  unfold tailWord_1100171
  simp only [CollatzResearch.WordTrace]
  refine ⟨40126532897275836092884367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26751021931517224061922911 40126532897275836092884367)
  ·
    refine ⟨60189799345913754139326551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40126532897275836092884367 60189799345913754139326551)
    ·
      refine ⟨90284699018870631208989827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60189799345913754139326551 90284699018870631208989827)
      ·
        refine ⟨135427048528305946813484741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90284699018870631208989827 135427048528305946813484741)
        ·
          refine ⟨25392571599057365027528389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135427048528305946813484741 25392571599057365027528389)
          ·
            refine ⟨4761107174823255942661573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25392571599057365027528389 4761107174823255942661573)
            ·
              refine ⟨892707595279360489249045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4761107174823255942661573 892707595279360489249045)
              ·
                refine ⟨41845668528720022933549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 892707595279360489249045 41845668528720022933549)
                ·
                  rfl

theorem cell22_1100171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 6].length) (baseStart_1100171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100171 prefixEnd_1100171 := by exact prefixLift 1100171
  have htrace : WordTrace (prefixWord ++ tailWord_1100171) baseStart_1100171 baseEnd_1100171 := by
    simpa [prefixWord, tailWord_1100171, baseEnd_1100171] using wordTrace_append hprefix tailTrace_1100171
  have hstable : (prefixWord ++ tailWord_1100171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100171).length < 2 ^ (prefixWord ++ tailWord_1100171).sum := by decide
  have hdescent : baseEnd_1100171 < baseStart_1100171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100190 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1100190 : Nat := 118140960795 + 1100190 * 2 ^ 59
def prefixEnd_1100190 : Nat := 4983230072969 + 3 ^ 40 * 1100190 * 2
def baseEnd_1100190 : Nat := 376617520846770490176883

theorem tailTrace_1100190 : CollatzResearch.WordTrace tailWord_1100190 prefixEnd_1100190 376617520846770490176883 := by
  unfold tailWord_1100190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015903235525875292228253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26751483922804668225217349 5015903235525875292228253)
  ·
    refine ⟨1880963713322203234585595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5015903235525875292228253 1880963713322203234585595)
    ·
      refine ⟨2821445569983304851878393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880963713322203234585595 2821445569983304851878393)
      ·
        refine ⟨2116084177487478638908795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2821445569983304851878393 2116084177487478638908795)
        ·
          refine ⟨3174126266231217958363193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116084177487478638908795 3174126266231217958363193)
          ·
            refine ⟨2380594699673413468772395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3174126266231217958363193 2380594699673413468772395)
            ·
              refine ⟨3570892049510120203158593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380594699673413468772395 3570892049510120203158593)
              ·
                refine ⟨2678169037132590152368945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3570892049510120203158593 2678169037132590152368945)
                ·
                  refine ⟨2008626777849442614276709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2678169037132590152368945 2008626777849442614276709)
                  ·
                    refine ⟨376617520846770490176883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008626777849442614276709 376617520846770490176883)
                    ·
                      rfl

theorem cell22_1100190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1100190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100190 prefixEnd_1100190 := by exact prefixLift 1100190
  have htrace : WordTrace (prefixWord ++ tailWord_1100190) baseStart_1100190 baseEnd_1100190 := by
    simpa [prefixWord, tailWord_1100190, baseEnd_1100190] using wordTrace_append hprefix tailTrace_1100190
  have hstable : (prefixWord ++ tailWord_1100190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100190).length < 2 ^ (prefixWord ++ tailWord_1100190).sum := by decide
  have hdescent : baseEnd_1100190 < baseStart_1100190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100278 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1100278 : Nat := 118140960795 + 1100278 * 2 ^ 59
def prefixEnd_1100278 : Nat := 4983230072969 + 3 ^ 40 * 1100278 * 2
def baseEnd_1100278 : Nat := 125549215015055864658871

theorem tailTrace_1100278 : CollatzResearch.WordTrace tailWord_1100278 prefixEnd_1100278 125549215015055864658871 := by
  unfold tailWord_1100278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2508152219243012085439343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26753623671925462244686325 2508152219243012085439343)
  ·
    refine ⟨3762228328864518128159015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2508152219243012085439343 3762228328864518128159015)
    ·
      refine ⟨5643342493296777192238523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3762228328864518128159015 5643342493296777192238523)
      ·
        refine ⟨8465013739945165788357785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643342493296777192238523 8465013739945165788357785)
        ·
          refine ⟨6348760304958874341268339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8465013739945165788357785 6348760304958874341268339)
          ·
            refine ⟨9523140457438311511902509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348760304958874341268339 9523140457438311511902509)
            ·
              refine ⟨3571177671539366816963441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9523140457438311511902509 3571177671539366816963441)
              ·
                refine ⟨2678383253654525112722581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571177671539366816963441 2678383253654525112722581)
                ·
                  refine ⟨125549215015055864658871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2678383253654525112722581 125549215015055864658871)
                  ·
                    rfl

theorem cell22_1100278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1100278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100278 prefixEnd_1100278 := by exact prefixLift 1100278
  have htrace : WordTrace (prefixWord ++ tailWord_1100278) baseStart_1100278 baseEnd_1100278 := by
    simpa [prefixWord, tailWord_1100278, baseEnd_1100278] using wordTrace_append hprefix tailTrace_1100278
  have hstable : (prefixWord ++ tailWord_1100278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100278).length < 2 ^ (prefixWord ++ tailWord_1100278).sum := by decide
  have hdescent : baseEnd_1100278 < baseStart_1100278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100291 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 1, 6]
def baseStart_1100291 : Nat := 118140960795 + 1100291 * 2 ^ 59
def prefixEnd_1100291 : Nat := 4983230072969 + 3 ^ 40 * 1100291 * 2
def baseEnd_1100291 : Nat := 376652095210839893401573

theorem tailTrace_1100291 : CollatzResearch.WordTrace tailWord_1100291 prefixEnd_1100291 376652095210839893401573 := by
  unfold tailWord_1100291
  simp only [CollatzResearch.WordTrace]
  refine ⟨40130909656841096587252727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26753939771227397724835151 40130909656841096587252727)
  ·
    refine ⟨60196364485261644880879091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40130909656841096587252727 60196364485261644880879091)
    ·
      refine ⟨90294546727892467321318637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60196364485261644880879091 90294546727892467321318637)
      ·
        refine ⟨33860455022959675245494489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90294546727892467321318637 33860455022959675245494489)
        ·
          refine ⟨25395341267219756434120867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33860455022959675245494489 25395341267219756434120867)
          ·
            refine ⟨38093011900829634651181301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25395341267219756434120867 38093011900829634651181301)
            ·
              refine ⟨3571219865702778248548247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38093011900829634651181301 3571219865702778248548247)
              ·
                refine ⟨5356829798554167372822371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571219865702778248548247 5356829798554167372822371)
                ·
                  refine ⟨8035244697831251059233557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356829798554167372822371 8035244697831251059233557)
                  ·
                    refine ⟨376652095210839893401573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8035244697831251059233557 376652095210839893401573)
                    ·
                      rfl

theorem cell22_1100291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_1100291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100291 prefixEnd_1100291 := by exact prefixLift 1100291
  have htrace : WordTrace (prefixWord ++ tailWord_1100291) baseStart_1100291 baseEnd_1100291 := by
    simpa [prefixWord, tailWord_1100291, baseEnd_1100291] using wordTrace_append hprefix tailTrace_1100291
  have hstable : (prefixWord ++ tailWord_1100291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100291).length < 2 ^ (prefixWord ++ tailWord_1100291).sum := by decide
  have hdescent : baseEnd_1100291 < baseStart_1100291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100336 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_1100336 : Nat := 118140960795 + 1100336 * 2 ^ 59
def prefixEnd_1100336 : Nat := 4983230072969 + 3 ^ 40 * 1100336 * 2
def baseEnd_1100336 : Nat := 376667499630474776026435

theorem tailTrace_1100336 : CollatzResearch.WordTrace tailWord_1100336 prefixEnd_1100336 376667499630474776026435 := by
  unfold tailWord_1100336
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066275470839034636320431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26755033961118712848427241 20066275470839034636320431)
  ·
    refine ⟨30099413206258551954480647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20066275470839034636320431 30099413206258551954480647)
    ·
      refine ⟨45149119809387827931720971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30099413206258551954480647 45149119809387827931720971)
      ·
        refine ⟨67723679714081741897581457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45149119809387827931720971 67723679714081741897581457)
        ·
          refine ⟨50792759785561306423186093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67723679714081741897581457 50792759785561306423186093)
          ·
            refine ⟨19047284919585489908694785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50792759785561306423186093 19047284919585489908694785)
            ·
              refine ⟨14285463689689117431521089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19047284919585489908694785 14285463689689117431521089)
              ·
                refine ⟨10714097767266838073640817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14285463689689117431521089 10714097767266838073640817)
                ·
                  refine ⟨8035573325450128555230613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10714097767266838073640817 8035573325450128555230613)
                  ·
                    refine ⟨376667499630474776026435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8035573325450128555230613 376667499630474776026435)
                    ·
                      rfl

theorem cell22_1100336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_1100336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100336 prefixEnd_1100336 := by exact prefixLift 1100336
  have htrace : WordTrace (prefixWord ++ tailWord_1100336) baseStart_1100336 baseEnd_1100336 := by
    simpa [prefixWord, tailWord_1100336, baseEnd_1100336] using wordTrace_append hprefix tailTrace_1100336
  have hstable : (prefixWord ++ tailWord_1100336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100336).length < 2 ^ (prefixWord ++ tailWord_1100336).sum := by decide
  have hdescent : baseEnd_1100336 < baseStart_1100336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100351 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 9]
def baseStart_1100351 : Nat := 118140960795 + 1100351 * 2 ^ 59
def prefixEnd_1100351 : Nat := 4983230072969 + 3 ^ 40 * 1100351 * 2
def baseEnd_1100351 : Nat := 125557544812339912300463

theorem tailTrace_1100351 : CollatzResearch.WordTrace tailWord_1100351 prefixEnd_1100351 125557544812339912300463 := by
  unfold tailWord_1100351
  simp only [CollatzResearch.WordTrace]
  refine ⟨40133098036623726834436907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26755398691082484556291271 40133098036623726834436907)
  ·
    refine ⟨60199647054935590251655361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40133098036623726834436907 60199647054935590251655361)
    ·
      refine ⟨45149735291201692688741521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60199647054935590251655361 45149735291201692688741521)
      ·
        refine ⟨33862301468401269516556141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45149735291201692688741521 33862301468401269516556141)
        ·
          refine ⟨12698363050650476068708553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33862301468401269516556141 12698363050650476068708553)
          ·
            refine ⟨9523772287987857051531415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12698363050650476068708553 9523772287987857051531415)
            ·
              refine ⟨14285658431981785577297123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9523772287987857051531415 14285658431981785577297123)
              ·
                refine ⟨21428487647972678365945685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14285658431981785577297123 21428487647972678365945685)
                ·
                  refine ⟨125557544812339912300463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21428487647972678365945685 125557544812339912300463)
                  ·
                    rfl

theorem cell22_1100351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 9].length) (baseStart_1100351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100351 prefixEnd_1100351 := by exact prefixLift 1100351
  have htrace : WordTrace (prefixWord ++ tailWord_1100351) baseStart_1100351 baseEnd_1100351 := by
    simpa [prefixWord, tailWord_1100351, baseEnd_1100351] using wordTrace_append hprefix tailTrace_1100351
  have hstable : (prefixWord ++ tailWord_1100351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100351).length < 2 ^ (prefixWord ++ tailWord_1100351).sum := by decide
  have hdescent : baseEnd_1100351 < baseStart_1100351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100372 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1100372 : Nat := 118140960795 + 1100372 * 2 ^ 59
def prefixEnd_1100372 : Nat := 4983230072969 + 3 ^ 40 * 1100372 * 2
def baseEnd_1100372 : Nat := 376679823166182682126325

theorem tailTrace_1100372 : CollatzResearch.WordTrace tailWord_1100372 prefixEnd_1100372 376679823166182682126325 := by
  unfold tailWord_1100372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066931984773823710475685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26755909313031764947300913 20066931984773823710475685)
  ·
    refine ⟨3762549747145091945714191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20066931984773823710475685 3762549747145091945714191)
    ·
      refine ⟨5643824620717637918571287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3762549747145091945714191 5643824620717637918571287)
      ·
        refine ⟨8465736931076456877856931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643824620717637918571287 8465736931076456877856931)
        ·
          refine ⟨12698605396614685316785397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8465736931076456877856931 12698605396614685316785397)
          ·
            refine ⟨1190494255932626748448631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12698605396614685316785397 1190494255932626748448631)
            ·
              refine ⟨1785741383898940122672947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190494255932626748448631 1785741383898940122672947)
              ·
                refine ⟨2678612075848410184009421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785741383898940122672947 2678612075848410184009421)
                ·
                  refine ⟨1004479528443153819003533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2678612075848410184009421 1004479528443153819003533)
                  ·
                    refine ⟨376679823166182682126325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1004479528443153819003533 376679823166182682126325)
                    ·
                      rfl

theorem cell22_1100372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1100372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100372 prefixEnd_1100372 := by exact prefixLift 1100372
  have htrace : WordTrace (prefixWord ++ tailWord_1100372) baseStart_1100372 baseEnd_1100372 := by
    simpa [prefixWord, tailWord_1100372, baseEnd_1100372] using wordTrace_append hprefix tailTrace_1100372
  have hstable : (prefixWord ++ tailWord_1100372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100372).length < 2 ^ (prefixWord ++ tailWord_1100372).sum := by decide
  have hdescent : baseEnd_1100372 < baseStart_1100372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100385 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 5]
def baseStart_1100385 : Nat := 118140960795 + 1100385 * 2 ^ 59
def prefixEnd_1100385 : Nat := 4983230072969 + 3 ^ 40 * 1100385 * 2
def baseEnd_1100385 : Nat := 125561424443951660517095

theorem tailTrace_1100385 : CollatzResearch.WordTrace tailWord_1100385 prefixEnd_1100385 125561424443951660517095 := by
  unfold tailWord_1100385
  simp only [CollatzResearch.WordTrace]
  refine ⟨40134338118500550641174609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26756225412333700427449739 40134338118500550641174609)
  ·
    refine ⟨30100753588875412980880957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40134338118500550641174609 30100753588875412980880957)
    ·
      refine ⟨11287782595828279867830359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30100753588875412980880957 11287782595828279867830359)
      ·
        refine ⟨16931673893742419801745539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11287782595828279867830359 16931673893742419801745539)
        ·
          refine ⟨25397510840613629702618309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16931673893742419801745539 25397510840613629702618309)
          ·
            refine ⟨4762033282615055569240933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25397510840613629702618309 4762033282615055569240933)
            ·
              refine ⟨892881240490322919232675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4762033282615055569240933 892881240490322919232675)
              ·
                refine ⟨1339321860735484378849013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892881240490322919232675 1339321860735484378849013)
                ·
                  refine ⟨125561424443951660517095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1339321860735484378849013 125561424443951660517095)
                  ·
                    rfl

theorem cell22_1100385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_1100385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100385 prefixEnd_1100385 := by exact prefixLift 1100385
  have htrace : WordTrace (prefixWord ++ tailWord_1100385) baseStart_1100385 baseEnd_1100385 := by
    simpa [prefixWord, tailWord_1100385, baseEnd_1100385] using wordTrace_append hprefix tailTrace_1100385
  have hstable : (prefixWord ++ tailWord_1100385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100385).length < 2 ^ (prefixWord ++ tailWord_1100385).sum := by decide
  have hdescent : baseEnd_1100385 < baseStart_1100385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100462 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1100462 : Nat := 118140960795 + 1100462 * 2 ^ 59
def prefixEnd_1100462 : Nat := 4983230072969 + 3 ^ 40 * 1100462 * 2
def baseEnd_1100462 : Nat := 376710632005452447376049

theorem tailTrace_1100462 : CollatzResearch.WordTrace tailWord_1100462 prefixEnd_1100462 376710632005452447376049 := by
  unfold tailWord_1100462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017143317402699098965955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26758097692814395194485093 5017143317402699098965955)
  ·
    refine ⟨7525714976104048648448933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5017143317402699098965955 7525714976104048648448933)
    ·
      refine ⟨1411071558019509121584175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7525714976104048648448933 1411071558019509121584175)
      ·
        refine ⟨2116607337029263682376263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411071558019509121584175 2116607337029263682376263)
        ·
          refine ⟨3174911005543895523564395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116607337029263682376263 3174911005543895523564395)
          ·
            refine ⟨4762366508315843285346593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174911005543895523564395 4762366508315843285346593)
            ·
              refine ⟨3571774881236882464009945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762366508315843285346593 3571774881236882464009945)
              ·
                refine ⟨2678831160927661848007459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571774881236882464009945 2678831160927661848007459)
                ·
                  refine ⟨4018246741391492772011189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678831160927661848007459 4018246741391492772011189)
                  ·
                    refine ⟨376710632005452447376049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4018246741391492772011189 376710632005452447376049)
                    ·
                      rfl

theorem cell22_1100462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1100462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100462 prefixEnd_1100462 := by exact prefixLift 1100462
  have htrace : WordTrace (prefixWord ++ tailWord_1100462) baseStart_1100462 baseEnd_1100462 := by
    simpa [prefixWord, tailWord_1100462, baseEnd_1100462] using wordTrace_append hprefix tailTrace_1100462
  have hstable : (prefixWord ++ tailWord_1100462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100462).length < 2 ^ (prefixWord ++ tailWord_1100462).sum := by decide
  have hdescent : baseEnd_1100462 < baseStart_1100462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100567 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 3, 4]
def baseStart_1100567 : Nat := 118140960795 + 1100567 * 2 ^ 59
def prefixEnd_1100567 : Nat := 4983230072969 + 3 ^ 40 * 1100567 * 2
def baseEnd_1100567 : Nat := 376746575651267173500727

theorem tailTrace_1100567 : CollatzResearch.WordTrace tailWord_1100567 prefixEnd_1100567 376746575651267173500727 := by
  unfold tailWord_1100567
  simp only [CollatzResearch.WordTrace]
  refine ⟨40140976203841195724299955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26760650802560797149533303 40140976203841195724299955)
  ·
    refine ⟨60211464305761793586449933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40140976203841195724299955 60211464305761793586449933)
    ·
      refine ⟨22579299114660672594918725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60211464305761793586449933 22579299114660672594918725)
      ·
        refine ⟨4233618583998876111547261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22579299114660672594918725 4233618583998876111547261)
        ·
          refine ⟨1587606968999578541830223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4233618583998876111547261 1587606968999578541830223)
          ·
            refine ⟨2381410453499367812745335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587606968999578541830223 2381410453499367812745335)
            ·
              refine ⟨3572115680249051719118003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381410453499367812745335 3572115680249051719118003)
              ·
                refine ⟨5358173520373577578677005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572115680249051719118003 5358173520373577578677005)
                ·
                  refine ⟨2009315070140091592003877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5358173520373577578677005 2009315070140091592003877)
                  ·
                    refine ⟨376746575651267173500727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009315070140091592003877 376746575651267173500727)
                    ·
                      rfl

theorem cell22_1100567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_1100567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100567 prefixEnd_1100567 := by exact prefixLift 1100567
  have htrace : WordTrace (prefixWord ++ tailWord_1100567) baseStart_1100567 baseEnd_1100567 := by
    simpa [prefixWord, tailWord_1100567, baseEnd_1100567] using wordTrace_append hprefix tailTrace_1100567
  have hstable : (prefixWord ++ tailWord_1100567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100567).length < 2 ^ (prefixWord ++ tailWord_1100567).sum := by decide
  have hdescent : baseEnd_1100567 < baseStart_1100567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100584 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1100584 : Nat := 118140960795 + 1100584 * 2 ^ 59
def prefixEnd_1100584 : Nat := 4983230072969 + 3 ^ 40 * 1100584 * 2
def baseEnd_1100584 : Nat := 376752395098684795825675

theorem tailTrace_1100584 : CollatzResearch.WordTrace tailWord_1100584 prefixEnd_1100584 376752395098684795825675 := by
  unfold tailWord_1100584
  simp only [CollatzResearch.WordTrace]
  refine ⟨20070798122389803813834403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26761064163186405085112537 20070798122389803813834403)
  ·
    refine ⟨30106197183584705720751605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20070798122389803813834403 30106197183584705720751605)
    ·
      refine ⟨2822455985961066161320463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30106197183584705720751605 2822455985961066161320463)
      ·
        refine ⟨4233683978941599241980695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2822455985961066161320463 4233683978941599241980695)
        ·
          refine ⟨6350525968412398862971043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233683978941599241980695 6350525968412398862971043)
          ·
            refine ⟨9525788952618598294456565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350525968412398862971043 9525788952618598294456565)
            ·
              refine ⟨893042714307993590105303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9525788952618598294456565 893042714307993590105303)
              ·
                refine ⟨1339564071461990385157955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893042714307993590105303 1339564071461990385157955)
                ·
                  refine ⟨2009346107192985577736933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339564071461990385157955 2009346107192985577736933)
                  ·
                    refine ⟨376752395098684795825675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009346107192985577736933 376752395098684795825675)
                    ·
                      rfl

theorem cell22_1100584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1100584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100584 prefixEnd_1100584 := by exact prefixLift 1100584
  have htrace : WordTrace (prefixWord ++ tailWord_1100584) baseStart_1100584 baseEnd_1100584 := by
    simpa [prefixWord, tailWord_1100584, baseEnd_1100584] using wordTrace_append hprefix tailTrace_1100584
  have hstable : (prefixWord ++ tailWord_1100584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100584).length < 2 ^ (prefixWord ++ tailWord_1100584).sum := by decide
  have hdescent : baseEnd_1100584 < baseStart_1100584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100659 : List Nat := [1, 1, 1, 2, 2, 1, 6, 4, 1, 3]
def baseStart_1100659 : Nat := 118140960795 + 1100659 * 2 ^ 59
def prefixEnd_1100659 : Nat := 4983230072969 + 3 ^ 40 * 1100659 * 2
def baseEnd_1100659 : Nat := 376778069131409600200445

theorem tailTrace_1100659 : CollatzResearch.WordTrace tailWord_1100659 prefixEnd_1100659 376778069131409600200445 := by
  unfold tailWord_1100659
  simp only [CollatzResearch.WordTrace]
  refine ⟨40144331719507895436649031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26762887813005263624432687 40144331719507895436649031)
  ·
    refine ⟨60216497579261843154973547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40144331719507895436649031 60216497579261843154973547)
    ·
      refine ⟨90324746368892764732460321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60216497579261843154973547 90324746368892764732460321)
      ·
        refine ⟨67743559776669573549345241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90324746368892764732460321 67743559776669573549345241)
        ·
          refine ⟨50807669832502180162008931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67743559776669573549345241 50807669832502180162008931)
          ·
            refine ⟨76211504748753270243013397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50807669832502180162008931 76211504748753270243013397)
            ·
              refine ⟨3572414285097809542641253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76211504748753270243013397 3572414285097809542641253)
              ·
                refine ⟨669827678455839289245235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3572414285097809542641253 669827678455839289245235)
                ·
                  refine ⟨1004741517683758933867853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669827678455839289245235 1004741517683758933867853)
                  ·
                    refine ⟨376778069131409600200445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1004741517683758933867853 376778069131409600200445)
                    ·
                      rfl

theorem cell22_1100659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 3].length) (baseStart_1100659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100659 prefixEnd_1100659 := by exact prefixLift 1100659
  have htrace : WordTrace (prefixWord ++ tailWord_1100659) baseStart_1100659 baseEnd_1100659 := by
    simpa [prefixWord, tailWord_1100659, baseEnd_1100659] using wordTrace_append hprefix tailTrace_1100659
  have hstable : (prefixWord ++ tailWord_1100659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100659).length < 2 ^ (prefixWord ++ tailWord_1100659).sum := by decide
  have hdescent : baseEnd_1100659 < baseStart_1100659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100715 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 3, 5]
def baseStart_1100715 : Nat := 118140960795 + 1100715 * 2 ^ 59
def prefixEnd_1100715 : Nat := 4983230072969 + 3 ^ 40 * 1100715 * 2
def baseEnd_1100715 : Nat := 376797239075844120800273

theorem tailTrace_1100715 : CollatzResearch.WordTrace tailWord_1100715 prefixEnd_1100715 376797239075844120800273 := by
  unfold tailWord_1100715
  simp only [CollatzResearch.WordTrace]
  refine ⟨40146374207305017000687599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26764249471536678000458399 40146374207305017000687599)
  ·
    refine ⟨60219561310957525501031399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40146374207305017000687599 60219561310957525501031399)
    ·
      refine ⟨90329341966436288251547099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60219561310957525501031399 90329341966436288251547099)
      ·
        refine ⟨135494012949654432377320649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90329341966436288251547099 135494012949654432377320649)
        ·
          refine ⟨101620509712240824282990487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135494012949654432377320649 101620509712240824282990487)
          ·
            refine ⟨152430764568361236424485731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101620509712240824282990487 152430764568361236424485731)
            ·
              refine ⟨228646146852541854636728597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152430764568361236424485731 228646146852541854636728597)
              ·
                refine ⟨10717788133712899436096653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228646146852541854636728597 10717788133712899436096653)
                ·
                  refine ⟨4019170550142337288536245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10717788133712899436096653 4019170550142337288536245)
                  ·
                    refine ⟨376797239075844120800273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4019170550142337288536245 376797239075844120800273)
                    ·
                      rfl

theorem cell22_1100715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_1100715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100715 prefixEnd_1100715 := by exact prefixLift 1100715
  have htrace : WordTrace (prefixWord ++ tailWord_1100715) baseStart_1100715 baseEnd_1100715 := by
    simpa [prefixWord, tailWord_1100715, baseEnd_1100715] using wordTrace_append hprefix tailTrace_1100715
  have hstable : (prefixWord ++ tailWord_1100715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100715).length < 2 ^ (prefixWord ++ tailWord_1100715).sum := by decide
  have hdescent : baseEnd_1100715 < baseStart_1100715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100747 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 2, 4]
def baseStart_1100747 : Nat := 118140960795 + 1100747 * 2 ^ 59
def prefixEnd_1100747 : Nat := 4983230072969 + 3 ^ 40 * 1100747 * 2
def baseEnd_1100747 : Nat := 376808193329806704000175

theorem tailTrace_1100747 : CollatzResearch.WordTrace tailWord_1100747 prefixEnd_1100747 376808193329806704000175 := by
  unfold tailWord_1100747
  simp only [CollatzResearch.WordTrace]
  refine ⟨40147541343189086465852495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26765027562126057643901663 40147541343189086465852495)
  ·
    refine ⟨60221312014783629698778743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40147541343189086465852495 60221312014783629698778743)
    ·
      refine ⟨90331968022175444548168115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60221312014783629698778743 90331968022175444548168115)
      ·
        refine ⟨135497952033263166822252173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90331968022175444548168115 135497952033263166822252173)
        ·
          refine ⟨50811732012473687558344565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135497952033263166822252173 50811732012473687558344565)
          ·
            refine ⟨4763599876169408208594803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50811732012473687558344565 4763599876169408208594803)
            ·
              refine ⟨7145399814254112312892205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763599876169408208594803 7145399814254112312892205)
              ·
                refine ⟨2679524930345292117334577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7145399814254112312892205 2679524930345292117334577)
                ·
                  refine ⟨2009643697758969088000933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679524930345292117334577 2009643697758969088000933)
                  ·
                    refine ⟨376808193329806704000175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009643697758969088000933 376808193329806704000175)
                    ·
                      rfl

theorem cell22_1100747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_1100747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100747 prefixEnd_1100747 := by exact prefixLift 1100747
  have htrace : WordTrace (prefixWord ++ tailWord_1100747) baseStart_1100747 baseEnd_1100747 := by
    simpa [prefixWord, tailWord_1100747, baseEnd_1100747] using wordTrace_append hprefix tailTrace_1100747
  have hstable : (prefixWord ++ tailWord_1100747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100747).length < 2 ^ (prefixWord ++ tailWord_1100747).sum := by decide
  have hdescent : baseEnd_1100747 < baseStart_1100747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100777 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 9, 3]
def baseStart_1100777 : Nat := 118140960795 + 1100777 * 2 ^ 59
def prefixEnd_1100777 : Nat := 4983230072969 + 3 ^ 40 * 1100777 * 2
def baseEnd_1100777 : Nat := 376818462942896625750083

theorem tailTrace_1100777 : CollatzResearch.WordTrace tailWord_1100777 prefixEnd_1100777 376818462942896625750083 := by
  unfold tailWord_1100777
  simp only [CollatzResearch.WordTrace]
  refine ⟨40148635533080401589444585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26765757022053601059629723 40148635533080401589444585)
  ·
    refine ⟨30111476649810301192083439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40148635533080401589444585 30111476649810301192083439)
    ·
      refine ⟨45167214974715451788125159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30111476649810301192083439 45167214974715451788125159)
      ·
        refine ⟨67750822462073177682187739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45167214974715451788125159 67750822462073177682187739)
        ·
          refine ⟨101626233693109766523281609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67750822462073177682187739 101626233693109766523281609)
          ·
            refine ⟨76219675269832324892461207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101626233693109766523281609 76219675269832324892461207)
            ·
              refine ⟨114329512904748487338691811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76219675269832324892461207 114329512904748487338691811)
              ·
                refine ⟨171494269357122731008037717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114329512904748487338691811 171494269357122731008037717)
                ·
                  refine ⟨1004849234514391002000221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 171494269357122731008037717 1004849234514391002000221)
                  ·
                    refine ⟨376818462942896625750083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1004849234514391002000221 376818462942896625750083)
                    ·
                      rfl

theorem cell22_1100777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_1100777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100777 prefixEnd_1100777 := by exact prefixLift 1100777
  have htrace : WordTrace (prefixWord ++ tailWord_1100777) baseStart_1100777 baseEnd_1100777 := by
    simpa [prefixWord, tailWord_1100777, baseEnd_1100777] using wordTrace_append hprefix tailTrace_1100777
  have hstable : (prefixWord ++ tailWord_1100777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100777).length < 2 ^ (prefixWord ++ tailWord_1100777).sum := by decide
  have hdescent : baseEnd_1100777 < baseStart_1100777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
