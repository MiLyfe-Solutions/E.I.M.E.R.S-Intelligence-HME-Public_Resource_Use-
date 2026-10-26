import V185TrunkScan20Chunk033

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_207573 : List Nat := [1, 3, 2, 5, 1, 1, 7]
def baseStart_207573 : Nat := 118140960795 + 207573 * 2 ^ 59
def prefixEnd_207573 : Nat := 4983230072969 + 3 ^ 40 * 207573 * 2
def baseEnd_207573 : Nat := 10526885915636701568681

theorem tailTrace_207573 : CollatzResearch.WordTrace tailWord_207573 prefixEnd_207573 10526885915636701568681 := by
  unfold tailWord_207573
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570809277005946491139373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5047206184670630994092915 7570809277005946491139373)
  ·
    refine ⟨2839053478877229934177265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7570809277005946491139373 2839053478877229934177265)
    ·
      refine ⟨2129290109157922450632949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2839053478877229934177265 2129290109157922450632949)
      ·
        refine ⟨199620947733555229746839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2129290109157922450632949 199620947733555229746839)
        ·
          refine ⟨299431421600332844620259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199620947733555229746839 299431421600332844620259)
          ·
            refine ⟨449147132400499266930389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299431421600332844620259 449147132400499266930389)
            ·
              refine ⟨10526885915636701568681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 449147132400499266930389 10526885915636701568681)
              ·
                rfl

theorem cell20_207573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 7].length) (baseStart_207573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207573 prefixEnd_207573 := by exact prefixLift 207573
  have htrace : WordTrace (prefixWord ++ tailWord_207573) baseStart_207573 baseEnd_207573 := by
    simpa [prefixWord, tailWord_207573, baseEnd_207573] using wordTrace_append hprefix tailTrace_207573
  have hstable : (prefixWord ++ tailWord_207573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207573).length < 2 ^ (prefixWord ++ tailWord_207573).sum := by decide
  have hdescent : baseEnd_207573 < baseStart_207573 := by decide
  rcases family_descends (prefixWord ++ tailWord_207573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207577 : List Nat := [1, 2, 1, 2, 3, 2, 9]
def baseStart_207577 : Nat := 118140960795 + 207577 * 2 ^ 59
def prefixEnd_207577 : Nat := 4983230072969 + 3 ^ 40 * 207577 * 2
def baseEnd_207577 : Nat := 10527088772191564220531

theorem tailTrace_207577 : CollatzResearch.WordTrace tailWord_207577 prefixEnd_207577 10527088772191564220531 := by
  unfold tailWord_207577
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570955168991455174284985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5047303445994303449523323 7570955168991455174284985)
  ·
    refine ⟨5678216376743591380713739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7570955168991455174284985 5678216376743591380713739)
    ·
      refine ⟨8517324565115387071070609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678216376743591380713739 8517324565115387071070609)
      ·
        refine ⟨6387993423836540303302957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8517324565115387071070609 6387993423836540303302957)
        ·
          refine ⟨2395497533938702613738609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6387993423836540303302957 2395497533938702613738609)
          ·
            refine ⟨1796623150454026960303957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395497533938702613738609 1796623150454026960303957)
            ·
              refine ⟨10527088772191564220531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1796623150454026960303957 10527088772191564220531)
              ·
                rfl

theorem cell20_207577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_207577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207577 prefixEnd_207577 := by exact prefixLift 207577
  have htrace : WordTrace (prefixWord ++ tailWord_207577) baseStart_207577 baseEnd_207577 := by
    simpa [prefixWord, tailWord_207577, baseEnd_207577] using wordTrace_append hprefix tailTrace_207577
  have hstable : (prefixWord ++ tailWord_207577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207577).length < 2 ^ (prefixWord ++ tailWord_207577).sum := by decide
  have hdescent : baseEnd_207577 < baseStart_207577 := by decide
  rcases family_descends (prefixWord ++ tailWord_207577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207587 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_207587 : Nat := 118140960795 + 207587 * 2 ^ 59
def prefixEnd_207587 : Nat := 4983230072969 + 3 ^ 40 * 207587 * 2
def baseEnd_207587 : Nat := 94748363222208487651405

theorem tailTrace_207587 : CollatzResearch.WordTrace tailWord_207587 prefixEnd_207587 94748363222208487651405 := by
  unfold tailWord_207587
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571319898955226882149015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5047546599303484588099343 7571319898955226882149015)
  ·
    refine ⟨11356979848432840323223523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7571319898955226882149015 11356979848432840323223523)
    ·
      refine ⟨17035469772649260484835285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11356979848432840323223523 17035469772649260484835285)
      ·
        refine ⟨399268822796467042613327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 17035469772649260484835285 399268822796467042613327)
        ·
          refine ⟨598903234194700563919991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399268822796467042613327 598903234194700563919991)
          ·
            refine ⟨898354851292050845879987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598903234194700563919991 898354851292050845879987)
            ·
              refine ⟨1347532276938076268819981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898354851292050845879987 1347532276938076268819981)
              ·
                refine ⟨505324603851778600807493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1347532276938076268819981 505324603851778600807493)
                ·
                  refine ⟨94748363222208487651405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505324603851778600807493 94748363222208487651405)
                  ·
                    rfl

theorem cell20_207587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_207587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207587 prefixEnd_207587 := by exact prefixLift 207587
  have htrace : WordTrace (prefixWord ++ tailWord_207587) baseStart_207587 baseEnd_207587 := by
    simpa [prefixWord, tailWord_207587, baseEnd_207587] using wordTrace_append hprefix tailTrace_207587
  have hstable : (prefixWord ++ tailWord_207587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207587).length < 2 ^ (prefixWord ++ tailWord_207587).sum := by decide
  have hdescent : baseEnd_207587 < baseStart_207587 := by decide
  rcases family_descends (prefixWord ++ tailWord_207587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207597 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 3]
def baseStart_207597 : Nat := 118140960795 + 207597 * 2 ^ 59
def prefixEnd_207597 : Nat := 4983230072969 + 3 ^ 40 * 207597 * 2
def baseEnd_207597 : Nat := 94752927494692897318031

theorem tailTrace_207597 : CollatzResearch.WordTrace tailWord_207597 prefixEnd_207597 94752927494692897318031 := by
  unfold tailWord_207597
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571684628918998590013045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5047789752612665726675363 7571684628918998590013045)
  ·
    refine ⟨709845433961156117813723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7571684628918998590013045 709845433961156117813723)
    ·
      refine ⟨1064768150941734176720585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709845433961156117813723 1064768150941734176720585)
      ·
        refine ⟨798576113206300632540439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064768150941734176720585 798576113206300632540439)
        ·
          refine ⟨1197864169809450948810659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798576113206300632540439 1197864169809450948810659)
          ·
            refine ⟨1796796254714176423215989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197864169809450948810659 1796796254714176423215989)
            ·
              refine ⟨168449648879454039676499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1796796254714176423215989 168449648879454039676499)
              ·
                refine ⟨252674473319181059514749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168449648879454039676499 252674473319181059514749)
                ·
                  refine ⟨94752927494692897318031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252674473319181059514749 94752927494692897318031)
                  ·
                    rfl

theorem cell20_207597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_207597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207597 prefixEnd_207597 := by exact prefixLift 207597
  have htrace : WordTrace (prefixWord ++ tailWord_207597) baseStart_207597 baseEnd_207597 := by
    simpa [prefixWord, tailWord_207597, baseEnd_207597] using wordTrace_append hprefix tailTrace_207597
  have hstable : (prefixWord ++ tailWord_207597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207597).length < 2 ^ (prefixWord ++ tailWord_207597).sum := by decide
  have hdescent : baseEnd_207597 < baseStart_207597 := by decide
  rcases family_descends (prefixWord ++ tailWord_207597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207608 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_207608 : Nat := 118140960795 + 207608 * 2 ^ 59
def prefixEnd_207608 : Nat := 4983230072969 + 3 ^ 40 * 207608 * 2
def baseEnd_207608 : Nat := 94757948194425747951319

theorem tailTrace_207608 : CollatzResearch.WordTrace tailWord_207608 prefixEnd_207608 94757948194425747951319 := by
  unfold tailWord_207608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786042915939573734331739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5048057221252764979108985 3786042915939573734331739)
  ·
    refine ⟨5679064373909360601497609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786042915939573734331739 5679064373909360601497609)
    ·
      refine ⟨4259298280432020451123207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5679064373909360601497609 4259298280432020451123207)
      ·
        refine ⟨6388947420648030676684811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259298280432020451123207 6388947420648030676684811)
        ·
          refine ⟨9583421130972046015027217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6388947420648030676684811 9583421130972046015027217)
          ·
            refine ⟨7187565848229034511270413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9583421130972046015027217 7187565848229034511270413)
            ·
              refine ⟨2695337193085887941726405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7187565848229034511270413 2695337193085887941726405)
              ·
                refine ⟨505375723703603989073701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2695337193085887941726405 505375723703603989073701)
                ·
                  refine ⟨94757948194425747951319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505375723703603989073701 94757948194425747951319)
                  ·
                    rfl

theorem cell20_207608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_207608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207608 prefixEnd_207608 := by exact prefixLift 207608
  have htrace : WordTrace (prefixWord ++ tailWord_207608) baseStart_207608 baseEnd_207608 := by
    simpa [prefixWord, tailWord_207608, baseEnd_207608] using wordTrace_append hprefix tailTrace_207608
  have hstable : (prefixWord ++ tailWord_207608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207608).length < 2 ^ (prefixWord ++ tailWord_207608).sum := by decide
  have hdescent : baseEnd_207608 < baseStart_207608 := by decide
  rcases family_descends (prefixWord ++ tailWord_207608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207618 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_207618 : Nat := 118140960795 + 207618 * 2 ^ 59
def prefixEnd_207618 : Nat := 4983230072969 + 3 ^ 40 * 207618 * 2
def baseEnd_207618 : Nat := 94762512466910157617945

theorem tailTrace_207618 : CollatzResearch.WordTrace tailWord_207618 prefixEnd_207618 94762512466910157617945 := by
  unfold tailWord_207618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893112640460729794131877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5048300374561946117685005 1893112640460729794131877)
  ·
    refine ⟨354958620086386836399727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1893112640460729794131877 354958620086386836399727)
    ·
      refine ⟨532437930129580254599591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354958620086386836399727 532437930129580254599591)
      ·
        refine ⟨798656895194370381899387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532437930129580254599591 798656895194370381899387)
        ·
          refine ⟨1197985342791555572849081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798656895194370381899387 1197985342791555572849081)
          ·
            refine ⟨898489007093666679636811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197985342791555572849081 898489007093666679636811)
            ·
              refine ⟨1347733510640500019455217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898489007093666679636811 1347733510640500019455217)
              ·
                refine ⟨1010800132980375014591413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347733510640500019455217 1010800132980375014591413)
                ·
                  refine ⟨94762512466910157617945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1010800132980375014591413 94762512466910157617945)
                  ·
                    rfl

theorem cell20_207618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_207618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207618 prefixEnd_207618 := by exact prefixLift 207618
  have htrace : WordTrace (prefixWord ++ tailWord_207618) baseStart_207618 baseEnd_207618 := by
    simpa [prefixWord, tailWord_207618, baseEnd_207618] using wordTrace_append hprefix tailTrace_207618
  have hstable : (prefixWord ++ tailWord_207618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207618).length < 2 ^ (prefixWord ++ tailWord_207618).sum := by decide
  have hdescent : baseEnd_207618 < baseStart_207618 := by decide
  rcases family_descends (prefixWord ++ tailWord_207618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207652 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_207652 : Nat := 118140960795 + 207652 * 2 ^ 59
def prefixEnd_207652 : Nat := 4983230072969 + 3 ^ 40 * 207652 * 2
def baseEnd_207652 : Nat := 94778030993357150484473

theorem tailTrace_207652 : CollatzResearch.WordTrace tailWord_207652 prefixEnd_207652 94778030993357150484473 := by
  unfold tailWord_207652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786845321859871491632605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5049127095813161988843473 3786845321859871491632605)
  ·
    refine ⟨1420066995697451809362227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3786845321859871491632605 1420066995697451809362227)
    ·
      refine ⟨2130100493546177714043341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1420066995697451809362227 2130100493546177714043341)
      ·
        refine ⟨798787685079816642766253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2130100493546177714043341 798787685079816642766253)
        ·
          refine ⟨299545381904931241037345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 798787685079816642766253 299545381904931241037345)
          ·
            refine ⟨224659036428698430778009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299545381904931241037345 224659036428698430778009)
            ·
              refine ⟨168494277321523823083507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224659036428698430778009 168494277321523823083507)
              ·
                refine ⟨252741415982285734625261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168494277321523823083507 252741415982285734625261)
                ·
                  refine ⟨94778030993357150484473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252741415982285734625261 94778030993357150484473)
                  ·
                    rfl

theorem cell20_207652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_207652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207652 prefixEnd_207652 := by exact prefixLift 207652
  have htrace : WordTrace (prefixWord ++ tailWord_207652) baseStart_207652 baseEnd_207652 := by
    simpa [prefixWord, tailWord_207652, baseEnd_207652] using wordTrace_append hprefix tailTrace_207652
  have hstable : (prefixWord ++ tailWord_207652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207652).length < 2 ^ (prefixWord ++ tailWord_207652).sum := by decide
  have hdescent : baseEnd_207652 < baseStart_207652 := by decide
  rcases family_descends (prefixWord ++ tailWord_207652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207656 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_207656 : Nat := 118140960795 + 207656 * 2 ^ 59
def prefixEnd_207656 : Nat := 4983230072969 + 3 ^ 40 * 207656 * 2
def baseEnd_207656 : Nat := 94779856702350914351123

theorem tailTrace_207656 : CollatzResearch.WordTrace tailWord_207656 prefixEnd_207656 94779856702350914351123 := by
  unfold tailWord_207656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786918267852625833205411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5049224357136834444273881 3786918267852625833205411)
  ·
    refine ⟨5680377401778938749808117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786918267852625833205411 5680377401778938749808117)
    ·
      refine ⟨532535381416775507794511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5680377401778938749808117 532535381416775507794511)
      ·
        refine ⟨798803072125163261691767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532535381416775507794511 798803072125163261691767)
        ·
          refine ⟨1198204608187744892537651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798803072125163261691767 1198204608187744892537651)
          ·
            refine ⟨1797306912281617338806477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198204608187744892537651 1797306912281617338806477)
            ·
              refine ⟨673990092105606502052429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797306912281617338806477 673990092105606502052429)
              ·
                refine ⟨252746284539602438269661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673990092105606502052429 252746284539602438269661)
                ·
                  refine ⟨94779856702350914351123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252746284539602438269661 94779856702350914351123)
                  ·
                    rfl

theorem cell20_207656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_207656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207656 prefixEnd_207656 := by exact prefixLift 207656
  have htrace : WordTrace (prefixWord ++ tailWord_207656) baseStart_207656 baseEnd_207656 := by
    simpa [prefixWord, tailWord_207656, baseEnd_207656] using wordTrace_append hprefix tailTrace_207656
  have hstable : (prefixWord ++ tailWord_207656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207656).length < 2 ^ (prefixWord ++ tailWord_207656).sum := by decide
  have hdescent : baseEnd_207656 < baseStart_207656 := by decide
  rcases family_descends (prefixWord ++ tailWord_207656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207693 : List Nat := [1, 6, 1, 2, 2, 2, 2, 2, 2]
def baseStart_207693 : Nat := 118140960795 + 207693 * 2 ^ 59
def prefixEnd_207693 : Nat := 4983230072969 + 3 ^ 40 * 207693 * 2
def baseEnd_207693 : Nat := 94796744510543230117639

theorem tailTrace_207693 : CollatzResearch.WordTrace tailWord_207693 prefixEnd_207693 94796744510543230117639 := by
  unfold tailWord_207693
  simp only [CollatzResearch.WordTrace]
  refine ⟨7575186036571206985507733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5050124024380804657005155 7575186036571206985507733)
  ·
    refine ⟨355086845464275327445675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7575186036571206985507733 355086845464275327445675)
    ·
      refine ⟨532630268196412991168513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355086845464275327445675 532630268196412991168513)
      ·
        refine ⟨399472701147309743376385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532630268196412991168513 399472701147309743376385)
        ·
          refine ⟨299604525860482307532289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399472701147309743376385 299604525860482307532289)
          ·
            refine ⟨224703394395361730649217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299604525860482307532289 224703394395361730649217)
            ·
              refine ⟨168527545796521297986913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224703394395361730649217 168527545796521297986913)
              ·
                refine ⟨126395659347390973490185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168527545796521297986913 126395659347390973490185)
                ·
                  refine ⟨94796744510543230117639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126395659347390973490185 94796744510543230117639)
                  ·
                    rfl

theorem cell20_207693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_207693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207693 prefixEnd_207693 := by exact prefixLift 207693
  have htrace : WordTrace (prefixWord ++ tailWord_207693) baseStart_207693 baseEnd_207693 := by
    simpa [prefixWord, tailWord_207693, baseEnd_207693] using wordTrace_append hprefix tailTrace_207693
  have hstable : (prefixWord ++ tailWord_207693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207693).length < 2 ^ (prefixWord ++ tailWord_207693).sum := by decide
  have hdescent : baseEnd_207693 < baseStart_207693 := by decide
  rcases family_descends (prefixWord ++ tailWord_207693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207739 : List Nat := [1, 1, 1, 1, 1, 5, 3, 5, 2]
def baseStart_207739 : Nat := 118140960795 + 207739 * 2 ^ 59
def prefixEnd_207739 : Nat := 4983230072969 + 3 ^ 40 * 207739 * 2
def baseEnd_207739 : Nat := 94817740163971514584117

theorem tailTrace_207739 : CollatzResearch.WordTrace tailWord_207739 prefixEnd_207739 94817740163971514584117 := by
  unfold tailWord_207739
  simp only [CollatzResearch.WordTrace]
  refine ⟨7576863794404556841682271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5051242529603037894454847 7576863794404556841682271)
  ·
    refine ⟨11365295691606835262523407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7576863794404556841682271 11365295691606835262523407)
    ·
      refine ⟨17047943537410252893785111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11365295691606835262523407 17047943537410252893785111)
      ·
        refine ⟨25571915306115379340677667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17047943537410252893785111 25571915306115379340677667)
        ·
          refine ⟨38357872959173069011016501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25571915306115379340677667 38357872959173069011016501)
          ·
            refine ⟨3596050589922475219782797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38357872959173069011016501 3596050589922475219782797)
            ·
              refine ⟨1348518971220928207418549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3596050589922475219782797 1348518971220928207418549)
              ·
                refine ⟨126423653551962019445489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1348518971220928207418549 126423653551962019445489)
                ·
                  refine ⟨94817740163971514584117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126423653551962019445489 94817740163971514584117)
                  ·
                    rfl

theorem cell20_207739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 2].length) (baseStart_207739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207739 prefixEnd_207739 := by exact prefixLift 207739
  have htrace : WordTrace (prefixWord ++ tailWord_207739) baseStart_207739 baseEnd_207739 := by
    simpa [prefixWord, tailWord_207739, baseEnd_207739] using wordTrace_append hprefix tailTrace_207739
  have hstable : (prefixWord ++ tailWord_207739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207739).length < 2 ^ (prefixWord ++ tailWord_207739).sum := by decide
  have hdescent : baseEnd_207739 < baseStart_207739 := by decide
  rcases family_descends (prefixWord ++ tailWord_207739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207753 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_207753 : Nat := 118140960795 + 207753 * 2 ^ 59
def prefixEnd_207753 : Nat := 4983230072969 + 3 ^ 40 * 207753 * 2
def baseEnd_207753 : Nat := 94824130145449688117393

theorem tailTrace_207753 : CollatzResearch.WordTrace tailWord_207753 prefixEnd_207753 94824130145449688117393 := by
  unfold tailWord_207753
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577374416353837232691913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5051582944235891488461275 7577374416353837232691913)
  ·
    refine ⟨5683030812265377924518935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7577374416353837232691913 5683030812265377924518935)
    ·
      refine ⟨8524546218398066886778403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5683030812265377924518935 8524546218398066886778403)
      ·
        refine ⟨12786819327597100330167605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524546218398066886778403 12786819327597100330167605)
        ·
          refine ⟨1198764311962228155953213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12786819327597100330167605 1198764311962228155953213)
          ·
            refine ⟨449536616985835558482455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1198764311962228155953213 449536616985835558482455)
            ·
              refine ⟨674304925478753337723683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449536616985835558482455 674304925478753337723683)
              ·
                refine ⟨1011457388218130006585525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674304925478753337723683 1011457388218130006585525)
                ·
                  refine ⟨94824130145449688117393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1011457388218130006585525 94824130145449688117393)
                  ·
                    rfl

theorem cell20_207753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_207753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207753 prefixEnd_207753 := by exact prefixLift 207753
  have htrace : WordTrace (prefixWord ++ tailWord_207753) baseStart_207753 baseEnd_207753 := by
    simpa [prefixWord, tailWord_207753, baseEnd_207753] using wordTrace_append hprefix tailTrace_207753
  have hstable : (prefixWord ++ tailWord_207753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207753).length < 2 ^ (prefixWord ++ tailWord_207753).sum := by decide
  have hdescent : baseEnd_207753 < baseStart_207753 := by decide
  rcases family_descends (prefixWord ++ tailWord_207753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207767 : List Nat := [1, 1, 3, 3, 1, 2, 2, 7]
def baseStart_207767 : Nat := 118140960795 + 207767 * 2 ^ 59
def prefixEnd_207767 : Nat := 4983230072969 + 3 ^ 40 * 207767 * 2
def baseEnd_207767 : Nat := 31610173375642620550223

theorem tailTrace_207767 : CollatzResearch.WordTrace tailWord_207767 prefixEnd_207767 31610173375642620550223 := by
  unfold tailWord_207767
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577885038303117623701555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5051923358868745082467703 7577885038303117623701555)
  ·
    refine ⟨11366827557454676435552333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7577885038303117623701555 11366827557454676435552333)
    ·
      refine ⟨4262560334045503663332125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11366827557454676435552333 4262560334045503663332125)
      ·
        refine ⟨1598460125267063873749547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4262560334045503663332125 1598460125267063873749547)
        ·
          refine ⟨2397690187900595810624321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598460125267063873749547 2397690187900595810624321)
          ·
            refine ⟨1798267640925446857968241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397690187900595810624321 1798267640925446857968241)
            ·
              refine ⟨1348700730694085143476181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798267640925446857968241 1348700730694085143476181)
              ·
                refine ⟨31610173375642620550223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1348700730694085143476181 31610173375642620550223)
                ·
                  rfl

theorem cell20_207767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_207767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207767 prefixEnd_207767 := by exact prefixLift 207767
  have htrace : WordTrace (prefixWord ++ tailWord_207767) baseStart_207767 baseEnd_207767 := by
    simpa [prefixWord, tailWord_207767, baseEnd_207767] using wordTrace_append hprefix tailTrace_207767
  have hstable : (prefixWord ++ tailWord_207767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207767).length < 2 ^ (prefixWord ++ tailWord_207767).sum := by decide
  have hdescent : baseEnd_207767 < baseStart_207767 := by decide
  rcases family_descends (prefixWord ++ tailWord_207767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207777 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_207777 : Nat := 118140960795 + 207777 * 2 ^ 59
def prefixEnd_207777 : Nat := 4983230072969 + 3 ^ 40 * 207777 * 2
def baseEnd_207777 : Nat := 94835084399412271317295

theorem tailTrace_207777 : CollatzResearch.WordTrace tailWord_207777 prefixEnd_207777 94835084399412271317295 := by
  unfold tailWord_207777
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578249768266889331565585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5052166512177926221043723 7578249768266889331565585)
  ·
    refine ⟨5683687326200166998674189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7578249768266889331565585 5683687326200166998674189)
    ·
      refine ⟨2131382747325062624502821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5683687326200166998674189 2131382747325062624502821)
      ·
        refine ⟨399634265123449242094279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2131382747325062624502821 399634265123449242094279)
        ·
          refine ⟨599451397685173863141419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399634265123449242094279 599451397685173863141419)
          ·
            refine ⟨899177096527760794712129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599451397685173863141419 899177096527760794712129)
            ·
              refine ⟨674382822395820596034097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899177096527760794712129 674382822395820596034097)
              ·
                refine ⟨505787116796865447025573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674382822395820596034097 505787116796865447025573)
                ·
                  refine ⟨94835084399412271317295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505787116796865447025573 94835084399412271317295)
                  ·
                    rfl

theorem cell20_207777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_207777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207777 prefixEnd_207777 := by exact prefixLift 207777
  have htrace : WordTrace (prefixWord ++ tailWord_207777) baseStart_207777 baseEnd_207777 := by
    simpa [prefixWord, tailWord_207777, baseEnd_207777] using wordTrace_append hprefix tailTrace_207777
  have hstable : (prefixWord ++ tailWord_207777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207777).length < 2 ^ (prefixWord ++ tailWord_207777).sum := by decide
  have hdescent : baseEnd_207777 < baseStart_207777 := by decide
  rcases family_descends (prefixWord ++ tailWord_207777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207814 : List Nat := [6, 1, 3, 1, 1, 1, 2, 5]
def baseStart_207814 : Nat := 118140960795 + 207814 * 2 ^ 59
def prefixEnd_207814 : Nat := 4983230072969 + 3 ^ 40 * 207814 * 2
def baseEnd_207814 : Nat := 31617324069201529027937

theorem tailTrace_207814 : CollatzResearch.WordTrace tailWord_207814 prefixEnd_207814 31617324069201529027937 := by
  unfold tailWord_207814
  simp only [CollatzResearch.WordTrace]
  refine ⟨236862477160401395333203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5053066179421896433774997 236862477160401395333203)
  ·
    refine ⟨355293715740602092999805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236862477160401395333203 355293715740602092999805)
    ·
      refine ⟨133235143402725784874927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355293715740602092999805 133235143402725784874927)
      ·
        refine ⟨199852715104088677312391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133235143402725784874927 199852715104088677312391)
        ·
          refine ⟨299779072656133015968587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199852715104088677312391 299779072656133015968587)
          ·
            refine ⟨449668608984199523952881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299779072656133015968587 449668608984199523952881)
            ·
              refine ⟨337251456738149642964661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449668608984199523952881 337251456738149642964661)
              ·
                refine ⟨31617324069201529027937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337251456738149642964661 31617324069201529027937)
                ·
                  rfl

theorem cell20_207814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_207814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207814 prefixEnd_207814 := by exact prefixLift 207814
  have htrace : WordTrace (prefixWord ++ tailWord_207814) baseStart_207814 baseEnd_207814 := by
    simpa [prefixWord, tailWord_207814, baseEnd_207814] using wordTrace_append hprefix tailTrace_207814
  have hstable : (prefixWord ++ tailWord_207814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207814).length < 2 ^ (prefixWord ++ tailWord_207814).sum := by decide
  have hdescent : baseEnd_207814 < baseStart_207814 := by decide
  rcases family_descends (prefixWord ++ tailWord_207814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207815 : List Nat := [1, 1, 4, 1, 1, 2, 2, 6, 2]
def baseStart_207815 : Nat := 118140960795 + 207815 * 2 ^ 59
def prefixEnd_207815 : Nat := 4983230072969 + 3 ^ 40 * 207815 * 2
def baseEnd_207815 : Nat := 94852428634853028050473

theorem tailTrace_207815 : CollatzResearch.WordTrace tailWord_207815 prefixEnd_207815 94852428634853028050473 := by
  unfold tailWord_207815
  simp only [CollatzResearch.WordTrace]
  refine ⟨7579635742129221821448899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5053090494752814547632599 7579635742129221821448899)
  ·
    refine ⟨11369453613193832732173349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7579635742129221821448899 11369453613193832732173349)
    ·
      refine ⟨2131772552473843637282503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11369453613193832732173349 2131772552473843637282503)
      ·
        refine ⟨3197658828710765455923755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131772552473843637282503 3197658828710765455923755)
        ·
          refine ⟨4796488243066148183885633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197658828710765455923755 4796488243066148183885633)
          ·
            refine ⟨3597366182299611137914225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4796488243066148183885633 3597366182299611137914225)
            ·
              refine ⟨2698024636724708353435669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597366182299611137914225 2698024636724708353435669)
              ·
                refine ⟨126469904846470704067297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2698024636724708353435669 126469904846470704067297)
                ·
                  refine ⟨94852428634853028050473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126469904846470704067297 94852428634853028050473)
                  ·
                    rfl

theorem cell20_207815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 2].length) (baseStart_207815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207815 prefixEnd_207815 := by exact prefixLift 207815
  have htrace : WordTrace (prefixWord ++ tailWord_207815) baseStart_207815 baseEnd_207815 := by
    simpa [prefixWord, tailWord_207815, baseEnd_207815] using wordTrace_append hprefix tailTrace_207815
  have hstable : (prefixWord ++ tailWord_207815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207815).length < 2 ^ (prefixWord ++ tailWord_207815).sum := by decide
  have hdescent : baseEnd_207815 < baseStart_207815 := by decide
  rcases family_descends (prefixWord ++ tailWord_207815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207821 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 3]
def baseStart_207821 : Nat := 118140960795 + 207821 * 2 ^ 59
def prefixEnd_207821 : Nat := 4983230072969 + 3 ^ 40 * 207821 * 2
def baseEnd_207821 : Nat := 94855167198343673850449

theorem tailTrace_207821 : CollatzResearch.WordTrace tailWord_207821 prefixEnd_207821 94855167198343673850449 := by
  unfold tailWord_207821
  simp only [CollatzResearch.WordTrace]
  refine ⟨7579854580107484846167317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5053236386738323230778211 7579854580107484846167317)
  ·
    refine ⟨355305683442538352164093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7579854580107484846167317 355305683442538352164093)
    ·
      refine ⟨133239631290951882061535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355305683442538352164093 133239631290951882061535)
      ·
        refine ⟨199859446936427823092303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133239631290951882061535 199859446936427823092303)
        ·
          refine ⟨299789170404641734638455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199859446936427823092303 299789170404641734638455)
          ·
            refine ⟨449683755606962601957683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299789170404641734638455 449683755606962601957683)
            ·
              refine ⟨674525633410443902936525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449683755606962601957683 674525633410443902936525)
              ·
                refine ⟨252947112528916463601197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674525633410443902936525 252947112528916463601197)
                ·
                  refine ⟨94855167198343673850449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252947112528916463601197 94855167198343673850449)
                  ·
                    rfl

theorem cell20_207821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_207821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207821 prefixEnd_207821 := by exact prefixLift 207821
  have htrace : WordTrace (prefixWord ++ tailWord_207821) baseStart_207821 baseEnd_207821 := by
    simpa [prefixWord, tailWord_207821, baseEnd_207821] using wordTrace_append hprefix tailTrace_207821
  have hstable : (prefixWord ++ tailWord_207821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207821).length < 2 ^ (prefixWord ++ tailWord_207821).sum := by decide
  have hdescent : baseEnd_207821 < baseStart_207821 := by decide
  rcases family_descends (prefixWord ++ tailWord_207821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207822 : List Nat := [4, 1, 1, 1, 2, 4, 2, 5]
def baseStart_207822 : Nat := 118140960795 + 207822 * 2 ^ 59
def prefixEnd_207822 : Nat := 4983230072969 + 3 ^ 40 * 207822 * 2
def baseEnd_207822 : Nat := 31618541208530704939037

theorem tailTrace_207822 : CollatzResearch.WordTrace tailWord_207822 prefixEnd_207822 31618541208530704939037 := by
  unfold tailWord_207822
  simp only [CollatzResearch.WordTrace]
  refine ⟨947486381637982752119215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5053260702069241344635813 947486381637982752119215)
  ·
    refine ⟨1421229572456974128178823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947486381637982752119215 1421229572456974128178823)
    ·
      refine ⟨2131844358685461192268235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1421229572456974128178823 2131844358685461192268235)
      ·
        refine ⟨3197766538028191788402353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131844358685461192268235 3197766538028191788402353)
        ·
          refine ⟨2398324903521143841301765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3197766538028191788402353 2398324903521143841301765)
          ·
            refine ⟨449685919410214470244081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2398324903521143841301765 449685919410214470244081)
            ·
              refine ⟨337264439557660852683061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449685919410214470244081 337264439557660852683061)
              ·
                refine ⟨31618541208530704939037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337264439557660852683061 31618541208530704939037)
                ·
                  rfl

theorem cell20_207822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_207822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207822 prefixEnd_207822 := by exact prefixLift 207822
  have htrace : WordTrace (prefixWord ++ tailWord_207822) baseStart_207822 baseEnd_207822 := by
    simpa [prefixWord, tailWord_207822, baseEnd_207822] using wordTrace_append hprefix tailTrace_207822
  have hstable : (prefixWord ++ tailWord_207822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207822).length < 2 ^ (prefixWord ++ tailWord_207822).sum := by decide
  have hdescent : baseEnd_207822 < baseStart_207822 := by decide
  rcases family_descends (prefixWord ++ tailWord_207822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207843 : List Nat := [1, 1, 1, 6, 1, 1, 1, 8]
def baseStart_207843 : Nat := 118140960795 + 207843 * 2 ^ 59
def prefixEnd_207843 : Nat := 4983230072969 + 3 ^ 40 * 207843 * 2
def baseEnd_207843 : Nat := 31621736199269791705675

theorem tailTrace_207843 : CollatzResearch.WordTrace tailWord_207843 prefixEnd_207843 31621736199269791705675 := by
  unfold tailWord_207843
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580656986027782603468183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5053771324018521735645455 7580656986027782603468183)
  ·
    refine ⟨11370985479041673905202275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7580656986027782603468183 11370985479041673905202275)
    ·
      refine ⟨17056478218562510857803413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11370985479041673905202275 17056478218562510857803413)
      ·
        refine ⟨799522416495117696459535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17056478218562510857803413 799522416495117696459535)
        ·
          refine ⟨1199283624742676544689303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799522416495117696459535 1199283624742676544689303)
          ·
            refine ⟨1798925437114014817033955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199283624742676544689303 1798925437114014817033955)
            ·
              refine ⟨2698388155671022225550933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798925437114014817033955 2698388155671022225550933)
              ·
                refine ⟨31621736199269791705675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2698388155671022225550933 31621736199269791705675)
                ·
                  rfl

theorem cell20_207843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_207843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207843 prefixEnd_207843 := by exact prefixLift 207843
  have htrace : WordTrace (prefixWord ++ tailWord_207843) baseStart_207843 baseEnd_207843 := by
    simpa [prefixWord, tailWord_207843, baseEnd_207843] using wordTrace_append hprefix tailTrace_207843
  have hstable : (prefixWord ++ tailWord_207843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207843).length < 2 ^ (prefixWord ++ tailWord_207843).sum := by decide
  have hdescent : baseEnd_207843 < baseStart_207843 := by decide
  rcases family_descends (prefixWord ++ tailWord_207843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207898 : List Nat := [3, 1, 1, 3, 1, 2, 5, 4]
def baseStart_207898 : Nat := 118140960795 + 207898 * 2 ^ 59
def prefixEnd_207898 : Nat := 4983230072969 + 3 ^ 40 * 207898 * 2
def baseEnd_207898 : Nat := 31630104032157876094489

theorem tailTrace_207898 : CollatzResearch.WordTrace tailWord_207898 prefixEnd_207898 31630104032157876094489 := by
  unfold tailWord_207898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895665750207131749180087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5055108667219017997813565 1895665750207131749180087)
  ·
    refine ⟨2843498625310697623770131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1895665750207131749180087 2843498625310697623770131)
    ·
      refine ⟨4265247937966046435655197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843498625310697623770131 4265247937966046435655197)
      ·
        refine ⟨1599467976737267413370699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4265247937966046435655197 1599467976737267413370699)
        ·
          refine ⟨2399201965105901120056049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599467976737267413370699 2399201965105901120056049)
          ·
            refine ⟨1799401473829425840042037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399201965105901120056049 1799401473829425840042037)
            ·
              refine ⟨168693888171508672503941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1799401473829425840042037 168693888171508672503941)
              ·
                refine ⟨31630104032157876094489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168693888171508672503941 31630104032157876094489)
                ·
                  rfl

theorem cell20_207898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_207898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207898 prefixEnd_207898 := by exact prefixLift 207898
  have htrace : WordTrace (prefixWord ++ tailWord_207898) baseStart_207898 baseEnd_207898 := by
    simpa [prefixWord, tailWord_207898, baseEnd_207898] using wordTrace_append hprefix tailTrace_207898
  have hstable : (prefixWord ++ tailWord_207898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207898).length < 2 ^ (prefixWord ++ tailWord_207898).sum := by decide
  have hdescent : baseEnd_207898 < baseStart_207898 := by decide
  rcases family_descends (prefixWord ++ tailWord_207898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207908 : List Nat := [2, 3, 1, 4, 1, 1, 1, 5, 2]
def baseStart_207908 : Nat := 118140960795 + 207908 * 2 ^ 59
def prefixEnd_207908 : Nat := 4983230072969 + 3 ^ 40 * 207908 * 2
def baseEnd_207908 : Nat := 94894876368958037950093

theorem tailTrace_207908 : CollatzResearch.WordTrace tailWord_207908 prefixEnd_207908 94894876368958037950093 := by
  unfold tailWord_207908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791513865396149352292189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5055351820528199136389585 3791513865396149352292189)
  ·
    refine ⟨1421817699523556007109571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3791513865396149352292189 1421817699523556007109571)
    ·
      refine ⟨2132726549285334010664357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1421817699523556007109571 2132726549285334010664357)
      ·
        refine ⟨399886227991000126999567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2132726549285334010664357 399886227991000126999567)
        ·
          refine ⟨599829341986500190499351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399886227991000126999567 599829341986500190499351)
          ·
            refine ⟨899744012979750285749027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599829341986500190499351 899744012979750285749027)
            ·
              refine ⟨1349616019469625428623541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899744012979750285749027 1349616019469625428623541)
              ·
                refine ⟨126526501825277383933457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1349616019469625428623541 126526501825277383933457)
                ·
                  refine ⟨94894876368958037950093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126526501825277383933457 94894876368958037950093)
                  ·
                    rfl

theorem cell20_207908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_207908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207908 prefixEnd_207908 := by exact prefixLift 207908
  have htrace : WordTrace (prefixWord ++ tailWord_207908) baseStart_207908 baseEnd_207908 := by
    simpa [prefixWord, tailWord_207908, baseEnd_207908] using wordTrace_append hprefix tailTrace_207908
  have hstable : (prefixWord ++ tailWord_207908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207908).length < 2 ^ (prefixWord ++ tailWord_207908).sum := by decide
  have hdescent : baseEnd_207908 < baseStart_207908 := by decide
  rcases family_descends (prefixWord ++ tailWord_207908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207929 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_207929 : Nat := 118140960795 + 207929 * 2 ^ 59
def prefixEnd_207929 : Nat := 4983230072969 + 3 ^ 40 * 207929 * 2
def baseEnd_207929 : Nat := 94904461341175298250007

theorem tailTrace_207929 : CollatzResearch.WordTrace tailWord_207929 prefixEnd_207929 94904461341175298250007 := by
  unfold tailWord_207929
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583793663716219291098841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5055862442477479527399227 7583793663716219291098841)
  ·
    refine ⟨5687845247787164468324131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7583793663716219291098841 5687845247787164468324131)
    ·
      refine ⟨8531767871680746702486197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687845247787164468324131 8531767871680746702486197)
      ·
        refine ⟨799853237970070003358081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8531767871680746702486197 799853237970070003358081)
        ·
          refine ⟨599889928477552502518561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799853237970070003358081 599889928477552502518561)
          ·
            refine ⟨449917446358164376888921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599889928477552502518561 449917446358164376888921)
            ·
              refine ⟨337438084768623282666691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449917446358164376888921 337438084768623282666691)
              ·
                refine ⟨506157127152934924000037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337438084768623282666691 506157127152934924000037)
                ·
                  refine ⟨94904461341175298250007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506157127152934924000037 94904461341175298250007)
                  ·
                    rfl

theorem cell20_207929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_207929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207929 prefixEnd_207929 := by exact prefixLift 207929
  have htrace : WordTrace (prefixWord ++ tailWord_207929) baseStart_207929 baseEnd_207929 := by
    simpa [prefixWord, tailWord_207929, baseEnd_207929] using wordTrace_append hprefix tailTrace_207929
  have hstable : (prefixWord ++ tailWord_207929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207929).length < 2 ^ (prefixWord ++ tailWord_207929).sum := by decide
  have hdescent : baseEnd_207929 < baseStart_207929 := by decide
  rcases family_descends (prefixWord ++ tailWord_207929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207950 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_207950 : Nat := 118140960795 + 207950 * 2 ^ 59
def prefixEnd_207950 : Nat := 4983230072969 + 3 ^ 40 * 207950 * 2
def baseEnd_207950 : Nat := 94914046313392558549921

theorem tailTrace_207950 : CollatzResearch.WordTrace tailWord_207950 prefixEnd_207950 94914046313392558549921 := by
  unfold tailWord_207950
  simp only [CollatzResearch.WordTrace]
  refine ⟨948069949580017484701663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5056373064426759918408869 948069949580017484701663)
  ·
    refine ⟨1422104924370026227052495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948069949580017484701663 1422104924370026227052495)
    ·
      refine ⟨2133157386555039340578743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422104924370026227052495 2133157386555039340578743)
      ·
        refine ⟨3199736079832559010868115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133157386555039340578743 3199736079832559010868115)
        ·
          refine ⟨4799604119748838516302173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199736079832559010868115 4799604119748838516302173)
          ·
            refine ⟨1799851544905814443613315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4799604119748838516302173 1799851544905814443613315)
            ·
              refine ⟨2699777317358721665419973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799851544905814443613315 2699777317358721665419973)
              ·
                refine ⟨506208247004760312266245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2699777317358721665419973 506208247004760312266245)
                ·
                  refine ⟨94914046313392558549921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506208247004760312266245 94914046313392558549921)
                  ·
                    rfl

theorem cell20_207950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_207950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207950 prefixEnd_207950 := by exact prefixLift 207950
  have htrace : WordTrace (prefixWord ++ tailWord_207950) baseStart_207950 baseEnd_207950 := by
    simpa [prefixWord, tailWord_207950, baseEnd_207950] using wordTrace_append hprefix tailTrace_207950
  have hstable : (prefixWord ++ tailWord_207950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207950).length < 2 ^ (prefixWord ++ tailWord_207950).sum := by decide
  have hdescent : baseEnd_207950 < baseStart_207950 := by decide
  rcases family_descends (prefixWord ++ tailWord_207950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207957 : List Nat := [1, 3, 2, 2, 1, 2, 3, 6]
def baseStart_207957 : Nat := 118140960795 + 207957 * 2 ^ 59
def prefixEnd_207957 : Nat := 4983230072969 + 3 ^ 40 * 207957 * 2
def baseEnd_207957 : Nat := 31639080434710548438853

theorem tailTrace_207957 : CollatzResearch.WordTrace tailWord_207957 prefixEnd_207957 31639080434710548438853 := by
  unfold tailWord_207957
  simp only [CollatzResearch.WordTrace]
  refine ⟨7584814907614780073118125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5056543271743186715412083 7584814907614780073118125)
  ·
    refine ⟨2844305590355542527419297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7584814907614780073118125 2844305590355542527419297)
    ·
      refine ⟨2133229192766656895564473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2844305590355542527419297 2133229192766656895564473)
      ·
        refine ⟨1599921894574992671673355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2133229192766656895564473 1599921894574992671673355)
        ·
          refine ⟨2399882841862489007510033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599921894574992671673355 2399882841862489007510033)
          ·
            refine ⟨1799912131396866755632525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399882841862489007510033 1799912131396866755632525)
            ·
              refine ⟨674967049273825033362197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1799912131396866755632525 674967049273825033362197)
              ·
                refine ⟨31639080434710548438853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 674967049273825033362197 31639080434710548438853)
                ·
                  rfl

theorem cell20_207957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_207957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207957 prefixEnd_207957 := by exact prefixLift 207957
  have htrace : WordTrace (prefixWord ++ tailWord_207957) baseStart_207957 baseEnd_207957 := by
    simpa [prefixWord, tailWord_207957, baseEnd_207957] using wordTrace_append hprefix tailTrace_207957
  have hstable : (prefixWord ++ tailWord_207957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207957).length < 2 ^ (prefixWord ++ tailWord_207957).sum := by decide
  have hdescent : baseEnd_207957 < baseStart_207957 := by decide
  rcases family_descends (prefixWord ++ tailWord_207957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207981 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_207981 : Nat := 118140960795 + 207981 * 2 ^ 59
def prefixEnd_207981 : Nat := 4983230072969 + 3 ^ 40 * 207981 * 2
def baseEnd_207981 : Nat := 94928195558094228516461

theorem tailTrace_207981 : CollatzResearch.WordTrace tailWord_207981 prefixEnd_207981 94928195558094228516461 := by
  unfold tailWord_207981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585690259527832171991797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5057126839685221447994531 7585690259527832171991797)
  ·
    refine ⟨711158461830734266124231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7585690259527832171991797 711158461830734266124231)
    ·
      refine ⟨1066737692746101399186347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 711158461830734266124231 1066737692746101399186347)
      ·
        refine ⟨1600106539119152098779521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066737692746101399186347 1600106539119152098779521)
        ·
          refine ⟨1200079904339364074084641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1600106539119152098779521 1200079904339364074084641)
          ·
            refine ⟨900059928254523055563481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200079904339364074084641 900059928254523055563481)
            ·
              refine ⟨675044946190892291672611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900059928254523055563481 675044946190892291672611)
              ·
                refine ⟨1012567419286338437508917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675044946190892291672611 1012567419286338437508917)
                ·
                  refine ⟨94928195558094228516461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012567419286338437508917 94928195558094228516461)
                  ·
                    rfl

theorem cell20_207981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_207981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207981 prefixEnd_207981 := by exact prefixLift 207981
  have htrace : WordTrace (prefixWord ++ tailWord_207981) baseStart_207981 baseEnd_207981 := by
    simpa [prefixWord, tailWord_207981, baseEnd_207981] using wordTrace_append hprefix tailTrace_207981
  have hstable : (prefixWord ++ tailWord_207981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207981).length < 2 ^ (prefixWord ++ tailWord_207981).sum := by decide
  have hdescent : baseEnd_207981 < baseStart_207981 := by decide
  rcases family_descends (prefixWord ++ tailWord_207981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207984 : List Nat := [2, 1, 1, 1, 5, 1, 5, 2, 2]
def baseStart_207984 : Nat := 118140960795 + 207984 * 2 ^ 59
def prefixEnd_207984 : Nat := 4983230072969 + 3 ^ 40 * 207984 * 2
def baseEnd_207984 : Nat := 94929564839839551416449

theorem tailTrace_207984 : CollatzResearch.WordTrace tailWord_207984 prefixEnd_207984 94929564839839551416449 := by
  unfold tailWord_207984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792899839258481842175503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5057199785677975789567337 3792899839258481842175503)
  ·
    refine ⟨5689349758887722763263255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3792899839258481842175503 5689349758887722763263255)
    ·
      refine ⟨8534024638331584144894883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689349758887722763263255 8534024638331584144894883)
      ·
        refine ⟨12801036957497376217342325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8534024638331584144894883 12801036957497376217342325)
        ·
          refine ⟨1200097214765379020375843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12801036957497376217342325 1200097214765379020375843)
          ·
            refine ⟨1800145822148068530563765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200097214765379020375843 1800145822148068530563765)
            ·
              refine ⟨168763670826381424740353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1800145822148068530563765 168763670826381424740353)
              ·
                refine ⟨126572753119786068555265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168763670826381424740353 126572753119786068555265)
                ·
                  refine ⟨94929564839839551416449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126572753119786068555265 94929564839839551416449)
                  ·
                    rfl

theorem cell20_207984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_207984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_207984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_207984 prefixEnd_207984 := by exact prefixLift 207984
  have htrace : WordTrace (prefixWord ++ tailWord_207984) baseStart_207984 baseEnd_207984 := by
    simpa [prefixWord, tailWord_207984, baseEnd_207984] using wordTrace_append hprefix tailTrace_207984
  have hstable : (prefixWord ++ tailWord_207984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207984).length < 2 ^ (prefixWord ++ tailWord_207984).sum := by decide
  have hdescent : baseEnd_207984 < baseStart_207984 := by decide
  rcases family_descends (prefixWord ++ tailWord_207984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208036 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_208036 : Nat := 118140960795 + 208036 * 2 ^ 59
def prefixEnd_208036 : Nat := 4983230072969 + 3 ^ 40 * 208036 * 2
def baseEnd_208036 : Nat := 94953299056758481682903

theorem tailTrace_208036 : CollatzResearch.WordTrace tailWord_208036 prefixEnd_208036 94953299056758481682903 := by
  unfold tailWord_208036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3793848137164288282621981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5058464182885717710162641 3793848137164288282621981)
  ·
    refine ⟨1422693051436608105983243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3793848137164288282621981 1422693051436608105983243)
    ·
      refine ⟨2134039577154912158974865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422693051436608105983243 2134039577154912158974865)
      ·
        refine ⟨1600529682866184119231149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2134039577154912158974865 1600529682866184119231149)
        ·
          refine ⟨600198631074819044711681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1600529682866184119231149 600198631074819044711681)
          ·
            refine ⟨450148973306114283533761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600198631074819044711681 450148973306114283533761)
            ·
              refine ⟨337611729979585712650321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450148973306114283533761 337611729979585712650321)
              ·
                refine ⟨253208797484689284487741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337611729979585712650321 253208797484689284487741)
                ·
                  refine ⟨94953299056758481682903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253208797484689284487741 94953299056758481682903)
                  ·
                    rfl

theorem cell20_208036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_208036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208036 prefixEnd_208036 := by exact prefixLift 208036
  have htrace : WordTrace (prefixWord ++ tailWord_208036) baseStart_208036 baseEnd_208036 := by
    simpa [prefixWord, tailWord_208036, baseEnd_208036] using wordTrace_append hprefix tailTrace_208036
  have hstable : (prefixWord ++ tailWord_208036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208036).length < 2 ^ (prefixWord ++ tailWord_208036).sum := by decide
  have hdescent : baseEnd_208036 < baseStart_208036 := by decide
  rcases family_descends (prefixWord ++ tailWord_208036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208039 : List Nat := [1, 1, 6, 2, 1, 1, 4, 2, 2]
def baseStart_208039 : Nat := 118140960795 + 208039 * 2 ^ 59
def prefixEnd_208039 : Nat := 4983230072969 + 3 ^ 40 * 208039 * 2
def baseEnd_208039 : Nat := 94954668338503804582891

theorem tailTrace_208039 : CollatzResearch.WordTrace tailWord_208039 prefixEnd_208039 94954668338503804582891 := by
  unfold tailWord_208039
  simp only [CollatzResearch.WordTrace]
  refine ⟨7587805693317708077603171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5058537128878472051735447 7587805693317708077603171)
  ·
    refine ⟨11381708539976562116404757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7587805693317708077603171 11381708539976562116404757)
    ·
      refine ⟨533517587811401349206473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11381708539976562116404757 533517587811401349206473)
      ·
        refine ⟨400138190858551011904855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533517587811401349206473 400138190858551011904855)
        ·
          refine ⟨600207286287826517857283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400138190858551011904855 600207286287826517857283)
          ·
            refine ⟨900310929431739776785925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600207286287826517857283 900310929431739776785925)
            ·
              refine ⟨168808299268451208147361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 900310929431739776785925 168808299268451208147361)
              ·
                refine ⟨126606224451338406110521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168808299268451208147361 126606224451338406110521)
                ·
                  refine ⟨94954668338503804582891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126606224451338406110521 94954668338503804582891)
                  ·
                    rfl

theorem cell20_208039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 2].length) (baseStart_208039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208039 prefixEnd_208039 := by exact prefixLift 208039
  have htrace : WordTrace (prefixWord ++ tailWord_208039) baseStart_208039 baseEnd_208039 := by
    simpa [prefixWord, tailWord_208039, baseEnd_208039] using wordTrace_append hprefix tailTrace_208039
  have hstable : (prefixWord ++ tailWord_208039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208039).length < 2 ^ (prefixWord ++ tailWord_208039).sum := by decide
  have hdescent : baseEnd_208039 < baseStart_208039 := by decide
  rcases family_descends (prefixWord ++ tailWord_208039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208050 : List Nat := [3, 2, 1, 1, 1, 6, 1, 5]
def baseStart_208050 : Nat := 118140960795 + 208050 * 2 ^ 59
def prefixEnd_208050 : Nat := 4983230072969 + 3 ^ 40 * 208050 * 2
def baseEnd_208050 : Nat := 31653229679412218405393

theorem tailTrace_208050 : CollatzResearch.WordTrace tailWord_208050 prefixEnd_208050 31653229679412218405393 := by
  unfold tailWord_208050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897051724069464239063401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5058804597518571304169069 1897051724069464239063401)
  ·
    refine ⟨1422788793052098179297551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1897051724069464239063401 1422788793052098179297551)
    ·
      refine ⟨2134183189578147268946327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422788793052098179297551 2134183189578147268946327)
      ·
        refine ⟨3201274784367220903419491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134183189578147268946327 3201274784367220903419491)
        ·
          refine ⟨4801912176550831355129237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201274784367220903419491 4801912176550831355129237)
          ·
            refine ⟨225089633275820219771683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4801912176550831355129237 225089633275820219771683)
            ·
              refine ⟨337634449913730329657525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225089633275820219771683 337634449913730329657525)
              ·
                refine ⟨31653229679412218405393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337634449913730329657525 31653229679412218405393)
                ·
                  rfl

theorem cell20_208050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_208050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208050 prefixEnd_208050 := by exact prefixLift 208050
  have htrace : WordTrace (prefixWord ++ tailWord_208050) baseStart_208050 baseEnd_208050 := by
    simpa [prefixWord, tailWord_208050, baseEnd_208050] using wordTrace_append hprefix tailTrace_208050
  have hstable : (prefixWord ++ tailWord_208050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208050).length < 2 ^ (prefixWord ++ tailWord_208050).sum := by decide
  have hdescent : baseEnd_208050 < baseStart_208050 := by decide
  rcases family_descends (prefixWord ++ tailWord_208050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208057 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 3]
def baseStart_208057 : Nat := 118140960795 + 208057 * 2 ^ 59
def prefixEnd_208057 : Nat := 4983230072969 + 3 ^ 40 * 208057 * 2
def baseEnd_208057 : Nat := 94962884028975741982817

theorem tailTrace_208057 : CollatzResearch.WordTrace tailWord_208057 prefixEnd_208057 94962884028975741982817 := by
  unfold tailWord_208057
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588462207252497151758425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5058974804834998101172283 7588462207252497151758425)
  ·
    refine ⟨5691346655439372863818819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7588462207252497151758425 5691346655439372863818819)
    ·
      refine ⟨8537019983159059295728229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5691346655439372863818819 8537019983159059295728229)
      ·
        refine ⟨1600691246842323617949043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8537019983159059295728229 1600691246842323617949043)
        ·
          refine ⟨2401036870263485426923565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600691246842323617949043 2401036870263485426923565)
          ·
            refine ⟨900388826348807035096337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2401036870263485426923565 900388826348807035096337)
            ·
              refine ⟨675291619761605276322253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900388826348807035096337 675291619761605276322253)
              ·
                refine ⟨253234357410601978620845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675291619761605276322253 253234357410601978620845)
                ·
                  refine ⟨94962884028975741982817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253234357410601978620845 94962884028975741982817)
                  ·
                    rfl

theorem cell20_208057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_208057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208057 prefixEnd_208057 := by exact prefixLift 208057
  have htrace : WordTrace (prefixWord ++ tailWord_208057) baseStart_208057 baseEnd_208057 := by
    simpa [prefixWord, tailWord_208057, baseEnd_208057] using wordTrace_append hprefix tailTrace_208057
  have hstable : (prefixWord ++ tailWord_208057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208057).length < 2 ^ (prefixWord ++ tailWord_208057).sum := by decide
  have hdescent : baseEnd_208057 < baseStart_208057 := by decide
  rcases family_descends (prefixWord ++ tailWord_208057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208095 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 3]
def baseStart_208095 : Nat := 118140960795 + 208095 * 2 ^ 59
def prefixEnd_208095 : Nat := 4983230072969 + 3 ^ 40 * 208095 * 2
def baseEnd_208095 : Nat := 94980228264416498715995

theorem tailTrace_208095 : CollatzResearch.WordTrace tailWord_208095 prefixEnd_208095 94980228264416498715995 := by
  unfold tailWord_208095
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589848181114829641641739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5059898787409886427761159 7589848181114829641641739)
  ·
    refine ⟨11384772271672244462462609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7589848181114829641641739 11384772271672244462462609)
    ·
      refine ⟨8538579203754183346846957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11384772271672244462462609 8538579203754183346846957)
      ·
        refine ⟨3201967201407818755067609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8538579203754183346846957 3201967201407818755067609)
        ·
          refine ⟨2401475401055864066300707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201967201407818755067609 2401475401055864066300707)
          ·
            refine ⟨3602213101583796099451061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401475401055864066300707 3602213101583796099451061)
            ·
              refine ⟨337707478273480884323537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3602213101583796099451061 337707478273480884323537)
              ·
                refine ⟨253280608705110663242653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337707478273480884323537 253280608705110663242653)
                ·
                  refine ⟨94980228264416498715995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253280608705110663242653 94980228264416498715995)
                  ·
                    rfl

theorem cell20_208095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_208095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208095 prefixEnd_208095 := by exact prefixLift 208095
  have htrace : WordTrace (prefixWord ++ tailWord_208095) baseStart_208095 baseEnd_208095 := by
    simpa [prefixWord, tailWord_208095, baseEnd_208095] using wordTrace_append hprefix tailTrace_208095
  have hstable : (prefixWord ++ tailWord_208095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208095).length < 2 ^ (prefixWord ++ tailWord_208095).sum := by decide
  have hdescent : baseEnd_208095 < baseStart_208095 := by decide
  rcases family_descends (prefixWord ++ tailWord_208095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208126 : List Nat := [4, 2, 2, 1, 1, 3, 1, 6]
def baseStart_208126 : Nat := 118140960795 + 208126 * 2 ^ 59
def prefixEnd_208126 : Nat := 4983230072969 + 3 ^ 40 * 208126 * 2
def baseEnd_208126 : Nat := 31664792503039389560845

theorem tailTrace_208126 : CollatzResearch.WordTrace tailWord_208126 prefixEnd_208126 31664792503039389560845 := by
  unfold tailWord_208126
  simp only [CollatzResearch.WordTrace]
  refine ⟨948872355500315242002529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5060652562668347957346821 948872355500315242002529)
  ·
    refine ⟨711654266625236431501897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 948872355500315242002529 711654266625236431501897)
    ·
      refine ⟨533740699968927323626423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 711654266625236431501897 533740699968927323626423)
      ·
        refine ⟨800611049953390985439635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533740699968927323626423 800611049953390985439635)
        ·
          refine ⟨1200916574930086478159453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800611049953390985439635 1200916574930086478159453)
          ·
            refine ⟨450343715598782429309795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1200916574930086478159453 450343715598782429309795)
            ·
              refine ⟨675515573398173643964693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450343715598782429309795 675515573398173643964693)
              ·
                refine ⟨31664792503039389560845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 675515573398173643964693 31664792503039389560845)
                ·
                  rfl

theorem cell20_208126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_208126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208126 prefixEnd_208126 := by exact prefixLift 208126
  have htrace : WordTrace (prefixWord ++ tailWord_208126) baseStart_208126 baseEnd_208126 := by
    simpa [prefixWord, tailWord_208126, baseEnd_208126] using wordTrace_append hprefix tailTrace_208126
  have hstable : (prefixWord ++ tailWord_208126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208126).length < 2 ^ (prefixWord ++ tailWord_208126).sum := by decide
  have hdescent : baseEnd_208126 < baseStart_208126 := by decide
  rcases family_descends (prefixWord ++ tailWord_208126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208157 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_208157 : Nat := 118140960795 + 208157 * 2 ^ 59
def prefixEnd_208157 : Nat := 4983230072969 + 3 ^ 40 * 208157 * 2
def baseEnd_208157 : Nat := 95008526753819838649075

theorem tailTrace_208157 : CollatzResearch.WordTrace tailWord_208157 prefixEnd_208157 95008526753819838649075 := by
  unfold tailWord_208157
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592109506890214230398725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5061406337926809486932483 7592109506890214230398725)
  ·
    refine ⟨1423520532541915168199761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7592109506890214230398725 1423520532541915168199761)
    ·
      refine ⟨1067640399406436376149821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1423520532541915168199761 1067640399406436376149821)
      ·
        refine ⟨400365149777413641056183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1067640399406436376149821 400365149777413641056183)
        ·
          refine ⟨600547724666120461584275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400365149777413641056183 600547724666120461584275)
          ·
            refine ⟨900821586999180692376413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600547724666120461584275 900821586999180692376413)
            ·
              refine ⟨337808095124692759641155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 900821586999180692376413 337808095124692759641155)
              ·
                refine ⟨506712142687039139461733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337808095124692759641155 506712142687039139461733)
                ·
                  refine ⟨95008526753819838649075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506712142687039139461733 95008526753819838649075)
                  ·
                    rfl

theorem cell20_208157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_208157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208157 prefixEnd_208157 := by exact prefixLift 208157
  have htrace : WordTrace (prefixWord ++ tailWord_208157) baseStart_208157 baseEnd_208157 := by
    simpa [prefixWord, tailWord_208157, baseEnd_208157] using wordTrace_append hprefix tailTrace_208157
  have hstable : (prefixWord ++ tailWord_208157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208157).length < 2 ^ (prefixWord ++ tailWord_208157).sum := by decide
  have hdescent : baseEnd_208157 < baseStart_208157 := by decide
  rcases family_descends (prefixWord ++ tailWord_208157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208198 : List Nat := [6, 1, 1, 3, 2, 7]
def baseStart_208198 : Nat := 118140960795 + 208198 * 2 ^ 59
def prefixEnd_208198 : Nat := 4983230072969 + 3 ^ 40 * 208198 * 2
def baseEnd_208198 : Nat := 3519527417444663640083

theorem tailTrace_208198 : CollatzResearch.WordTrace tailWord_208198 prefixEnd_208198 3519527417444663640083 := by
  unfold tailWord_208198
  simp only [CollatzResearch.WordTrace]
  refine ⟨237300153116927444770039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5062403266494452155094165 237300153116927444770039)
  ·
    refine ⟨355950229675391167155059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237300153116927444770039 355950229675391167155059)
    ·
      refine ⟨533925344513086750732589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355950229675391167155059 533925344513086750732589)
      ·
        refine ⟨200222004192407531524721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533925344513086750732589 200222004192407531524721)
        ·
          refine ⟨150166503144305648643541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200222004192407531524721 150166503144305648643541)
          ·
            refine ⟨3519527417444663640083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150166503144305648643541 3519527417444663640083)
            ·
              rfl

theorem cell20_208198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 7].length) (baseStart_208198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208198 prefixEnd_208198 := by exact prefixLift 208198
  have htrace : WordTrace (prefixWord ++ tailWord_208198) baseStart_208198 baseEnd_208198 := by
    simpa [prefixWord, tailWord_208198, baseEnd_208198] using wordTrace_append hprefix tailTrace_208198
  have hstable : (prefixWord ++ tailWord_208198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208198).length < 2 ^ (prefixWord ++ tailWord_208198).sum := by decide
  have hdescent : baseEnd_208198 < baseStart_208198 := by decide
  rcases family_descends (prefixWord ++ tailWord_208198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208209 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 3]
def baseStart_208209 : Nat := 118140960795 + 208209 * 2 ^ 59
def prefixEnd_208209 : Nat := 4983230072969 + 3 ^ 40 * 208209 * 2
def baseEnd_208209 : Nat := 95032260970738768915529

theorem tailTrace_208209 : CollatzResearch.WordTrace tailWord_208209 prefixEnd_208209 95032260970738768915529 := by
  unfold tailWord_208209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7594006102701827111291681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5062670735134551407527787 7594006102701827111291681)
  ·
    refine ⟨5695504577026370333468761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7594006102701827111291681 5695504577026370333468761)
    ·
      refine ⟨4271628432769777750101571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5695504577026370333468761 4271628432769777750101571)
      ·
        refine ⟨6407442649154666625152357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271628432769777750101571 6407442649154666625152357)
        ·
          refine ⟨1201395496716499992216067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6407442649154666625152357 1201395496716499992216067)
          ·
            refine ⟨1802093245074749988324101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201395496716499992216067 1802093245074749988324101)
            ·
              refine ⟨337892483451515622810769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1802093245074749988324101 337892483451515622810769)
              ·
                refine ⟨253419362588636717108077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337892483451515622810769 253419362588636717108077)
                ·
                  refine ⟨95032260970738768915529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253419362588636717108077 95032260970738768915529)
                  ·
                    rfl

theorem cell20_208209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_208209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208209 prefixEnd_208209 := by exact prefixLift 208209
  have htrace : WordTrace (prefixWord ++ tailWord_208209) baseStart_208209 baseEnd_208209 := by
    simpa [prefixWord, tailWord_208209, baseEnd_208209] using wordTrace_append hprefix tailTrace_208209
  have hstable : (prefixWord ++ tailWord_208209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208209).length < 2 ^ (prefixWord ++ tailWord_208209).sum := by decide
  have hdescent : baseEnd_208209 < baseStart_208209 := by decide
  rcases family_descends (prefixWord ++ tailWord_208209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208264 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_208264 : Nat := 118140960795 + 208264 * 2 ^ 59
def prefixEnd_208264 : Nat := 4983230072969 + 3 ^ 40 * 208264 * 2
def baseEnd_208264 : Nat := 95057364469403022081971

theorem tailTrace_208264 : CollatzResearch.WordTrace tailWord_208264 prefixEnd_208264 95057364469403022081971 := by
  unfold tailWord_208264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798006058751285752271923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5064008078335047669695897 3798006058751285752271923)
  ·
    refine ⟨5697009088126928628407885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3798006058751285752271923 5697009088126928628407885)
    ·
      refine ⟨2136378408047598235652957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5697009088126928628407885 2136378408047598235652957)
      ·
        refine ⟨801141903017849338369859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2136378408047598235652957 801141903017849338369859)
        ·
          refine ⟨1201712854526774007554789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801141903017849338369859 1201712854526774007554789)
          ·
            refine ⟨225321160223770126416523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1201712854526774007554789 225321160223770126416523)
            ·
              refine ⟨337981740335655189624785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225321160223770126416523 337981740335655189624785)
              ·
                refine ⟨253486305251741392218589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337981740335655189624785 253486305251741392218589)
                ·
                  refine ⟨95057364469403022081971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253486305251741392218589 95057364469403022081971)
                  ·
                    rfl

theorem cell20_208264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_208264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208264 prefixEnd_208264 := by exact prefixLift 208264
  have htrace : WordTrace (prefixWord ++ tailWord_208264) baseStart_208264 baseEnd_208264 := by
    simpa [prefixWord, tailWord_208264, baseEnd_208264] using wordTrace_append hprefix tailTrace_208264
  have hstable : (prefixWord ++ tailWord_208264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208264).length < 2 ^ (prefixWord ++ tailWord_208264).sum := by decide
  have hdescent : baseEnd_208264 < baseStart_208264 := by decide
  rcases family_descends (prefixWord ++ tailWord_208264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208268 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_208268 : Nat := 118140960795 + 208268 * 2 ^ 59
def prefixEnd_208268 : Nat := 4983230072969 + 3 ^ 40 * 208268 * 2
def baseEnd_208268 : Nat := 95059190178396785948621

theorem tailTrace_208268 : CollatzResearch.WordTrace tailWord_208268 prefixEnd_208268 95059190178396785948621 := by
  unfold tailWord_208268
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798079004744040093844729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5064105339658720125126305 3798079004744040093844729)
  ·
    refine ⟨2848559253558030070383547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3798079004744040093844729 2848559253558030070383547)
    ·
      refine ⟨4272838880337045105575321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2848559253558030070383547 4272838880337045105575321)
      ·
        refine ⟨3204629160252783829181491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4272838880337045105575321 3204629160252783829181491)
        ·
          refine ⟨4806943740379175743772237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204629160252783829181491 4806943740379175743772237)
          ·
            refine ⟨1802603902642190903914589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4806943740379175743772237 1802603902642190903914589)
            ·
              refine ⟨675976463490821588967971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1802603902642190903914589 675976463490821588967971)
              ·
                refine ⟨1013964695236232383451957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675976463490821588967971 1013964695236232383451957)
                ·
                  refine ⟨95059190178396785948621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1013964695236232383451957 95059190178396785948621)
                  ·
                    rfl

theorem cell20_208268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_208268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208268 prefixEnd_208268 := by exact prefixLift 208268
  have htrace : WordTrace (prefixWord ++ tailWord_208268) baseStart_208268 baseEnd_208268 := by
    simpa [prefixWord, tailWord_208268, baseEnd_208268] using wordTrace_append hprefix tailTrace_208268
  have hstable : (prefixWord ++ tailWord_208268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208268).length < 2 ^ (prefixWord ++ tailWord_208268).sum := by decide
  have hdescent : baseEnd_208268 < baseStart_208268 := by decide
  rcases family_descends (prefixWord ++ tailWord_208268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208316 : List Nat := [2, 2, 2, 4, 2, 2, 6]
def baseStart_208316 : Nat := 118140960795 + 208316 * 2 ^ 59
def prefixEnd_208316 : Nat := 4983230072969 + 3 ^ 40 * 208316 * 2
def baseEnd_208316 : Nat := 10564566520702439149825

theorem tailTrace_208316 : CollatzResearch.WordTrace tailWord_208316 prefixEnd_208316 10564566520702439149825 := by
  unfold tailWord_208316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798954356657092192718401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5065272475542789590291201 3798954356657092192718401)
  ·
    refine ⟨2849215767492819144538801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3798954356657092192718401 2849215767492819144538801)
    ·
      refine ⟨2136911825619614358404101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2849215767492819144538801 2136911825619614358404101)
      ·
        refine ⟨400670967303677692200769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2136911825619614358404101 400670967303677692200769)
        ·
          refine ⟨300503225477758269150577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400670967303677692200769 300503225477758269150577)
          ·
            refine ⟨225377419108318701862933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300503225477758269150577 225377419108318701862933)
            ·
              refine ⟨10564566520702439149825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 225377419108318701862933 10564566520702439149825)
              ·
                rfl

theorem cell20_208316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 6].length) (baseStart_208316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208316 prefixEnd_208316 := by exact prefixLift 208316
  have htrace : WordTrace (prefixWord ++ tailWord_208316) baseStart_208316 baseEnd_208316 := by
    simpa [prefixWord, tailWord_208316, baseEnd_208316] using wordTrace_append hprefix tailTrace_208316
  have hstable : (prefixWord ++ tailWord_208316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208316).length < 2 ^ (prefixWord ++ tailWord_208316).sum := by decide
  have hdescent : baseEnd_208316 < baseStart_208316 := by decide
  rcases family_descends (prefixWord ++ tailWord_208316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208320 : List Nat := [2, 1, 1, 2, 3, 1, 10]
def baseStart_208320 : Nat := 118140960795 + 208320 * 2 ^ 59
def prefixEnd_208320 : Nat := 4983230072969 + 3 ^ 40 * 208320 * 2
def baseEnd_208320 : Nat := 10564769377257301801675

theorem tailTrace_208320 : CollatzResearch.WordTrace tailWord_208320 prefixEnd_208320 10564769377257301801675 := by
  unfold tailWord_208320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799027302649846534291207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5065369736866462045721609 3799027302649846534291207)
  ·
    refine ⟨5698540953974769801436811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3799027302649846534291207 5698540953974769801436811)
    ·
      refine ⟨8547811430962154702155217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698540953974769801436811 8547811430962154702155217)
      ·
        refine ⟨6410858573221616026616413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8547811430962154702155217 6410858573221616026616413)
        ·
          refine ⟨2404071964958106009981155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6410858573221616026616413 2404071964958106009981155)
          ·
            refine ⟨3606107947437159014971733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404071964958106009981155 3606107947437159014971733)
            ·
              refine ⟨10564769377257301801675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3606107947437159014971733 10564769377257301801675)
              ·
                rfl

theorem cell20_208320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 10].length) (baseStart_208320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208320 prefixEnd_208320 := by exact prefixLift 208320
  have htrace : WordTrace (prefixWord ++ tailWord_208320) baseStart_208320 baseEnd_208320 := by
    simpa [prefixWord, tailWord_208320, baseEnd_208320] using wordTrace_append hprefix tailTrace_208320
  have hstable : (prefixWord ++ tailWord_208320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208320).length < 2 ^ (prefixWord ++ tailWord_208320).sum := by decide
  have hdescent : baseEnd_208320 < baseStart_208320 := by decide
  rcases family_descends (prefixWord ++ tailWord_208320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208330 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_208330 : Nat := 118140960795 + 208330 * 2 ^ 59
def prefixEnd_208330 : Nat := 4983230072969 + 3 ^ 40 * 208330 * 2
def baseEnd_208330 : Nat := 95087488667800125881701

theorem tailTrace_208330 : CollatzResearch.WordTrace tailWord_208330 prefixEnd_208330 95087488667800125881701 := by
  unfold tailWord_208330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1899604833815866194111611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5065612890175643184297629 1899604833815866194111611)
  ·
    refine ⟨2849407250723799291167417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1899604833815866194111611 2849407250723799291167417)
    ·
      refine ⟨2137055438042849468375563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2849407250723799291167417 2137055438042849468375563)
      ·
        refine ⟨3205583157064274202563345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137055438042849468375563 3205583157064274202563345)
        ·
          refine ⟨2404187367798205651922509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3205583157064274202563345 2404187367798205651922509)
          ·
            refine ⟨901570262924327119470941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2404187367798205651922509 901570262924327119470941)
            ·
              refine ⟨338088848596622669801603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 901570262924327119470941 338088848596622669801603)
              ·
                refine ⟨507133272894934004702405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338088848596622669801603 507133272894934004702405)
                ·
                  refine ⟨95087488667800125881701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507133272894934004702405 95087488667800125881701)
                  ·
                    rfl

theorem cell20_208330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_208330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208330 prefixEnd_208330 := by exact prefixLift 208330
  have htrace : WordTrace (prefixWord ++ tailWord_208330) baseStart_208330 baseEnd_208330 := by
    simpa [prefixWord, tailWord_208330, baseEnd_208330] using wordTrace_append hprefix tailTrace_208330
  have hstable : (prefixWord ++ tailWord_208330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208330).length < 2 ^ (prefixWord ++ tailWord_208330).sum := by decide
  have hdescent : baseEnd_208330 < baseStart_208330 := by decide
  rcases family_descends (prefixWord ++ tailWord_208330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208340 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_208340 : Nat := 118140960795 + 208340 * 2 ^ 59
def prefixEnd_208340 : Nat := 4983230072969 + 3 ^ 40 * 208340 * 2
def baseEnd_208340 : Nat := 95092052940284535548327

theorem tailTrace_208340 : CollatzResearch.WordTrace tailWord_208340 prefixEnd_208340 95092052940284535548327 := by
  unfold tailWord_208340
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799392032613618242155237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5065856043484824322873649 3799392032613618242155237)
  ·
    refine ⟨712386006115053420404107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3799392032613618242155237 712386006115053420404107)
    ·
      refine ⟨1068579009172580130606161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 712386006115053420404107 1068579009172580130606161)
      ·
        refine ⟨801434256879435097954621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1068579009172580130606161 801434256879435097954621)
        ·
          refine ⟨300537846329788161732983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 801434256879435097954621 300537846329788161732983)
          ·
            refine ⟨450806769494682242599475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300537846329788161732983 450806769494682242599475)
            ·
              refine ⟨676210154242023363899213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450806769494682242599475 676210154242023363899213)
              ·
                refine ⟨253578807840758761462205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676210154242023363899213 253578807840758761462205)
                ·
                  refine ⟨95092052940284535548327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253578807840758761462205 95092052940284535548327)
                  ·
                    rfl

theorem cell20_208340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_208340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208340 prefixEnd_208340 := by exact prefixLift 208340
  have htrace : WordTrace (prefixWord ++ tailWord_208340) baseStart_208340 baseEnd_208340 := by
    simpa [prefixWord, tailWord_208340, baseEnd_208340] using wordTrace_append hprefix tailTrace_208340
  have hstable : (prefixWord ++ tailWord_208340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208340).length < 2 ^ (prefixWord ++ tailWord_208340).sum := by decide
  have hdescent : baseEnd_208340 < baseStart_208340 := by decide
  rcases family_descends (prefixWord ++ tailWord_208340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208351 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_208351 : Nat := 118140960795 + 208351 * 2 ^ 59
def prefixEnd_208351 : Nat := 4983230072969 + 3 ^ 40 * 208351 * 2
def baseEnd_208351 : Nat := 95097073640017386181615

theorem tailTrace_208351 : CollatzResearch.WordTrace tailWord_208351 prefixEnd_208351 95097073640017386181615 := by
  unfold tailWord_208351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599185268187385362960907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5066123512124923575307271 7599185268187385362960907)
  ·
    refine ⟨11398777902281078044441361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599185268187385362960907 11398777902281078044441361)
    ·
      refine ⟨8549083426710808533331021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11398777902281078044441361 8549083426710808533331021)
      ·
        refine ⟨3205906285016553199999133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8549083426710808533331021 3205906285016553199999133)
        ·
          refine ⟨1202214856881207449999675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3205906285016553199999133 1202214856881207449999675)
          ·
            refine ⟨1803322285321811174999513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202214856881207449999675 1803322285321811174999513)
            ·
              refine ⟨1352491713991358381249635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803322285321811174999513 1352491713991358381249635)
              ·
                refine ⟨2028737570987037571874453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352491713991358381249635 2028737570987037571874453)
                ·
                  refine ⟨95097073640017386181615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2028737570987037571874453 95097073640017386181615)
                  ·
                    rfl

theorem cell20_208351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_208351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208351 prefixEnd_208351 := by exact prefixLift 208351
  have htrace : WordTrace (prefixWord ++ tailWord_208351) baseStart_208351 baseEnd_208351 := by
    simpa [prefixWord, tailWord_208351, baseEnd_208351] using wordTrace_append hprefix tailTrace_208351
  have hstable : (prefixWord ++ tailWord_208351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208351).length < 2 ^ (prefixWord ++ tailWord_208351).sum := by decide
  have hdescent : baseEnd_208351 < baseStart_208351 := by decide
  rcases family_descends (prefixWord ++ tailWord_208351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208389 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_208389 : Nat := 118140960795 + 208389 * 2 ^ 59
def prefixEnd_208389 : Nat := 4983230072969 + 3 ^ 40 * 208389 * 2
def baseEnd_208389 : Nat := 95114417875458142914793

theorem tailTrace_208389 : CollatzResearch.WordTrace tailWord_208389 prefixEnd_208389 95114417875458142914793 := by
  unfold tailWord_208389
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600571242049717852844221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5067047494699811901896147 7600571242049717852844221)
  ·
    refine ⟨2850214215768644194816583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7600571242049717852844221 2850214215768644194816583)
    ·
      refine ⟨4275321323652966292224875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850214215768644194816583 4275321323652966292224875)
      ·
        refine ⟨6412981985479449438337313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275321323652966292224875 6412981985479449438337313)
        ·
          refine ⟨4809736489109587078752985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6412981985479449438337313 4809736489109587078752985)
          ·
            refine ⟨3607302366832190309064739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4809736489109587078752985 3607302366832190309064739)
            ·
              refine ⟨5410953550248285463597109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607302366832190309064739 5410953550248285463597109)
              ·
                refine ⟨507276895335776762212229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5410953550248285463597109 507276895335776762212229)
                ·
                  refine ⟨95114417875458142914793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507276895335776762212229 95114417875458142914793)
                  ·
                    rfl

theorem cell20_208389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_208389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208389 prefixEnd_208389 := by exact prefixLift 208389
  have htrace : WordTrace (prefixWord ++ tailWord_208389) baseStart_208389 baseEnd_208389 := by
    simpa [prefixWord, tailWord_208389, baseEnd_208389] using wordTrace_append hprefix tailTrace_208389
  have hstable : (prefixWord ++ tailWord_208389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208389).length < 2 ^ (prefixWord ++ tailWord_208389).sum := by decide
  have hdescent : baseEnd_208389 < baseStart_208389 := by decide
  rcases family_descends (prefixWord ++ tailWord_208389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208437 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 3]
def baseStart_208437 : Nat := 118140960795 + 208437 * 2 ^ 59
def prefixEnd_208437 : Nat := 4983230072969 + 3 ^ 40 * 208437 * 2
def baseEnd_208437 : Nat := 95136326383383309314597

theorem tailTrace_208437 : CollatzResearch.WordTrace tailWord_208437 prefixEnd_208437 95136326383383309314597 := by
  unfold tailWord_208437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602321945875822050591565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5068214630583881367061043 7602321945875822050591565)
  ·
    refine ⟨2850870729703433268971837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7602321945875822050591565 2850870729703433268971837)
    ·
      refine ⟨1069076523638787475864439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2850870729703433268971837 1069076523638787475864439)
      ·
        refine ⟨1603614785458181213796659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069076523638787475864439 1603614785458181213796659)
        ·
          refine ⟨2405422178187271820694989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603614785458181213796659 2405422178187271820694989)
          ·
            refine ⟨902033316820226932760621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2405422178187271820694989 902033316820226932760621)
            ·
              refine ⟨338262493807585099785233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 902033316820226932760621 338262493807585099785233)
              ·
                refine ⟨253696870355688824838925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338262493807585099785233 253696870355688824838925)
                ·
                  refine ⟨95136326383383309314597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253696870355688824838925 95136326383383309314597)
                  ·
                    rfl

theorem cell20_208437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_208437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208437 prefixEnd_208437 := by exact prefixLift 208437
  have htrace : WordTrace (prefixWord ++ tailWord_208437) baseStart_208437 baseEnd_208437 := by
    simpa [prefixWord, tailWord_208437, baseEnd_208437] using wordTrace_append hprefix tailTrace_208437
  have hstable : (prefixWord ++ tailWord_208437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208437).length < 2 ^ (prefixWord ++ tailWord_208437).sum := by decide
  have hdescent : baseEnd_208437 < baseStart_208437 := by decide
  rcases family_descends (prefixWord ++ tailWord_208437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208465 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_208465 : Nat := 118140960795 + 208465 * 2 ^ 59
def prefixEnd_208465 : Nat := 4983230072969 + 3 ^ 40 * 208465 * 2
def baseEnd_208465 : Nat := 95149106346339656381149

theorem tailTrace_208465 : CollatzResearch.WordTrace tailWord_208465 prefixEnd_208465 95149106346339656381149 := by
  unfold tailWord_208465
  simp only [CollatzResearch.WordTrace]
  refine ⟨7603343189774382832610849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5068895459849588555073899 7603343189774382832610849)
  ·
    refine ⟨5702507392330787124458137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7603343189774382832610849 5702507392330787124458137)
    ·
      refine ⟨4276880544248090343343603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5702507392330787124458137 4276880544248090343343603)
      ·
        refine ⟨6415320816372135515015405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276880544248090343343603 6415320816372135515015405)
        ·
          refine ⟨2405745306139550818130777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6415320816372135515015405 2405745306139550818130777)
          ·
            refine ⟨1804308979604663113598083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2405745306139550818130777 1804308979604663113598083)
            ·
              refine ⟨2706463469406994670397125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804308979604663113598083 2706463469406994670397125)
              ·
                refine ⟨507461900513811500699461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2706463469406994670397125 507461900513811500699461)
                ·
                  refine ⟨95149106346339656381149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507461900513811500699461 95149106346339656381149)
                  ·
                    rfl

theorem cell20_208465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_208465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208465 prefixEnd_208465 := by exact prefixLift 208465
  have htrace : WordTrace (prefixWord ++ tailWord_208465) baseStart_208465 baseEnd_208465 := by
    simpa [prefixWord, tailWord_208465, baseEnd_208465] using wordTrace_append hprefix tailTrace_208465
  have hstable : (prefixWord ++ tailWord_208465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208465).length < 2 ^ (prefixWord ++ tailWord_208465).sum := by decide
  have hdescent : baseEnd_208465 < baseStart_208465 := by decide
  rcases family_descends (prefixWord ++ tailWord_208465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208496 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_208496 : Nat := 118140960795 + 208496 * 2 ^ 59
def prefixEnd_208496 : Nat := 4983230072969 + 3 ^ 40 * 208496 * 2
def baseEnd_208496 : Nat := 95163255591041326347689

theorem tailTrace_208496 : CollatzResearch.WordTrace tailWord_208496 prefixEnd_208496 95163255591041326347689 := by
  unfold tailWord_208496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802236926331037563494671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5069649235108050084659561 3802236926331037563494671)
  ·
    refine ⟨5703355389496556345242007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802236926331037563494671 5703355389496556345242007)
    ·
      refine ⟨8555033084244834517863011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703355389496556345242007 8555033084244834517863011)
      ·
        refine ⟨12832549626367251776794517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555033084244834517863011 12832549626367251776794517)
        ·
          refine ⟨601525763735964927037243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12832549626367251776794517 601525763735964927037243)
          ·
            refine ⟨902288645603947390555865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601525763735964927037243 902288645603947390555865)
            ·
              refine ⟨676716484202960542916899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902288645603947390555865 676716484202960542916899)
              ·
                refine ⟨1015074726304440814375349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676716484202960542916899 1015074726304440814375349)
                ·
                  refine ⟨95163255591041326347689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1015074726304440814375349 95163255591041326347689)
                  ·
                    rfl

theorem cell20_208496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_208496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208496 prefixEnd_208496 := by exact prefixLift 208496
  have htrace : WordTrace (prefixWord ++ tailWord_208496) baseStart_208496 baseEnd_208496 := by
    simpa [prefixWord, tailWord_208496, baseEnd_208496] using wordTrace_append hprefix tailTrace_208496
  have hstable : (prefixWord ++ tailWord_208496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208496).length < 2 ^ (prefixWord ++ tailWord_208496).sum := by decide
  have hdescent : baseEnd_208496 < baseStart_208496 := by decide
  rcases family_descends (prefixWord ++ tailWord_208496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208513 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 3]
def baseStart_208513 : Nat := 118140960795 + 208513 * 2 ^ 59
def prefixEnd_208513 : Nat := 4983230072969 + 3 ^ 40 * 208513 * 2
def baseEnd_208513 : Nat := 95171014854264822780953

theorem tailTrace_208513 : CollatzResearch.WordTrace tailWord_208513 prefixEnd_208513 95171014854264822780953 := by
  unfold tailWord_208513
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605093893600487030358193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5070062595733658020238795 7605093893600487030358193)
  ·
    refine ⟨5703820420200365272768645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7605093893600487030358193 5703820420200365272768645)
    ·
      refine ⟨1069466328787568488644121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5703820420200365272768645 1069466328787568488644121)
      ·
        refine ⟨802099746590676366483091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069466328787568488644121 802099746590676366483091)
        ·
          refine ⟨1203149619886014549724637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802099746590676366483091 1203149619886014549724637)
          ·
            refine ⟨451181107457255456146739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1203149619886014549724637 451181107457255456146739)
            ·
              refine ⟨676771661185883184220109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451181107457255456146739 676771661185883184220109)
              ·
                refine ⟨253789372944706194082541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676771661185883184220109 253789372944706194082541)
                ·
                  refine ⟨95171014854264822780953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253789372944706194082541 95171014854264822780953)
                  ·
                    rfl

theorem cell20_208513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_208513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208513 prefixEnd_208513 := by exact prefixLift 208513
  have htrace : WordTrace (prefixWord ++ tailWord_208513) baseStart_208513 baseEnd_208513 := by
    simpa [prefixWord, tailWord_208513, baseEnd_208513] using wordTrace_append hprefix tailTrace_208513
  have hstable : (prefixWord ++ tailWord_208513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208513).length < 2 ^ (prefixWord ++ tailWord_208513).sum := by decide
  have hdescent : baseEnd_208513 < baseStart_208513 := by decide
  rcases family_descends (prefixWord ++ tailWord_208513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208548 : List Nat := [2, 3, 1, 2, 2, 10]
def baseStart_208548 : Nat := 118140960795 + 208548 * 2 ^ 59
def prefixEnd_208548 : Nat := 4983230072969 + 3 ^ 40 * 208548 * 2
def baseEnd_208548 : Nat := 3525444066961490985709

theorem tailTrace_208548 : CollatzResearch.WordTrace tailWord_208548 prefixEnd_208548 3525444066961490985709 := by
  unfold tailWord_208548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803185224236844003941149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5070913632315792005254865 3803185224236844003941149)
  ·
    refine ⟨1426194459088816501477931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3803185224236844003941149 1426194459088816501477931)
    ·
      refine ⟨2139291688633224752216897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426194459088816501477931 2139291688633224752216897)
      ·
        refine ⟨1604468766474918564162673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2139291688633224752216897 1604468766474918564162673)
        ·
          refine ⟨1203351574856188923122005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604468766474918564162673 1203351574856188923122005)
          ·
            refine ⟨3525444066961490985709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1203351574856188923122005 3525444066961490985709)
            ·
              rfl

theorem cell20_208548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 10].length) (baseStart_208548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208548 prefixEnd_208548 := by exact prefixLift 208548
  have htrace : WordTrace (prefixWord ++ tailWord_208548) baseStart_208548 baseEnd_208548 := by
    simpa [prefixWord, tailWord_208548, baseEnd_208548] using wordTrace_append hprefix tailTrace_208548
  have hstable : (prefixWord ++ tailWord_208548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208548).length < 2 ^ (prefixWord ++ tailWord_208548).sum := by decide
  have hdescent : baseEnd_208548 < baseStart_208548 := by decide
  rcases family_descends (prefixWord ++ tailWord_208548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208641 : List Nat := [1, 2, 4, 1, 1, 1, 6, 4]
def baseStart_208641 : Nat := 118140960795 + 208641 * 2 ^ 59
def prefixEnd_208641 : Nat := 4983230072969 + 3 ^ 40 * 208641 * 2
def baseEnd_208641 : Nat := 31743145847355088837921

theorem tailTrace_208641 : CollatzResearch.WordTrace tailWord_208641 prefixEnd_208641 31743145847355088837921 := by
  unfold tailWord_208641
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609762437136764891017777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5073174958091176594011851 7609762437136764891017777)
  ·
    refine ⟨5707321827852573668263333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7609762437136764891017777 5707321827852573668263333)
    ·
      refine ⟨1070122842722357562799375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5707321827852573668263333 1070122842722357562799375)
      ·
        refine ⟨1605184264083536344199063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070122842722357562799375 1605184264083536344199063)
        ·
          refine ⟨2407776396125304516298595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605184264083536344199063 2407776396125304516298595)
          ·
            refine ⟨3611664594187956774447893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407776396125304516298595 3611664594187956774447893)
            ·
              refine ⟨169296777852560473802245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3611664594187956774447893 169296777852560473802245)
              ·
                refine ⟨31743145847355088837921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169296777852560473802245 31743145847355088837921)
                ·
                  rfl

theorem cell20_208641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_208641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208641 prefixEnd_208641 := by exact prefixLift 208641
  have htrace : WordTrace (prefixWord ++ tailWord_208641) baseStart_208641 baseEnd_208641 := by
    simpa [prefixWord, tailWord_208641, baseEnd_208641] using wordTrace_append hprefix tailTrace_208641
  have hstable : (prefixWord ++ tailWord_208641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208641).length < 2 ^ (prefixWord ++ tailWord_208641).sum := by decide
  have hdescent : baseEnd_208641 < baseStart_208641 := by decide
  rcases family_descends (prefixWord ++ tailWord_208641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208647 : List Nat := [1, 1, 4, 4, 3, 1, 1, 3, 2]
def baseStart_208647 : Nat := 118140960795 + 208647 * 2 ^ 59
def prefixEnd_208647 : Nat := 4983230072969 + 3 ^ 40 * 208647 * 2
def baseEnd_208647 : Nat := 95232176105555912313739

theorem tailTrace_208647 : CollatzResearch.WordTrace tailWord_208647 prefixEnd_208647 95232176105555912313739 := by
  unfold tailWord_208647
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609981275115027915736195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5073320850076685277157463 7609981275115027915736195)
  ·
    refine ⟨11414971912672541873604293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7609981275115027915736195 11414971912672541873604293)
    ·
      refine ⟨2140307233626101601300805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11414971912672541873604293 2140307233626101601300805)
      ·
        refine ⟨401307606304894050243901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2140307233626101601300805 401307606304894050243901)
        ·
          refine ⟨150490352364335268841463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401307606304894050243901 150490352364335268841463)
          ·
            refine ⟨225735528546502903262195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150490352364335268841463 225735528546502903262195)
            ·
              refine ⟨338603292819754354893293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225735528546502903262195 338603292819754354893293)
              ·
                refine ⟨126976234807407883084985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338603292819754354893293 126976234807407883084985)
                ·
                  refine ⟨95232176105555912313739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126976234807407883084985 95232176105555912313739)
                  ·
                    rfl

theorem cell20_208647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 2].length) (baseStart_208647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208647 prefixEnd_208647 := by exact prefixLift 208647
  have htrace : WordTrace (prefixWord ++ tailWord_208647) baseStart_208647 baseEnd_208647 := by
    simpa [prefixWord, tailWord_208647, baseEnd_208647] using wordTrace_append hprefix tailTrace_208647
  have hstable : (prefixWord ++ tailWord_208647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208647).length < 2 ^ (prefixWord ++ tailWord_208647).sum := by decide
  have hdescent : baseEnd_208647 < baseStart_208647 := by decide
  rcases family_descends (prefixWord ++ tailWord_208647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208658 : List Nat := [3, 2, 4, 1, 1, 3, 6]
def baseStart_208658 : Nat := 118140960795 + 208658 * 2 ^ 59
def prefixEnd_208658 : Nat := 4983230072969 + 3 ^ 40 * 208658 * 2
def baseEnd_208658 : Nat := 10581910756143195883003

theorem tailTrace_208658 : CollatzResearch.WordTrace tailWord_208658 prefixEnd_208658 10581910756143195883003 := by
  unfold tailWord_208658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902595619518794198596657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5073588318716784529591085 1902595619518794198596657)
  ·
    refine ⟨1426946714639095648947493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1902595619518794198596657 1426946714639095648947493)
    ·
      refine ⟨267552508994830434177655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1426946714639095648947493 267552508994830434177655)
      ·
        refine ⟨401328763492245651266483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267552508994830434177655 401328763492245651266483)
        ·
          refine ⟨601993145238368476899725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401328763492245651266483 601993145238368476899725)
          ·
            refine ⟨225747429464388178837397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601993145238368476899725 225747429464388178837397)
            ·
              refine ⟨10581910756143195883003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 225747429464388178837397 10581910756143195883003)
              ·
                rfl

theorem cell20_208658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 6].length) (baseStart_208658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208658 prefixEnd_208658 := by exact prefixLift 208658
  have htrace : WordTrace (prefixWord ++ tailWord_208658) baseStart_208658 baseEnd_208658 := by
    simpa [prefixWord, tailWord_208658, baseEnd_208658] using wordTrace_append hprefix tailTrace_208658
  have hstable : (prefixWord ++ tailWord_208658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208658).length < 2 ^ (prefixWord ++ tailWord_208658).sum := by decide
  have hdescent : baseEnd_208658 < baseStart_208658 := by decide
  rcases family_descends (prefixWord ++ tailWord_208658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208700 : List Nat := [2, 2, 2, 2, 1, 1, 4, 6]
def baseStart_208700 : Nat := 118140960795 + 208700 * 2 ^ 59
def prefixEnd_208700 : Nat := 4983230072969 + 3 ^ 40 * 208700 * 2
def baseEnd_208700 : Nat := 31752122249907761182285

theorem tailTrace_208700 : CollatzResearch.WordTrace tailWord_208700 prefixEnd_208700 31752122249907761182285 := by
  unfold tailWord_208700
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805957171961508983707777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5074609562615345311610369 3805957171961508983707777)
  ·
    refine ⟨2854467878971131737780833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3805957171961508983707777 2854467878971131737780833)
    ·
      refine ⟨2140850909228348803335625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2854467878971131737780833 2140850909228348803335625)
      ·
        refine ⟨1605638181921261602501719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2140850909228348803335625 1605638181921261602501719)
        ·
          refine ⟨2408457272881892403752579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605638181921261602501719 2408457272881892403752579)
          ·
            refine ⟨3612685909322838605628869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408457272881892403752579 3612685909322838605628869)
            ·
              refine ⟨677378607998032238555413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3612685909322838605628869 677378607998032238555413)
              ·
                refine ⟨31752122249907761182285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 677378607998032238555413 31752122249907761182285)
                ·
                  rfl

theorem cell20_208700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_208700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208700 prefixEnd_208700 := by exact prefixLift 208700
  have htrace : WordTrace (prefixWord ++ tailWord_208700) baseStart_208700 baseEnd_208700 := by
    simpa [prefixWord, tailWord_208700, baseEnd_208700] using wordTrace_append hprefix tailTrace_208700
  have hstable : (prefixWord ++ tailWord_208700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208700).length < 2 ^ (prefixWord ++ tailWord_208700).sum := by decide
  have hdescent : baseEnd_208700 < baseStart_208700 := by decide
  rcases family_descends (prefixWord ++ tailWord_208700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208717 : List Nat := [1, 6, 1, 2, 1, 9]
def baseStart_208717 : Nat := 118140960795 + 208717 * 2 ^ 59
def prefixEnd_208717 : Nat := 4983230072969 + 3 ^ 40 * 208717 * 2
def baseEnd_208717 : Nat := 3528300963442473332597

theorem tailTrace_208717 : CollatzResearch.WordTrace tailWord_208717 prefixEnd_208717 3528300963442473332597 := by
  unfold tailWord_208717
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612534384861429870784405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5075022923240953247189603 7612534384861429870784405)
  ·
    refine ⟨356837549290379525193019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7612534384861429870784405 356837549290379525193019)
    ·
      refine ⟨535256323935569287789529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356837549290379525193019 535256323935569287789529)
      ·
        refine ⟨401442242951676965842147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535256323935569287789529 401442242951676965842147)
        ·
          refine ⟨602163364427515448763221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401442242951676965842147 602163364427515448763221)
          ·
            refine ⟨3528300963442473332597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 602163364427515448763221 3528300963442473332597)
            ·
              rfl

theorem cell20_208717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 9].length) (baseStart_208717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208717 prefixEnd_208717 := by exact prefixLift 208717
  have htrace : WordTrace (prefixWord ++ tailWord_208717) baseStart_208717 baseEnd_208717 := by
    simpa [prefixWord, tailWord_208717, baseEnd_208717] using wordTrace_append hprefix tailTrace_208717
  have hstable : (prefixWord ++ tailWord_208717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208717).length < 2 ^ (prefixWord ++ tailWord_208717).sum := by decide
  have hdescent : baseEnd_208717 < baseStart_208717 := by decide
  rcases family_descends (prefixWord ++ tailWord_208717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208727 : List Nat := [1, 1, 3, 2, 5, 1, 1, 4, 2]
def baseStart_208727 : Nat := 118140960795 + 208727 * 2 ^ 59
def prefixEnd_208727 : Nat := 4983230072969 + 3 ^ 40 * 208727 * 2
def baseEnd_208727 : Nat := 95268690285431189646745

theorem tailTrace_208727 : CollatzResearch.WordTrace tailWord_208727 prefixEnd_208727 95268690285431189646745 := by
  unfold tailWord_208727
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612899114825201578648435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5075266076550134385765623 7612899114825201578648435)
  ·
    refine ⟨11419348672237802367972653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7612899114825201578648435 11419348672237802367972653)
    ·
      refine ⟨4282255752089175887989745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11419348672237802367972653 4282255752089175887989745)
      ·
        refine ⟨3211691814066881915992309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4282255752089175887989745 3211691814066881915992309)
        ·
          refine ⟨301096107568770179624279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3211691814066881915992309 301096107568770179624279)
          ·
            refine ⟨451644161353155269436419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301096107568770179624279 451644161353155269436419)
            ·
              refine ⟨677466242029732904154629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451644161353155269436419 677466242029732904154629)
              ·
                refine ⟨127024920380574919528993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677466242029732904154629 127024920380574919528993)
                ·
                  refine ⟨95268690285431189646745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127024920380574919528993 95268690285431189646745)
                  ·
                    rfl

theorem cell20_208727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 2].length) (baseStart_208727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208727 prefixEnd_208727 := by exact prefixLift 208727
  have htrace : WordTrace (prefixWord ++ tailWord_208727) baseStart_208727 baseEnd_208727 := by
    simpa [prefixWord, tailWord_208727, baseEnd_208727] using wordTrace_append hprefix tailTrace_208727
  have hstable : (prefixWord ++ tailWord_208727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208727).length < 2 ^ (prefixWord ++ tailWord_208727).sum := by decide
  have hdescent : baseEnd_208727 < baseStart_208727 := by decide
  rcases family_descends (prefixWord ++ tailWord_208727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208786 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_208786 : Nat := 118140960795 + 208786 * 2 ^ 59
def prefixEnd_208786 : Nat := 4983230072969 + 3 ^ 40 * 208786 * 2
def baseEnd_208786 : Nat := 95295619493089206679837

theorem tailTrace_208786 : CollatzResearch.WordTrace tailWord_208786 prefixEnd_208786 95295619493089206679837 := by
  unfold tailWord_208786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903762755402863663761553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5076700681074303103364141 1903762755402863663761553)
  ·
    refine ⟨1427822066552147747821165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1903762755402863663761553 1427822066552147747821165)
    ·
      refine ⟨535433274957055405432937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1427822066552147747821165 535433274957055405432937)
      ·
        refine ⟨401574956217791554074703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535433274957055405432937 401574956217791554074703)
        ·
          refine ⟨602362434326687331112055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401574956217791554074703 602362434326687331112055)
          ·
            refine ⟨903543651490030996668083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602362434326687331112055 903543651490030996668083)
            ·
              refine ⟨1355315477235046495002125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903543651490030996668083 1355315477235046495002125)
              ·
                refine ⟨508243303963142435625797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355315477235046495002125 508243303963142435625797)
                ·
                  refine ⟨95295619493089206679837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508243303963142435625797 95295619493089206679837)
                  ·
                    rfl

theorem cell20_208786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_208786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208786 prefixEnd_208786 := by exact prefixLift 208786
  have htrace : WordTrace (prefixWord ++ tailWord_208786) baseStart_208786 baseEnd_208786 := by
    simpa [prefixWord, tailWord_208786, baseEnd_208786] using wordTrace_append hprefix tailTrace_208786
  have hstable : (prefixWord ++ tailWord_208786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208786).length < 2 ^ (prefixWord ++ tailWord_208786).sum := by decide
  have hdescent : baseEnd_208786 < baseStart_208786 := by decide
  rcases family_descends (prefixWord ++ tailWord_208786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208796 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_208796 : Nat := 118140960795 + 208796 * 2 ^ 59
def prefixEnd_208796 : Nat := 4983230072969 + 3 ^ 40 * 208796 * 2
def baseEnd_208796 : Nat := 95300183765573616346463

theorem tailTrace_208796 : CollatzResearch.WordTrace tailWord_208796 prefixEnd_208796 95300183765573616346463 := by
  unfold tailWord_208796
  simp only [CollatzResearch.WordTrace]
  refine ⟨3807707875787613181455121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5076943834383484241940161 3807707875787613181455121)
  ·
    refine ⟨2855780906840709886091341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3807707875787613181455121 2855780906840709886091341)
    ·
      refine ⟨1070917840065266207284253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2855780906840709886091341 1070917840065266207284253)
      ·
        refine ⟨401594190024474827731595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1070917840065266207284253 401594190024474827731595)
        ·
          refine ⟨602391285036712241597393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401594190024474827731595 602391285036712241597393)
          ·
            refine ⟨451793463777534181198045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602391285036712241597393 451793463777534181198045)
            ·
              refine ⟨169422548916575317949267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 451793463777534181198045 169422548916575317949267)
              ·
                refine ⟨254133823374862976923901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169422548916575317949267 254133823374862976923901)
                ·
                  refine ⟨95300183765573616346463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254133823374862976923901 95300183765573616346463)
                  ·
                    rfl

theorem cell20_208796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_208796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208796 prefixEnd_208796 := by exact prefixLift 208796
  have htrace : WordTrace (prefixWord ++ tailWord_208796) baseStart_208796 baseEnd_208796 := by
    simpa [prefixWord, tailWord_208796, baseEnd_208796] using wordTrace_append hprefix tailTrace_208796
  have hstable : (prefixWord ++ tailWord_208796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208796).length < 2 ^ (prefixWord ++ tailWord_208796).sum := by decide
  have hdescent : baseEnd_208796 < baseStart_208796 := by decide
  rcases family_descends (prefixWord ++ tailWord_208796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208952 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_208952 : Nat := 118140960795 + 208952 * 2 ^ 59
def prefixEnd_208952 : Nat := 4983230072969 + 3 ^ 40 * 208952 * 2
def baseEnd_208952 : Nat := 95371386416330407145825

theorem tailTrace_208952 : CollatzResearch.WordTrace tailWord_208952 prefixEnd_208952 95371386416330407145825 := by
  unfold tailWord_208952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810552769505032502794555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5080737026006710003726073 3810552769505032502794555)
  ·
    refine ⟨5715829154257548754191833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3810552769505032502794555 5715829154257548754191833)
    ·
      refine ⟨4286871865693161565643875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5715829154257548754191833 4286871865693161565643875)
      ·
        refine ⟨6430307798539742348465813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286871865693161565643875 6430307798539742348465813)
        ·
          refine ⟨301420678056550422584335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6430307798539742348465813 301420678056550422584335)
          ·
            refine ⟨452131017084825633876503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301420678056550422584335 452131017084825633876503)
            ·
              refine ⟨678196525627238450814755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452131017084825633876503 678196525627238450814755)
              ·
                refine ⟨1017294788440857676222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678196525627238450814755 1017294788440857676222133)
                ·
                  refine ⟨95371386416330407145825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1017294788440857676222133 95371386416330407145825)
                  ·
                    rfl

theorem cell20_208952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_208952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_208952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_208952 prefixEnd_208952 := by exact prefixLift 208952
  have htrace : WordTrace (prefixWord ++ tailWord_208952) baseStart_208952 baseEnd_208952 := by
    simpa [prefixWord, tailWord_208952, baseEnd_208952] using wordTrace_append hprefix tailTrace_208952
  have hstable : (prefixWord ++ tailWord_208952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208952).length < 2 ^ (prefixWord ++ tailWord_208952).sum := by decide
  have hdescent : baseEnd_208952 < baseStart_208952 := by decide
  rcases family_descends (prefixWord ++ tailWord_208952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209004 : List Nat := [2, 2, 1, 1, 3, 5, 6]
def baseStart_209004 : Nat := 118140960795 + 209004 * 2 ^ 59
def prefixEnd_209004 : Nat := 4983230072969 + 3 ^ 40 * 209004 * 2
def baseEnd_209004 : Nat := 10599457848138815268031

theorem tailTrace_209004 : CollatzResearch.WordTrace tailWord_209004 prefixEnd_209004 10599457848138815268031 := by
  unfold tailWord_209004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811501067410838943241033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5082001423214451924321377 3811501067410838943241033)
  ·
    refine ⟨2858625800558129207430775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3811501067410838943241033 2858625800558129207430775)
    ·
      refine ⟨4287938700837193811146163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858625800558129207430775 4287938700837193811146163)
      ·
        refine ⟨6431908051255790716719245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287938700837193811146163 6431908051255790716719245)
        ·
          refine ⟨2411965519220921518769717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6431908051255790716719245 2411965519220921518769717)
          ·
            refine ⟨226121767426961392384661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2411965519220921518769717 226121767426961392384661)
            ·
              refine ⟨10599457848138815268031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 226121767426961392384661 10599457848138815268031)
              ·
                rfl

theorem cell20_209004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 6].length) (baseStart_209004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209004 prefixEnd_209004 := by exact prefixLift 209004
  have htrace : WordTrace (prefixWord ++ tailWord_209004) baseStart_209004 baseEnd_209004 := by
    simpa [prefixWord, tailWord_209004, baseEnd_209004] using wordTrace_append hprefix tailTrace_209004
  have hstable : (prefixWord ++ tailWord_209004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209004).length < 2 ^ (prefixWord ++ tailWord_209004).sum := by decide
  have hdescent : baseEnd_209004 < baseStart_209004 := by decide
  rcases family_descends (prefixWord ++ tailWord_209004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209014 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_209014 : Nat := 118140960795 + 209014 * 2 ^ 59
def prefixEnd_209014 : Nat := 4983230072969 + 3 ^ 40 * 209014 * 2
def baseEnd_209014 : Nat := 95399684905733747078905

theorem tailTrace_209014 : CollatzResearch.WordTrace tailWord_209014 prefixEnd_209014 95399684905733747078905 := by
  unfold tailWord_209014
  simp only [CollatzResearch.WordTrace]
  refine ⟨476460429049090599646631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5082244576523633062897397 476460429049090599646631)
  ·
    refine ⟨714690643573635899469947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476460429049090599646631 714690643573635899469947)
    ·
      refine ⟨1072035965360453849204921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714690643573635899469947 1072035965360453849204921)
      ·
        refine ⟨804026974020340386903691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072035965360453849204921 804026974020340386903691)
        ·
          refine ⟨1206040461030510580355537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804026974020340386903691 1206040461030510580355537)
          ·
            refine ⟨904530345772882935266653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206040461030510580355537 904530345772882935266653)
            ·
              refine ⟨339198879664831100724995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 904530345772882935266653 339198879664831100724995)
              ·
                refine ⟨508798319497246651087493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339198879664831100724995 508798319497246651087493)
                ·
                  refine ⟨95399684905733747078905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508798319497246651087493 95399684905733747078905)
                  ·
                    rfl

theorem cell20_209014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_209014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209014 prefixEnd_209014 := by exact prefixLift 209014
  have htrace : WordTrace (prefixWord ++ tailWord_209014) baseStart_209014 baseEnd_209014 := by
    simpa [prefixWord, tailWord_209014, baseEnd_209014] using wordTrace_append hprefix tailTrace_209014
  have hstable : (prefixWord ++ tailWord_209014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209014).length < 2 ^ (prefixWord ++ tailWord_209014).sum := by decide
  have hdescent : baseEnd_209014 < baseStart_209014 := by decide
  rcases family_descends (prefixWord ++ tailWord_209014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209028 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_209028 : Nat := 118140960795 + 209028 * 2 ^ 59
def prefixEnd_209028 : Nat := 4983230072969 + 3 ^ 40 * 209028 * 2
def baseEnd_209028 : Nat := 95406074887211920612181

theorem tailTrace_209028 : CollatzResearch.WordTrace tailWord_209028 prefixEnd_209028 95406074887211920612181 := by
  unfold tailWord_209028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811938743367364992677869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5082584991156486656903825 3811938743367364992677869)
  ·
    refine ⟨1429477028762761872254201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3811938743367364992677869 1429477028762761872254201)
    ·
      refine ⟨1072107771572071404190651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1429477028762761872254201 1072107771572071404190651)
      ·
        refine ⟨1608161657358107106285977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072107771572071404190651 1608161657358107106285977)
        ·
          refine ⟨1206121243018580329714483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608161657358107106285977 1206121243018580329714483)
          ·
            refine ⟨1809181864527870494571725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206121243018580329714483 1809181864527870494571725)
            ·
              refine ⟨678443199197951435464397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1809181864527870494571725 678443199197951435464397)
              ·
                refine ⟨254416199699231788299149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 678443199197951435464397 254416199699231788299149)
                ·
                  refine ⟨95406074887211920612181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254416199699231788299149 95406074887211920612181)
                  ·
                    rfl

theorem cell20_209028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_209028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209028 prefixEnd_209028 := by exact prefixLift 209028
  have htrace : WordTrace (prefixWord ++ tailWord_209028) baseStart_209028 baseEnd_209028 := by
    simpa [prefixWord, tailWord_209028, baseEnd_209028] using wordTrace_append hprefix tailTrace_209028
  have hstable : (prefixWord ++ tailWord_209028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209028).length < 2 ^ (prefixWord ++ tailWord_209028).sum := by decide
  have hdescent : baseEnd_209028 < baseStart_209028 := by decide
  rcases family_descends (prefixWord ++ tailWord_209028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209042 : List Nat := [3, 2, 3, 1, 1, 1, 1, 8]
def baseStart_209042 : Nat := 118140960795 + 209042 * 2 ^ 59
def prefixEnd_209042 : Nat := 4983230072969 + 3 ^ 40 * 209042 * 2
def baseEnd_209042 : Nat := 31804154956230031381819

theorem tailTrace_209042 : CollatzResearch.WordTrace tailWord_209042 prefixEnd_209042 31804154956230031381819 := by
  unfold tailWord_209042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906097027171002594091345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5082925405789340250910253 1906097027171002594091345)
  ·
    refine ⟨1429572770378251945568509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1906097027171002594091345 1429572770378251945568509)
    ·
      refine ⟨536089788891844479588191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1429572770378251945568509 536089788891844479588191)
      ·
        refine ⟨804134683337766719382287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536089788891844479588191 804134683337766719382287)
        ·
          refine ⟨1206202025006650079073431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804134683337766719382287 1206202025006650079073431)
          ·
            refine ⟨1809303037509975118610147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206202025006650079073431 1809303037509975118610147)
            ·
              refine ⟨2713954556264962677915221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809303037509975118610147 2713954556264962677915221)
              ·
                refine ⟨31804154956230031381819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2713954556264962677915221 31804154956230031381819)
                ·
                  rfl

theorem cell20_209042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_209042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209042 prefixEnd_209042 := by exact prefixLift 209042
  have htrace : WordTrace (prefixWord ++ tailWord_209042) baseStart_209042 baseEnd_209042 := by
    simpa [prefixWord, tailWord_209042, baseEnd_209042] using wordTrace_append hprefix tailTrace_209042
  have hstable : (prefixWord ++ tailWord_209042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209042).length < 2 ^ (prefixWord ++ tailWord_209042).sum := by decide
  have hdescent : baseEnd_209042 < baseStart_209042 := by decide
  rcases family_descends (prefixWord ++ tailWord_209042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209052 : List Nat := [2, 2, 3, 2, 1, 1, 2, 5, 2]
def baseStart_209052 : Nat := 118140960795 + 209052 * 2 ^ 59
def prefixEnd_209052 : Nat := 4983230072969 + 3 ^ 40 * 209052 * 2
def baseEnd_209052 : Nat := 95417029141174503812083

theorem tailTrace_209052 : CollatzResearch.WordTrace tailWord_209052 prefixEnd_209052 95417029141174503812083 := by
  unfold tailWord_209052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812376419323891042114705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5083168559098521389486273 3812376419323891042114705)
  ·
    refine ⟨2859282314492918281586029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3812376419323891042114705 2859282314492918281586029)
    ·
      refine ⟨1072230867934844355594761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2859282314492918281586029 1072230867934844355594761)
      ·
        refine ⟨804173150951133266696071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072230867934844355594761 804173150951133266696071)
        ·
          refine ⟨1206259726426699900044107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804173150951133266696071 1206259726426699900044107)
          ·
            refine ⟨1809389589640049850066161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206259726426699900044107 1809389589640049850066161)
            ·
              refine ⟨1357042192230037387549621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1809389589640049850066161 1357042192230037387549621)
              ·
                refine ⟨127222705521566005082777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1357042192230037387549621 127222705521566005082777)
                ·
                  refine ⟨95417029141174503812083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127222705521566005082777 95417029141174503812083)
                  ·
                    rfl

theorem cell20_209052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_209052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209052 prefixEnd_209052 := by exact prefixLift 209052
  have htrace : WordTrace (prefixWord ++ tailWord_209052) baseStart_209052 baseEnd_209052 := by
    simpa [prefixWord, tailWord_209052, baseEnd_209052] using wordTrace_append hprefix tailTrace_209052
  have hstable : (prefixWord ++ tailWord_209052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209052).length < 2 ^ (prefixWord ++ tailWord_209052).sum := by decide
  have hdescent : baseEnd_209052 < baseStart_209052 := by decide
  rcases family_descends (prefixWord ++ tailWord_209052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209069 : List Nat := [1, 5, 2, 1, 2, 2, 1, 4, 2]
def baseStart_209069 : Nat := 118140960795 + 209069 * 2 ^ 59
def prefixEnd_209069 : Nat := 4983230072969 + 3 ^ 40 * 209069 * 2
def baseEnd_209069 : Nat := 95424788404398000245347

theorem tailTrace_209069 : CollatzResearch.WordTrace tailWord_209069 prefixEnd_209069 95424788404398000245347 := by
  unfold tailWord_209069
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625372879586193987598261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5083581919724129325065507 7625372879586193987598261)
  ·
    refine ⟨714878707461205686337337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7625372879586193987598261 714878707461205686337337)
    ·
      refine ⟨536159030595904264753003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 714878707461205686337337 536159030595904264753003)
      ·
        refine ⟨804238545893856397129505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536159030595904264753003 804238545893856397129505)
        ·
          refine ⟨603178909420392297847129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804238545893856397129505 603178909420392297847129)
          ·
            refine ⟨452384182065294223385347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603178909420392297847129 452384182065294223385347)
            ·
              refine ⟨678576273097941335078021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452384182065294223385347 678576273097941335078021)
              ·
                refine ⟨127233051205864000327129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678576273097941335078021 127233051205864000327129)
                ·
                  refine ⟨95424788404398000245347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127233051205864000327129 95424788404398000245347)
                  ·
                    rfl

theorem cell20_209069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_209069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209069 prefixEnd_209069 := by exact prefixLift 209069
  have htrace : WordTrace (prefixWord ++ tailWord_209069) baseStart_209069 baseEnd_209069 := by
    simpa [prefixWord, tailWord_209069, baseEnd_209069] using wordTrace_append hprefix tailTrace_209069
  have hstable : (prefixWord ++ tailWord_209069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209069).length < 2 ^ (prefixWord ++ tailWord_209069).sum := by decide
  have hdescent : baseEnd_209069 < baseStart_209069 := by decide
  rcases family_descends (prefixWord ++ tailWord_209069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209128 : List Nat := [2, 1, 4, 1, 2, 2, 2, 4, 2]
def baseStart_209128 : Nat := 118140960795 + 209128 * 2 ^ 59
def prefixEnd_209128 : Nat := 4983230072969 + 3 ^ 40 * 209128 * 2
def baseEnd_209128 : Nat := 95451717612056017278439

theorem tailTrace_209128 : CollatzResearch.WordTrace tailWord_209128 prefixEnd_209128 95451717612056017278439 := by
  unfold tailWord_209128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813762393186223531998019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5085016524248298042664025 3813762393186223531998019)
  ·
    refine ⟨5720643589779335297997029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813762393186223531998019 5720643589779335297997029)
    ·
      refine ⟨1072620673083625368374443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5720643589779335297997029 1072620673083625368374443)
      ·
        refine ⟨1608931009625438052561665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072620673083625368374443 1608931009625438052561665)
        ·
          refine ⟨1206698257219078539421249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608931009625438052561665 1206698257219078539421249)
          ·
            refine ⟨905023692914308904565937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206698257219078539421249 905023692914308904565937)
            ·
              refine ⟨678767769685731678424453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905023692914308904565937 678767769685731678424453)
              ·
                refine ⟨127268956816074689704585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678767769685731678424453 127268956816074689704585)
                ·
                  refine ⟨95451717612056017278439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127268956816074689704585 95451717612056017278439)
                  ·
                    rfl

theorem cell20_209128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_209128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209128 prefixEnd_209128 := by exact prefixLift 209128
  have htrace : WordTrace (prefixWord ++ tailWord_209128) baseStart_209128 baseEnd_209128 := by
    simpa [prefixWord, tailWord_209128, baseEnd_209128] using wordTrace_append hprefix tailTrace_209128
  have hstable : (prefixWord ++ tailWord_209128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209128).length < 2 ^ (prefixWord ++ tailWord_209128).sum := by decide
  have hdescent : baseEnd_209128 < baseStart_209128 := by decide
  rcases family_descends (prefixWord ++ tailWord_209128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209139 : List Nat := [1, 1, 1, 2, 2, 4, 2, 7]
def baseStart_209139 : Nat := 118140960795 + 209139 * 2 ^ 59
def prefixEnd_209139 : Nat := 4983230072969 + 3 ^ 40 * 209139 * 2
def baseEnd_209139 : Nat := 31818912770596289303909

theorem tailTrace_209139 : CollatzResearch.WordTrace tailWord_209139 prefixEnd_209139 31818912770596289303909 := by
  unfold tailWord_209139
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627925989332595942646471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5085283992888397295097647 7627925989332595942646471)
  ·
    refine ⟨11441888983998893913969707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7627925989332595942646471 11441888983998893913969707)
    ·
      refine ⟨17162833475998340870954561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441888983998893913969707 17162833475998340870954561)
      ·
        refine ⟨12872125106998755653215921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17162833475998340870954561 12872125106998755653215921)
        ·
          refine ⟨9654093830249066739911941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12872125106998755653215921 9654093830249066739911941)
          ·
            refine ⟨1810142593171700013733489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9654093830249066739911941 1810142593171700013733489)
            ·
              refine ⟨1357606944878775010300117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810142593171700013733489 1357606944878775010300117)
              ·
                refine ⟨31818912770596289303909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1357606944878775010300117 31818912770596289303909)
                ·
                  rfl

theorem cell20_209139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_209139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209139 prefixEnd_209139 := by exact prefixLift 209139
  have htrace : WordTrace (prefixWord ++ tailWord_209139) baseStart_209139 baseEnd_209139 := by
    simpa [prefixWord, tailWord_209139, baseEnd_209139] using wordTrace_append hprefix tailTrace_209139
  have hstable : (prefixWord ++ tailWord_209139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209139).length < 2 ^ (prefixWord ++ tailWord_209139).sum := by decide
  have hdescent : baseEnd_209139 < baseStart_209139 := by decide
  rcases family_descends (prefixWord ++ tailWord_209139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209142 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_209142 : Nat := 118140960795 + 209142 * 2 ^ 59
def prefixEnd_209142 : Nat := 4983230072969 + 3 ^ 40 * 209142 * 2
def baseEnd_209142 : Nat := 95458107593534190811715

theorem tailTrace_209142 : CollatzResearch.WordTrace tailWord_209142 prefixEnd_209142 95458107593534190811715 := by
  unfold tailWord_209142
  simp only [CollatzResearch.WordTrace]
  refine ⟨476752213020107965937855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5085356938881151636670453 476752213020107965937855)
  ·
    refine ⟨715128319530161948906783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476752213020107965937855 715128319530161948906783)
    ·
      refine ⟨1072692479295242923360175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715128319530161948906783 1072692479295242923360175)
      ·
        refine ⟨1609038718942864385040263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072692479295242923360175 1609038718942864385040263)
        ·
          refine ⟨2413558078414296577560395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609038718942864385040263 2413558078414296577560395)
          ·
            refine ⟨3620337117621444866340593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413558078414296577560395 3620337117621444866340593)
            ·
              refine ⟨2715252838216083649755445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3620337117621444866340593 2715252838216083649755445)
              ·
                refine ⟨254554953582757842164573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2715252838216083649755445 254554953582757842164573)
                ·
                  refine ⟨95458107593534190811715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254554953582757842164573 95458107593534190811715)
                  ·
                    rfl

theorem cell20_209142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_209142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209142 prefixEnd_209142 := by exact prefixLift 209142
  have htrace : WordTrace (prefixWord ++ tailWord_209142) baseStart_209142 baseEnd_209142 := by
    simpa [prefixWord, tailWord_209142, baseEnd_209142] using wordTrace_append hprefix tailTrace_209142
  have hstable : (prefixWord ++ tailWord_209142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209142).length < 2 ^ (prefixWord ++ tailWord_209142).sum := by decide
  have hdescent : baseEnd_209142 < baseStart_209142 := by decide
  rcases family_descends (prefixWord ++ tailWord_209142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209183 : List Nat := [1, 1, 2, 4, 3, 2, 3, 2, 2]
def baseStart_209183 : Nat := 118140960795 + 209183 * 2 ^ 59
def prefixEnd_209183 : Nat := 4983230072969 + 3 ^ 40 * 209183 * 2
def baseEnd_209183 : Nat := 95476821110720270444881

theorem tailTrace_209183 : CollatzResearch.WordTrace tailWord_209183 prefixEnd_209183 95476821110720270444881 := by
  unfold tailWord_209183
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629530801173191457248203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5086353867448794304832135 7629530801173191457248203)
  ·
    refine ⟨11444296201759787185872305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629530801173191457248203 11444296201759787185872305)
    ·
      refine ⟨8583222151319840389404229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11444296201759787185872305 8583222151319840389404229)
      ·
        refine ⟨1609354153372470073013293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8583222151319840389404229 1609354153372470073013293)
        ·
          refine ⟨603507807514676277379985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1609354153372470073013293 603507807514676277379985)
          ·
            refine ⟨452630855636007208034989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603507807514676277379985 452630855636007208034989)
            ·
              refine ⟨169736570863502703013121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452630855636007208034989 169736570863502703013121)
              ·
                refine ⟨127302428147627027259841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169736570863502703013121 127302428147627027259841)
                ·
                  refine ⟨95476821110720270444881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127302428147627027259841 95476821110720270444881)
                  ·
                    rfl

theorem cell20_209183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 2].length) (baseStart_209183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209183 prefixEnd_209183 := by exact prefixLift 209183
  have htrace : WordTrace (prefixWord ++ tailWord_209183) baseStart_209183 baseEnd_209183 := by
    simpa [prefixWord, tailWord_209183, baseEnd_209183] using wordTrace_append hprefix tailTrace_209183
  have hstable : (prefixWord ++ tailWord_209183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209183).length < 2 ^ (prefixWord ++ tailWord_209183).sum := by decide
  have hdescent : baseEnd_209183 < baseStart_209183 := by decide
  rcases family_descends (prefixWord ++ tailWord_209183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209208 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_209208 : Nat := 118140960795 + 209208 * 2 ^ 59
def prefixEnd_209208 : Nat := 4983230072969 + 3 ^ 40 * 209208 * 2
def baseEnd_209208 : Nat := 95488231791931294611445

theorem tailTrace_209208 : CollatzResearch.WordTrace tailWord_209208 prefixEnd_209208 95488231791931294611445 := by
  unfold tailWord_209208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815221313041310363454139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5086961750721747151272185 3815221313041310363454139)
  ·
    refine ⟨5722831969561965545181209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3815221313041310363454139 5722831969561965545181209)
    ·
      refine ⟨4292123977171474158885907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5722831969561965545181209 4292123977171474158885907)
      ·
        refine ⟨6438185965757211238328861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4292123977171474158885907 6438185965757211238328861)
        ·
          refine ⟨2414319737158954214373323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6438185965757211238328861 2414319737158954214373323)
          ·
            refine ⟨3621479605738431321559985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414319737158954214373323 3621479605738431321559985)
            ·
              refine ⟨2716109704303823491169989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621479605738431321559985 2716109704303823491169989)
              ·
                refine ⟨509270569556966904594373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2716109704303823491169989 509270569556966904594373)
                ·
                  refine ⟨95488231791931294611445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509270569556966904594373 95488231791931294611445)
                  ·
                    rfl

theorem cell20_209208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_209208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209208 prefixEnd_209208 := by exact prefixLift 209208
  have htrace : WordTrace (prefixWord ++ tailWord_209208) baseStart_209208 baseEnd_209208 := by
    simpa [prefixWord, tailWord_209208, baseEnd_209208] using wordTrace_append hprefix tailTrace_209208
  have hstable : (prefixWord ++ tailWord_209208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209208).length < 2 ^ (prefixWord ++ tailWord_209208).sum := by decide
  have hdescent : baseEnd_209208 < baseStart_209208 := by decide
  rcases family_descends (prefixWord ++ tailWord_209208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209215 : List Nat := [1, 1, 2, 2, 4, 1, 1, 8]
def baseStart_209215 : Nat := 118140960795 + 209215 * 2 ^ 59
def prefixEnd_209215 : Nat := 4983230072969 + 3 ^ 40 * 209215 * 2
def baseEnd_209215 : Nat := 31830475594223460459361

theorem tailTrace_209215 : CollatzResearch.WordTrace tailWord_209215 prefixEnd_209215 31830475594223460459361 := by
  unfold tailWord_209215
  simp only [CollatzResearch.WordTrace]
  refine ⟨7630697937057260922413099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5087131958038173948275399 7630697937057260922413099)
  ·
    refine ⟨11446046905585891383619649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7630697937057260922413099 11446046905585891383619649)
    ·
      refine ⟨8584535179189418537714737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11446046905585891383619649 8584535179189418537714737)
      ·
        refine ⟨6438401384392063903286053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8584535179189418537714737 6438401384392063903286053)
        ·
          refine ⟨1207200259573511981866135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6438401384392063903286053 1207200259573511981866135)
          ·
            refine ⟨1810800389360267972799203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207200259573511981866135 1810800389360267972799203)
            ·
              refine ⟨2716200584040401959198805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810800389360267972799203 2716200584040401959198805)
              ·
                refine ⟨31830475594223460459361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2716200584040401959198805 31830475594223460459361)
                ·
                  rfl

theorem cell20_209215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_209215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209215 prefixEnd_209215 := by exact prefixLift 209215
  have htrace : WordTrace (prefixWord ++ tailWord_209215) baseStart_209215 baseEnd_209215 := by
    simpa [prefixWord, tailWord_209215, baseEnd_209215] using wordTrace_append hprefix tailTrace_209215
  have hstable : (prefixWord ++ tailWord_209215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209215).length < 2 ^ (prefixWord ++ tailWord_209215).sum := by decide
  have hdescent : baseEnd_209215 < baseStart_209215 := by decide
  rcases family_descends (prefixWord ++ tailWord_209215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209225 : List Nat := [1, 2, 1, 1, 2, 3, 1, 7, 2]
def baseStart_209225 : Nat := 118140960795 + 209225 * 2 ^ 59
def prefixEnd_209225 : Nat := 4983230072969 + 3 ^ 40 * 209225 * 2
def baseEnd_209225 : Nat := 95495991055154791044709

theorem tailTrace_209225 : CollatzResearch.WordTrace tailWord_209225 prefixEnd_209225 95495991055154791044709 := by
  unfold tailWord_209225
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631062667021032630277129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5087375111347355086851419 7631062667021032630277129)
  ·
    refine ⟨5723297000265774472707847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7631062667021032630277129 5723297000265774472707847)
    ·
      refine ⟨8584945500398661709061771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5723297000265774472707847 8584945500398661709061771)
      ·
        refine ⟨12877418250597992563592657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584945500398661709061771 12877418250597992563592657)
        ·
          refine ⟨9658063687948494422694493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12877418250597992563592657 9658063687948494422694493)
          ·
            refine ⟨3621773882980685408510435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9658063687948494422694493 3621773882980685408510435)
            ·
              refine ⟨5432660824471028112765653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621773882980685408510435 5432660824471028112765653)
              ·
                refine ⟨127327988073539721392945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5432660824471028112765653 127327988073539721392945)
                ·
                  refine ⟨95495991055154791044709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127327988073539721392945 95495991055154791044709)
                  ·
                    rfl

theorem cell20_209225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_209225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209225 prefixEnd_209225 := by exact prefixLift 209225
  have htrace : WordTrace (prefixWord ++ tailWord_209225) baseStart_209225 baseEnd_209225 := by
    simpa [prefixWord, tailWord_209225, baseEnd_209225] using wordTrace_append hprefix tailTrace_209225
  have hstable : (prefixWord ++ tailWord_209225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209225).length < 2 ^ (prefixWord ++ tailWord_209225).sum := by decide
  have hdescent : baseEnd_209225 < baseStart_209225 := by decide
  rcases family_descends (prefixWord ++ tailWord_209225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209256 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_209256 : Nat := 118140960795 + 209256 * 2 ^ 59
def prefixEnd_209256 : Nat := 4983230072969 + 3 ^ 40 * 209256 * 2
def baseEnd_209256 : Nat := 95510140299856461011249

theorem tailTrace_209256 : CollatzResearch.WordTrace tailWord_209256 prefixEnd_209256 95510140299856461011249 := by
  unfold tailWord_209256
  simp only [CollatzResearch.WordTrace]
  refine ⟨3816096664954362462327811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5088128886605816616437081 3816096664954362462327811)
  ·
    refine ⟨5724144997431543693491717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3816096664954362462327811 5724144997431543693491717)
    ·
      refine ⟨1073277187018414442529697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5724144997431543693491717 1073277187018414442529697)
      ·
        refine ⟨804957890263810831897273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1073277187018414442529697 804957890263810831897273)
        ·
          refine ⟨603718417697858123922955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804957890263810831897273 603718417697858123922955)
          ·
            refine ⟨905577626546787185884433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603718417697858123922955 905577626546787185884433)
            ·
              refine ⟨679183219910090389413325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905577626546787185884433 679183219910090389413325)
              ·
                refine ⟨254693707466283896029997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679183219910090389413325 254693707466283896029997)
                ·
                  refine ⟨95510140299856461011249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254693707466283896029997 95510140299856461011249)
                  ·
                    rfl

theorem cell20_209256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_209256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209256 prefixEnd_209256 := by exact prefixLift 209256
  have htrace : WordTrace (prefixWord ++ tailWord_209256) baseStart_209256 baseEnd_209256 := by
    simpa [prefixWord, tailWord_209256, baseEnd_209256] using wordTrace_append hprefix tailTrace_209256
  have hstable : (prefixWord ++ tailWord_209256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209256).length < 2 ^ (prefixWord ++ tailWord_209256).sum := by decide
  have hdescent : baseEnd_209256 < baseStart_209256 := by decide
  rcases family_descends (prefixWord ++ tailWord_209256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209284 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_209284 : Nat := 118140960795 + 209284 * 2 ^ 59
def prefixEnd_209284 : Nat := 4983230072969 + 3 ^ 40 * 209284 * 2
def baseEnd_209284 : Nat := 95522920262812808077801

theorem tailTrace_209284 : CollatzResearch.WordTrace tailWord_209284 prefixEnd_209284 95522920262812808077801 := by
  unfold tailWord_209284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3816607286903642853337453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5088809715871523804449937 3816607286903642853337453)
  ·
    refine ⟨1431227732588866070001545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3816607286903642853337453 1431227732588866070001545)
    ·
      refine ⟨1073420799441649552501159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1431227732588866070001545 1073420799441649552501159)
      ·
        refine ⟨1610131199162474328751739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073420799441649552501159 1610131199162474328751739)
        ·
          refine ⟨2415196798743711493127609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610131199162474328751739 2415196798743711493127609)
          ·
            refine ⟨1811397599057783619845707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415196798743711493127609 1811397599057783619845707)
            ·
              refine ⟨2717096398586675429768561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811397599057783619845707 2717096398586675429768561)
              ·
                refine ⟨2037822298940006572326421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717096398586675429768561 2037822298940006572326421)
                ·
                  refine ⟨95522920262812808077801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2037822298940006572326421 95522920262812808077801)
                  ·
                    rfl

theorem cell20_209284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_209284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209284 prefixEnd_209284 := by exact prefixLift 209284
  have htrace : WordTrace (prefixWord ++ tailWord_209284) baseStart_209284 baseEnd_209284 := by
    simpa [prefixWord, tailWord_209284, baseEnd_209284] using wordTrace_append hprefix tailTrace_209284
  have hstable : (prefixWord ++ tailWord_209284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209284).length < 2 ^ (prefixWord ++ tailWord_209284).sum := by decide
  have hdescent : baseEnd_209284 < baseStart_209284 := by decide
  rcases family_descends (prefixWord ++ tailWord_209284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209290 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_209290 : Nat := 118140960795 + 209290 * 2 ^ 59
def prefixEnd_209290 : Nat := 4983230072969 + 3 ^ 40 * 209290 * 2
def baseEnd_209290 : Nat := 95525658826303453877777

theorem tailTrace_209290 : CollatzResearch.WordTrace tailWord_209290 prefixEnd_209290 95525658826303453877777 := by
  unfold tailWord_209290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908358352946387182848331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5088955607857032487595549 1908358352946387182848331)
  ·
    refine ⟨2862537529419580774272497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908358352946387182848331 2862537529419580774272497)
    ·
      refine ⟨2146903147064685580704373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2862537529419580774272497 2146903147064685580704373)
      ·
        refine ⟨201272170037314273191035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2146903147064685580704373 201272170037314273191035)
        ·
          refine ⟨301908255055971409786553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201272170037314273191035 301908255055971409786553)
          ·
            refine ⟨226431191291978557339915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301908255055971409786553 226431191291978557339915)
            ·
              refine ⟨339646786937967836009873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226431191291978557339915 339646786937967836009873)
              ·
                refine ⟨254735090203475877007405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339646786937967836009873 254735090203475877007405)
                ·
                  refine ⟨95525658826303453877777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254735090203475877007405 95525658826303453877777)
                  ·
                    rfl

theorem cell20_209290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_209290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209290 prefixEnd_209290 := by exact prefixLift 209290
  have htrace : WordTrace (prefixWord ++ tailWord_209290) baseStart_209290 baseEnd_209290 := by
    simpa [prefixWord, tailWord_209290, baseEnd_209290] using wordTrace_append hprefix tailTrace_209290
  have hstable : (prefixWord ++ tailWord_209290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209290).length < 2 ^ (prefixWord ++ tailWord_209290).sum := by decide
  have hdescent : baseEnd_209290 < baseStart_209290 := by decide
  rcases family_descends (prefixWord ++ tailWord_209290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209291 : List Nat := [1, 1, 1, 1, 4, 5, 7]
def baseStart_209291 : Nat := 118140960795 + 209291 * 2 ^ 59
def prefixEnd_209291 : Nat := 4983230072969 + 3 ^ 40 * 209291 * 2
def baseEnd_209291 : Nat := 10614012805950210538271

theorem tailTrace_209291 : CollatzResearch.WordTrace tailWord_209291 prefixEnd_209291 10614012805950210538271 := by
  unfold tailWord_209291
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633469884781925902179727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5088979923187950601453151 7633469884781925902179727)
  ·
    refine ⟨11450204827172888853269591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7633469884781925902179727 11450204827172888853269591)
    ·
      refine ⟨17175307240759333279904387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11450204827172888853269591 17175307240759333279904387)
      ·
        refine ⟨25762960861138999919856581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17175307240759333279904387 25762960861138999919856581)
        ·
          refine ⟨4830555161463562484973109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25762960861138999919856581 4830555161463562484973109)
          ·
            refine ⟨452864546387208982966229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4830555161463562484973109 452864546387208982966229)
            ·
              refine ⟨10614012805950210538271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 452864546387208982966229 10614012805950210538271)
              ·
                rfl

theorem cell20_209291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_209291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209291 prefixEnd_209291 := by exact prefixLift 209291
  have htrace : WordTrace (prefixWord ++ tailWord_209291) baseStart_209291 baseEnd_209291 := by
    simpa [prefixWord, tailWord_209291, baseEnd_209291] using wordTrace_append hprefix tailTrace_209291
  have hstable : (prefixWord ++ tailWord_209291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209291).length < 2 ^ (prefixWord ++ tailWord_209291).sum := by decide
  have hdescent : baseEnd_209291 < baseStart_209291 := by decide
  rcases family_descends (prefixWord ++ tailWord_209291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209294 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_209294 : Nat := 118140960795 + 209294 * 2 ^ 59
def prefixEnd_209294 : Nat := 4983230072969 + 3 ^ 40 * 209294 * 2
def baseEnd_209294 : Nat := 95527484535297217744427

theorem tailTrace_209294 : CollatzResearch.WordTrace tailWord_209294 prefixEnd_209294 95527484535297217744427 := by
  unfold tailWord_209294
  simp only [CollatzResearch.WordTrace]
  refine ⟨954197412971382176817367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5089052869180704943025957 954197412971382176817367)
  ·
    refine ⟨1431296119457073265226051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954197412971382176817367 1431296119457073265226051)
    ·
      refine ⟨2146944179185609897839077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431296119457073265226051 2146944179185609897839077)
      ·
        refine ⟨402552033597301855844827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2146944179185609897839077 402552033597301855844827)
        ·
          refine ⟨603828050395952783767241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402552033597301855844827 603828050395952783767241)
          ·
            refine ⟨452871037796964587825431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603828050395952783767241 452871037796964587825431)
            ·
              refine ⟨679306556695446881738147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452871037796964587825431 679306556695446881738147)
              ·
                refine ⟨1018959835043170322607221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679306556695446881738147 1018959835043170322607221)
                ·
                  refine ⟨95527484535297217744427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1018959835043170322607221 95527484535297217744427)
                  ·
                    rfl

theorem cell20_209294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_209294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209294 prefixEnd_209294 := by exact prefixLift 209294
  have htrace : WordTrace (prefixWord ++ tailWord_209294) baseStart_209294 baseEnd_209294 := by
    simpa [prefixWord, tailWord_209294, baseEnd_209294] using wordTrace_append hprefix tailTrace_209294
  have hstable : (prefixWord ++ tailWord_209294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209294).length < 2 ^ (prefixWord ++ tailWord_209294).sum := by decide
  have hdescent : baseEnd_209294 < baseStart_209294 := by decide
  rcases family_descends (prefixWord ++ tailWord_209294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209325 : List Nat := [1, 5, 2, 2, 2, 1, 1, 6]
def baseStart_209325 : Nat := 118140960795 + 209325 * 2 ^ 59
def prefixEnd_209325 : Nat := 4983230072969 + 3 ^ 40 * 209325 * 2
def baseEnd_209325 : Nat := 31847211259999629236989

theorem tailTrace_209325 : CollatzResearch.WordTrace tailWord_209325 prefixEnd_209325 31847211259999629236989 := by
  unfold tailWord_209325
  simp only [CollatzResearch.WordTrace]
  refine ⟨7634709966658749708917429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5089806644439166472611619 7634709966658749708917429)
  ·
    refine ⟨715754059374257785211009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7634709966658749708917429 715754059374257785211009)
    ·
      refine ⟨536815544530693338908257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 715754059374257785211009 536815544530693338908257)
      ·
        refine ⟨402611658398020004181193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536815544530693338908257 402611658398020004181193)
        ·
          refine ⟨301958743798515003135895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402611658398020004181193 301958743798515003135895)
          ·
            refine ⟨452938115697772504703843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301958743798515003135895 452938115697772504703843)
            ·
              refine ⟨679407173546658757055765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452938115697772504703843 679407173546658757055765)
              ·
                refine ⟨31847211259999629236989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 679407173546658757055765 31847211259999629236989)
                ·
                  rfl

theorem cell20_209325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_209325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209325 prefixEnd_209325 := by exact prefixLift 209325
  have htrace : WordTrace (prefixWord ++ tailWord_209325) baseStart_209325 baseEnd_209325 := by
    simpa [prefixWord, tailWord_209325, baseEnd_209325] using wordTrace_append hprefix tailTrace_209325
  have hstable : (prefixWord ++ tailWord_209325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209325).length < 2 ^ (prefixWord ++ tailWord_209325).sum := by decide
  have hdescent : baseEnd_209325 < baseStart_209325 := by decide
  rcases family_descends (prefixWord ++ tailWord_209325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209356 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_209356 : Nat := 118140960795 + 209356 * 2 ^ 59
def prefixEnd_209356 : Nat := 4983230072969 + 3 ^ 40 * 209356 * 2
def baseEnd_209356 : Nat := 95555783024700557677507

theorem tailTrace_209356 : CollatzResearch.WordTrace tailWord_209356 prefixEnd_209356 95555783024700557677507 := by
  unfold tailWord_209356
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817920314773221001647961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5090560419697628002197281 3817920314773221001647961)
  ·
    refine ⟨2863440236079915751235971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3817920314773221001647961 2863440236079915751235971)
    ·
      refine ⟨4295160354119873626853957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863440236079915751235971 4295160354119873626853957)
      ·
        refine ⟨805342566397476305035117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4295160354119873626853957 805342566397476305035117)
        ·
          refine ⟨302003462399053614388169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 805342566397476305035117 302003462399053614388169)
          ·
            refine ⟨226502596799290210791127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302003462399053614388169 226502596799290210791127)
            ·
              refine ⟨339753895198935316186691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226502596799290210791127 339753895198935316186691)
              ·
                refine ⟨509630842798402974280037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339753895198935316186691 509630842798402974280037)
                ·
                  refine ⟨95555783024700557677507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509630842798402974280037 95555783024700557677507)
                  ·
                    rfl

theorem cell20_209356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_209356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209356 prefixEnd_209356 := by exact prefixLift 209356
  have htrace : WordTrace (prefixWord ++ tailWord_209356) baseStart_209356 baseEnd_209356 := by
    simpa [prefixWord, tailWord_209356, baseEnd_209356] using wordTrace_append hprefix tailTrace_209356
  have hstable : (prefixWord ++ tailWord_209356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209356).length < 2 ^ (prefixWord ++ tailWord_209356).sum := by decide
  have hdescent : baseEnd_209356 < baseStart_209356 := by decide
  rcases family_descends (prefixWord ++ tailWord_209356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209422 : List Nat := [4, 1, 1, 2, 3, 1, 3, 5]
def baseStart_209422 : Nat := 118140960795 + 209422 * 2 ^ 59
def prefixEnd_209422 : Nat := 4983230072969 + 3 ^ 40 * 209422 * 2
def baseEnd_209422 : Nat := 31861969074365887159079

theorem tailTrace_209422 : CollatzResearch.WordTrace tailWord_209422 prefixEnd_209422 31861969074365887159079 := by
  unfold tailWord_209422
  simp only [CollatzResearch.WordTrace]
  refine ⟨954780980913416909399815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5092165231538223516799013 954780980913416909399815)
  ·
    refine ⟨1432171471370125364099723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954780980913416909399815 1432171471370125364099723)
    ·
      refine ⟨2148257207055188046149585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432171471370125364099723 2148257207055188046149585)
      ·
        refine ⟨1611192905291391034612189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2148257207055188046149585 1611192905291391034612189)
        ·
          refine ⟨604197339484271637979571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1611192905291391034612189 604197339484271637979571)
          ·
            refine ⟨906296009226407456969357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604197339484271637979571 906296009226407456969357)
            ·
              refine ⟨339861003459902796363509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 906296009226407456969357 339861003459902796363509)
              ·
                refine ⟨31861969074365887159079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339861003459902796363509 31861969074365887159079)
                ·
                  rfl

theorem cell20_209422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_209422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209422 prefixEnd_209422 := by exact prefixLift 209422
  have htrace : WordTrace (prefixWord ++ tailWord_209422) baseStart_209422 baseEnd_209422 := by
    simpa [prefixWord, tailWord_209422, baseEnd_209422] using wordTrace_append hprefix tailTrace_209422
  have hstable : (prefixWord ++ tailWord_209422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209422).length < 2 ^ (prefixWord ++ tailWord_209422).sum := by decide
  have hdescent : baseEnd_209422 < baseStart_209422 := by decide
  rcases family_descends (prefixWord ++ tailWord_209422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209429 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 3]
def baseStart_209429 : Nat := 118140960795 + 209429 * 2 ^ 59
def prefixEnd_209429 : Nat := 4983230072969 + 3 ^ 40 * 209429 * 2
def baseEnd_209429 : Nat := 95589102213836748243875

theorem tailTrace_209429 : CollatzResearch.WordTrace tailWord_209429 prefixEnd_209429 95589102213836748243875 := by
  unfold tailWord_209429
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638503158281975470703341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5092335438854650313802227 7638503158281975470703341)
  ·
    refine ⟨2864438684355740801513753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7638503158281975470703341 2864438684355740801513753)
    ·
      refine ⟨2148329013266805601135315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2864438684355740801513753 2148329013266805601135315)
      ·
        refine ⟨3222493519900208401702973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148329013266805601135315 3222493519900208401702973)
        ·
          refine ⟨1208435069962578150638615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3222493519900208401702973 1208435069962578150638615)
          ·
            refine ⟨1812652604943867225957923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208435069962578150638615 1812652604943867225957923)
            ·
              refine ⟨2718978907415800838936885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812652604943867225957923 2718978907415800838936885)
              ·
                refine ⟨254904272570231328650333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2718978907415800838936885 254904272570231328650333)
                ·
                  refine ⟨95589102213836748243875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254904272570231328650333 95589102213836748243875)
                  ·
                    rfl

theorem cell20_209429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_209429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209429 prefixEnd_209429 := by exact prefixLift 209429
  have htrace : WordTrace (prefixWord ++ tailWord_209429) baseStart_209429 baseEnd_209429 := by
    simpa [prefixWord, tailWord_209429, baseEnd_209429] using wordTrace_append hprefix tailTrace_209429
  have hstable : (prefixWord ++ tailWord_209429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209429).length < 2 ^ (prefixWord ++ tailWord_209429).sum := by decide
  have hdescent : baseEnd_209429 < baseStart_209429 := by decide
  rcases family_descends (prefixWord ++ tailWord_209429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209436 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_209436 : Nat := 118140960795 + 209436 * 2 ^ 59
def prefixEnd_209436 : Nat := 4983230072969 + 3 ^ 40 * 209436 * 2
def baseEnd_209436 : Nat := 95592297204575835010513

theorem tailTrace_209436 : CollatzResearch.WordTrace tailWord_209436 prefixEnd_209436 95592297204575835010513 := by
  unfold tailWord_209436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3819379234628307833104081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5092505646171077110805441 3819379234628307833104081)
  ·
    refine ⟨2864534425971230874828061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3819379234628307833104081 2864534425971230874828061)
    ·
      refine ⟨1074200409739211578060523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2864534425971230874828061 1074200409739211578060523)
      ·
        refine ⟨1611300614608817367090785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074200409739211578060523 1611300614608817367090785)
        ·
          refine ⟨1208475460956613025318089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1611300614608817367090785 1208475460956613025318089)
          ·
            refine ⟨906356595717459768988567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208475460956613025318089 906356595717459768988567)
            ·
              refine ⟨1359534893576189653482851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906356595717459768988567 1359534893576189653482851)
              ·
                refine ⟨2039302340364284480224277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359534893576189653482851 2039302340364284480224277)
                ·
                  refine ⟨95592297204575835010513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2039302340364284480224277 95592297204575835010513)
                  ·
                    rfl

theorem cell20_209436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_209436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209436 prefixEnd_209436 := by exact prefixLift 209436
  have htrace : WordTrace (prefixWord ++ tailWord_209436) baseStart_209436 baseEnd_209436 := by
    simpa [prefixWord, tailWord_209436, baseEnd_209436] using wordTrace_append hprefix tailTrace_209436
  have hstable : (prefixWord ++ tailWord_209436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209436).length < 2 ^ (prefixWord ++ tailWord_209436).sum := by decide
  have hdescent : baseEnd_209436 < baseStart_209436 := by decide
  rcases family_descends (prefixWord ++ tailWord_209436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209484 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_209484 : Nat := 118140960795 + 209484 * 2 ^ 59
def prefixEnd_209484 : Nat := 4983230072969 + 3 ^ 40 * 209484 * 2
def baseEnd_209484 : Nat := 95614205712501001410317

theorem tailTrace_209484 : CollatzResearch.WordTrace tailWord_209484 prefixEnd_209484 95614205712501001410317 := by
  unfold tailWord_209484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820254586541359931977753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5093672782055146575970337 3820254586541359931977753)
  ·
    refine ⟨2865190939906019948983315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3820254586541359931977753 2865190939906019948983315)
    ·
      refine ⟨4297786409859029923474973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865190939906019948983315 4297786409859029923474973)
      ·
        refine ⟨1611669903697136221303115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4297786409859029923474973 1611669903697136221303115)
        ·
          refine ⟨2417504855545704331954673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611669903697136221303115 2417504855545704331954673)
          ·
            refine ⟨1813128641659278248966005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417504855545704331954673 1813128641659278248966005)
            ·
              refine ⟨169980810155557335840563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1813128641659278248966005 169980810155557335840563)
              ·
                refine ⟨254971215233336003760845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169980810155557335840563 254971215233336003760845)
                ·
                  refine ⟨95614205712501001410317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254971215233336003760845 95614205712501001410317)
                  ·
                    rfl

theorem cell20_209484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_209484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209484 prefixEnd_209484 := by exact prefixLift 209484
  have htrace : WordTrace (prefixWord ++ tailWord_209484) baseStart_209484 baseEnd_209484 := by
    simpa [prefixWord, tailWord_209484, baseEnd_209484] using wordTrace_append hprefix tailTrace_209484
  have hstable : (prefixWord ++ tailWord_209484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209484).length < 2 ^ (prefixWord ++ tailWord_209484).sum := by decide
  have hdescent : baseEnd_209484 < baseStart_209484 := by decide
  rcases family_descends (prefixWord ++ tailWord_209484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209525 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 4]
def baseStart_209525 : Nat := 118140960795 + 209525 * 2 ^ 59
def prefixEnd_209525 : Nat := 4983230072969 + 3 ^ 40 * 209525 * 2
def baseEnd_209525 : Nat := 95632919229687081043483

theorem tailTrace_209525 : CollatzResearch.WordTrace tailWord_209525 prefixEnd_209525 95632919229687081043483 := by
  unfold tailWord_209525
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642004565934183866198029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5094669710622789244132019 7642004565934183866198029)
  ·
    refine ⟨2865751712225318949824261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7642004565934183866198029 2865751712225318949824261)
    ·
      refine ⟨537328446042247303092049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2865751712225318949824261 537328446042247303092049)
      ·
        refine ⟨402996334531685477319037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537328446042247303092049 402996334531685477319037)
        ·
          refine ⟨151123625449382053994639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402996334531685477319037 151123625449382053994639)
          ·
            refine ⟨226685438174073080991959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151123625449382053994639 226685438174073080991959)
            ·
              refine ⟨340028157261109621487939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226685438174073080991959 340028157261109621487939)
              ·
                refine ⟨510042235891664432231909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340028157261109621487939 510042235891664432231909)
                ·
                  refine ⟨95632919229687081043483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510042235891664432231909 95632919229687081043483)
                  ·
                    rfl

theorem cell20_209525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_209525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209525 prefixEnd_209525 := by exact prefixLift 209525
  have htrace : WordTrace (prefixWord ++ tailWord_209525) baseStart_209525 baseEnd_209525 := by
    simpa [prefixWord, tailWord_209525, baseEnd_209525] using wordTrace_append hprefix tailTrace_209525
  have hstable : (prefixWord ++ tailWord_209525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209525).length < 2 ^ (prefixWord ++ tailWord_209525).sum := by decide
  have hdescent : baseEnd_209525 < baseStart_209525 := by decide
  rcases family_descends (prefixWord ++ tailWord_209525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209529 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 4]
def baseStart_209529 : Nat := 118140960795 + 209529 * 2 ^ 59
def prefixEnd_209529 : Nat := 4983230072969 + 3 ^ 40 * 209529 * 2
def baseEnd_209529 : Nat := 95634744938680844910133

theorem tailTrace_209529 : CollatzResearch.WordTrace tailWord_209529 prefixEnd_209529 95634744938680844910133 := by
  unfold tailWord_209529
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642150457919692549343641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5094766971946461699562427 7642150457919692549343641)
  ·
    refine ⟨5731612843439769412007731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7642150457919692549343641 5731612843439769412007731)
    ·
      refine ⟨8597419265159654118011597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731612843439769412007731 8597419265159654118011597)
      ·
        refine ⟨3224032224434870294254349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8597419265159654118011597 3224032224434870294254349)
        ·
          refine ⟨1209012084163076360345381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3224032224434870294254349 1209012084163076360345381)
          ·
            refine ⟨226689765780576817564759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1209012084163076360345381 226689765780576817564759)
            ·
              refine ⟨340034648670865226347139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226689765780576817564759 340034648670865226347139)
              ·
                refine ⟨510051973006297839520709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340034648670865226347139 510051973006297839520709)
                ·
                  refine ⟨95634744938680844910133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510051973006297839520709 95634744938680844910133)
                  ·
                    rfl

theorem cell20_209529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_209529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209529 prefixEnd_209529 := by exact prefixLift 209529
  have htrace : WordTrace (prefixWord ++ tailWord_209529) baseStart_209529 baseEnd_209529 := by
    simpa [prefixWord, tailWord_209529, baseEnd_209529] using wordTrace_append hprefix tailTrace_209529
  have hstable : (prefixWord ++ tailWord_209529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209529).length < 2 ^ (prefixWord ++ tailWord_209529).sum := by decide
  have hdescent : baseEnd_209529 < baseStart_209529 := by decide
  rcases family_descends (prefixWord ++ tailWord_209529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209543 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 3]
def baseStart_209543 : Nat := 118140960795 + 209543 * 2 ^ 59
def prefixEnd_209543 : Nat := 4983230072969 + 3 ^ 40 * 209543 * 2
def baseEnd_209543 : Nat := 95641134920159018443409

theorem tailTrace_209543 : CollatzResearch.WordTrace tailWord_209543 prefixEnd_209543 95641134920159018443409 := by
  unfold tailWord_209543
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642661079868972940353283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5095107386579315293568855 7642661079868972940353283)
  ·
    refine ⟨11463991619803459410529925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7642661079868972940353283 11463991619803459410529925)
    ·
      refine ⟨2149498428713148639474361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11463991619803459410529925 2149498428713148639474361)
      ·
        refine ⟨1612123821534861479605771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2149498428713148639474361 1612123821534861479605771)
        ·
          refine ⟨2418185732302292219408657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612123821534861479605771 2418185732302292219408657)
          ·
            refine ⟨1813639299226719164556493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2418185732302292219408657 1813639299226719164556493)
            ·
              refine ⟨680114737210019686708685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1813639299226719164556493 680114737210019686708685)
              ·
                refine ⟨255043026453757382515757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680114737210019686708685 255043026453757382515757)
                ·
                  refine ⟨95641134920159018443409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255043026453757382515757 95641134920159018443409)
                  ·
                    rfl

theorem cell20_209543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_209543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209543 prefixEnd_209543 := by exact prefixLift 209543
  have htrace : WordTrace (prefixWord ++ tailWord_209543) baseStart_209543 baseEnd_209543 := by
    simpa [prefixWord, tailWord_209543, baseEnd_209543] using wordTrace_append hprefix tailTrace_209543
  have hstable : (prefixWord ++ tailWord_209543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209543).length < 2 ^ (prefixWord ++ tailWord_209543).sum := by decide
  have hdescent : baseEnd_209543 < baseStart_209543 := by decide
  rcases family_descends (prefixWord ++ tailWord_209543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209550 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_209550 : Nat := 118140960795 + 209550 * 2 ^ 59
def prefixEnd_209550 : Nat := 4983230072969 + 3 ^ 40 * 209550 * 2
def baseEnd_209550 : Nat := 95644329910898105210047

theorem tailTrace_209550 : CollatzResearch.WordTrace tailWord_209550 prefixEnd_209550 95644329910898105210047 := by
  unfold tailWord_209550
  simp only [CollatzResearch.WordTrace]
  refine ⟨955364548855451641982263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5095277593895742090572069 955364548855451641982263)
  ·
    refine ⟨1433046823283177462973395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 955364548855451641982263 1433046823283177462973395)
    ·
      refine ⟨2149570234924766194460093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1433046823283177462973395 2149570234924766194460093)
      ·
        refine ⟨806088838096787322922535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2149570234924766194460093 806088838096787322922535)
        ·
          refine ⟨1209133257145180984383803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806088838096787322922535 1209133257145180984383803)
          ·
            refine ⟨1813699885717771476575705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209133257145180984383803 1813699885717771476575705)
            ·
              refine ⟨1360274914288328607431779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813699885717771476575705 1360274914288328607431779)
              ·
                refine ⟨2040412371432492911147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360274914288328607431779 2040412371432492911147669)
                ·
                  refine ⟨95644329910898105210047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2040412371432492911147669 95644329910898105210047)
                  ·
                    rfl

theorem cell20_209550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_209550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209550 prefixEnd_209550 := by exact prefixLift 209550
  have htrace : WordTrace (prefixWord ++ tailWord_209550) baseStart_209550 baseEnd_209550 := by
    simpa [prefixWord, tailWord_209550, baseEnd_209550] using wordTrace_append hprefix tailTrace_209550
  have hstable : (prefixWord ++ tailWord_209550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209550).length < 2 ^ (prefixWord ++ tailWord_209550).sum := by decide
  have hdescent : baseEnd_209550 < baseStart_209550 := by decide
  rcases family_descends (prefixWord ++ tailWord_209550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209571 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_209571 : Nat := 118140960795 + 209571 * 2 ^ 59
def prefixEnd_209571 : Nat := 4983230072969 + 3 ^ 40 * 209571 * 2
def baseEnd_209571 : Nat := 95653914883115365509961

theorem tailTrace_209571 : CollatzResearch.WordTrace tailWord_209571 prefixEnd_209571 95653914883115365509961 := by
  unfold tailWord_209571
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643682323767533722372567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5095788215845022481581711 7643682323767533722372567)
  ·
    refine ⟨11465523485651300583558851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7643682323767533722372567 11465523485651300583558851)
    ·
      refine ⟨17198285228476950875338277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11465523485651300583558851 17198285228476950875338277)
      ·
        refine ⟨3224678480339428289125927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17198285228476950875338277 3224678480339428289125927)
        ·
          refine ⟨4837017720509142433688891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224678480339428289125927 4837017720509142433688891)
          ·
            refine ⟨7255526580763713650533337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837017720509142433688891 7255526580763713650533337)
            ·
              refine ⟨5441644935572785237900003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7255526580763713650533337 5441644935572785237900003)
              ·
                refine ⟨8162467403359177856850005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441644935572785237900003 8162467403359177856850005)
                ·
                  refine ⟨95653914883115365509961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8162467403359177856850005 95653914883115365509961)
                  ·
                    rfl

theorem cell20_209571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_209571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209571 prefixEnd_209571 := by exact prefixLift 209571
  have htrace : WordTrace (prefixWord ++ tailWord_209571) baseStart_209571 baseEnd_209571 := by
    simpa [prefixWord, tailWord_209571, baseEnd_209571] using wordTrace_append hprefix tailTrace_209571
  have hstable : (prefixWord ++ tailWord_209571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209571).length < 2 ^ (prefixWord ++ tailWord_209571).sum := by decide
  have hdescent : baseEnd_209571 < baseStart_209571 := by decide
  rcases family_descends (prefixWord ++ tailWord_209571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209591 : List Nat := [1, 1, 3, 1, 7, 1, 1, 5]
def baseStart_209591 : Nat := 118140960795 + 209591 * 2 ^ 59
def prefixEnd_209591 : Nat := 4983230072969 + 3 ^ 40 * 209591 * 2
def baseEnd_209591 : Nat := 31887681142694728281071

theorem tailTrace_209591 : CollatzResearch.WordTrace tailWord_209591 prefixEnd_209591 31887681142694728281071 := by
  unfold tailWord_209591
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644411783695077138100627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5096274522463384758733751 7644411783695077138100627)
  ·
    refine ⟨11466617675542615707150941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7644411783695077138100627 11466617675542615707150941)
    ·
      refine ⟨4299981628328480890181603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11466617675542615707150941 4299981628328480890181603)
      ·
        refine ⟨6449972442492721335272405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299981628328480890181603 6449972442492721335272405)
        ·
          refine ⟨151171229120923156295447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6449972442492721335272405 151171229120923156295447)
          ·
            refine ⟨226756843681384734443171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151171229120923156295447 226756843681384734443171)
            ·
              refine ⟨340135265522077101664757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226756843681384734443171 340135265522077101664757)
              ·
                refine ⟨31887681142694728281071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 340135265522077101664757 31887681142694728281071)
                ·
                  rfl

theorem cell20_209591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5].length) (baseStart_209591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209591 prefixEnd_209591 := by exact prefixLift 209591
  have htrace : WordTrace (prefixWord ++ tailWord_209591) baseStart_209591 baseEnd_209591 := by
    simpa [prefixWord, tailWord_209591, baseEnd_209591] using wordTrace_append hprefix tailTrace_209591
  have hstable : (prefixWord ++ tailWord_209591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209591).length < 2 ^ (prefixWord ++ tailWord_209591).sum := by decide
  have hdescent : baseEnd_209591 < baseStart_209591 := by decide
  rcases family_descends (prefixWord ++ tailWord_209591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209633 : List Nat := [1, 2, 3, 1, 4, 2, 7]
def baseStart_209633 : Nat := 118140960795 + 209633 * 2 ^ 59
def prefixEnd_209633 : Nat := 4983230072969 + 3 ^ 40 * 209633 * 2
def baseEnd_209633 : Nat := 10631357041390967271449

theorem tailTrace_209633 : CollatzResearch.WordTrace tailWord_209633 prefixEnd_209633 10631357041390967271449 := by
  unfold tailWord_209633
  simp only [CollatzResearch.WordTrace]
  refine ⟨7645943649542918311129553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5097295766361945540753035 7645943649542918311129553)
  ·
    refine ⟨5734457737157188733347165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7645943649542918311129553 5734457737157188733347165)
    ·
      refine ⟨2150421651433945775005187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5734457737157188733347165 2150421651433945775005187)
      ·
        refine ⟨3225632477150918662507781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150421651433945775005187 3225632477150918662507781)
        ·
          refine ⟨604806089465797249220209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3225632477150918662507781 604806089465797249220209)
          ·
            refine ⟨453604567099347936915157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604806089465797249220209 453604567099347936915157)
            ·
              refine ⟨10631357041390967271449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 453604567099347936915157 10631357041390967271449)
              ·
                rfl

theorem cell20_209633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_209633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209633 prefixEnd_209633 := by exact prefixLift 209633
  have htrace : WordTrace (prefixWord ++ tailWord_209633) baseStart_209633 baseEnd_209633 := by
    simpa [prefixWord, tailWord_209633, baseEnd_209633] using wordTrace_append hprefix tailTrace_209633
  have hstable : (prefixWord ++ tailWord_209633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209633).length < 2 ^ (prefixWord ++ tailWord_209633).sum := by decide
  have hdescent : baseEnd_209633 < baseStart_209633 := by decide
  rcases family_descends (prefixWord ++ tailWord_209633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209636 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_209636 : Nat := 118140960795 + 209636 * 2 ^ 59
def prefixEnd_209636 : Nat := 4983230072969 + 3 ^ 40 * 209636 * 2
def baseEnd_209636 : Nat := 95683582654264028343029

theorem tailTrace_209636 : CollatzResearch.WordTrace tailWord_209636 prefixEnd_209636 95683582654264028343029 := by
  unfold tailWord_209636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823026534266024911744381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5097368712354699882325841 3823026534266024911744381)
  ·
    refine ⟨1433634950349759341904143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3823026534266024911744381 1433634950349759341904143)
    ·
      refine ⟨2150452425524639012856215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1433634950349759341904143 2150452425524639012856215)
      ·
        refine ⟨3225678638286958519284323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150452425524639012856215 3225678638286958519284323)
        ·
          refine ⟨4838517957430437778926485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225678638286958519284323 4838517957430437778926485)
          ·
            refine ⟨226805529254551770887179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4838517957430437778926485 226805529254551770887179)
            ·
              refine ⟨340208293881827656330769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226805529254551770887179 340208293881827656330769)
              ·
                refine ⟨255156220411370742248077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340208293881827656330769 255156220411370742248077)
                ·
                  refine ⟨95683582654264028343029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255156220411370742248077 95683582654264028343029)
                  ·
                    rfl

theorem cell20_209636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_209636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209636 prefixEnd_209636 := by exact prefixLift 209636
  have htrace : WordTrace (prefixWord ++ tailWord_209636) baseStart_209636 baseEnd_209636 := by
    simpa [prefixWord, tailWord_209636, baseEnd_209636] using wordTrace_append hprefix tailTrace_209636
  have hstable : (prefixWord ++ tailWord_209636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209636).length < 2 ^ (prefixWord ++ tailWord_209636).sum := by decide
  have hdescent : baseEnd_209636 < baseStart_209636 := by decide
  rcases family_descends (prefixWord ++ tailWord_209636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209681 : List Nat := [1, 2, 2, 1, 1, 3, 5, 3, 2]
def baseStart_209681 : Nat := 118140960795 + 209681 * 2 ^ 59
def prefixEnd_209681 : Nat := 4983230072969 + 3 ^ 40 * 209681 * 2
def baseEnd_209681 : Nat := 95704121880443871842845

theorem tailTrace_209681 : CollatzResearch.WordTrace tailWord_209681 prefixEnd_209681 95704121880443871842845 := by
  unfold tailWord_209681
  simp only [CollatzResearch.WordTrace]
  refine ⟨7647694353369022508876897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5098462902246015005917931 7647694353369022508876897)
  ·
    refine ⟨5735770765026766881657673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7647694353369022508876897 5735770765026766881657673)
    ·
      refine ⟨4301828073770075161243255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5735770765026766881657673 4301828073770075161243255)
      ·
        refine ⟨6452742110655112741864883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301828073770075161243255 6452742110655112741864883)
        ·
          refine ⟨9679113165982669112797325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452742110655112741864883 9679113165982669112797325)
          ·
            refine ⟨3629667437243500917298997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9679113165982669112797325 3629667437243500917298997)
            ·
              refine ⟨340281322241578210996781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3629667437243500917298997 340281322241578210996781)
              ·
                refine ⟨127605495840591829123793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340281322241578210996781 127605495840591829123793)
                ·
                  refine ⟨95704121880443871842845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127605495840591829123793 95704121880443871842845)
                  ·
                    rfl

theorem cell20_209681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_209681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209681 prefixEnd_209681 := by exact prefixLift 209681
  have htrace : WordTrace (prefixWord ++ tailWord_209681) baseStart_209681 baseEnd_209681 := by
    simpa [prefixWord, tailWord_209681, baseEnd_209681] using wordTrace_append hprefix tailTrace_209681
  have hstable : (prefixWord ++ tailWord_209681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209681).length < 2 ^ (prefixWord ++ tailWord_209681).sum := by decide
  have hdescent : baseEnd_209681 < baseStart_209681 := by decide
  rcases family_descends (prefixWord ++ tailWord_209681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209764 : List Nat := [2, 3, 1, 1, 4, 3, 1, 5]
def baseStart_209764 : Nat := 118140960795 + 209764 * 2 ^ 59
def prefixEnd_209764 : Nat := 4983230072969 + 3 ^ 40 * 209764 * 2
def baseEnd_209764 : Nat := 31914001780688157358613

theorem tailTrace_209764 : CollatzResearch.WordTrace tailWord_209764 prefixEnd_209764 31914001780688157358613 := by
  unfold tailWord_209764
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825360806034163842074173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5100481074712218456098897 3825360806034163842074173)
  ·
    refine ⟨1434510302262811440777815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3825360806034163842074173 1434510302262811440777815)
    ·
      refine ⟨2151765453394217161166723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1434510302262811440777815 2151765453394217161166723)
      ·
        refine ⟨3227648180091325741750085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151765453394217161166723 3227648180091325741750085)
        ·
          refine ⟨605184033767123576578141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3227648180091325741750085 605184033767123576578141)
          ·
            refine ⟨226944012662671341216803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 605184033767123576578141 226944012662671341216803)
            ·
              refine ⟨340416018994007011825205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226944012662671341216803 340416018994007011825205)
              ·
                refine ⟨31914001780688157358613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 340416018994007011825205 31914001780688157358613)
                ·
                  rfl

theorem cell20_209764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_209764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209764 prefixEnd_209764 := by exact prefixLift 209764
  have htrace : WordTrace (prefixWord ++ tailWord_209764) baseStart_209764 baseEnd_209764 := by
    simpa [prefixWord, tailWord_209764, baseEnd_209764] using wordTrace_append hprefix tailTrace_209764
  have hstable : (prefixWord ++ tailWord_209764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209764).length < 2 ^ (prefixWord ++ tailWord_209764).sum := by decide
  have hdescent : baseEnd_209764 < baseStart_209764 := by decide
  rcases family_descends (prefixWord ++ tailWord_209764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209795 : List Nat := [1, 1, 1, 3, 4, 1, 4, 3, 2]
def baseStart_209795 : Nat := 118140960795 + 209795 * 2 ^ 59
def prefixEnd_209795 : Nat := 4983230072969 + 3 ^ 40 * 209795 * 2
def baseEnd_209795 : Nat := 95756154586766142042379

theorem tailTrace_209795 : CollatzResearch.WordTrace tailWord_209795 prefixEnd_209795 95756154586766142042379 := by
  unfold tailWord_209795
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651852274956019978526839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5101234849970679985684559 7651852274956019978526839)
  ·
    refine ⟨11477778412434029967790259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7651852274956019978526839 11477778412434029967790259)
    ·
      refine ⟨17216667618651044951685389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11477778412434029967790259 17216667618651044951685389)
      ·
        refine ⟨6456250356994141856882021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17216667618651044951685389 6456250356994141856882021)
        ·
          refine ⟨1210546941936401598165379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6456250356994141856882021 1210546941936401598165379)
          ·
            refine ⟨1815820412904602397248069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210546941936401598165379 1815820412904602397248069)
            ·
              refine ⟨340466327419612949484013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1815820412904602397248069 340466327419612949484013)
              ·
                refine ⟨127674872782354856056505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340466327419612949484013 127674872782354856056505)
                ·
                  refine ⟨95756154586766142042379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127674872782354856056505 95756154586766142042379)
                  ·
                    rfl

theorem cell20_209795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 2].length) (baseStart_209795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209795 prefixEnd_209795 := by exact prefixLift 209795
  have htrace : WordTrace (prefixWord ++ tailWord_209795) baseStart_209795 baseEnd_209795 := by
    simpa [prefixWord, tailWord_209795, baseEnd_209795] using wordTrace_append hprefix tailTrace_209795
  have hstable : (prefixWord ++ tailWord_209795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209795).length < 2 ^ (prefixWord ++ tailWord_209795).sum := by decide
  have hdescent : baseEnd_209795 < baseStart_209795 := by decide
  rcases family_descends (prefixWord ++ tailWord_209795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209868 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_209868 : Nat := 118140960795 + 209868 * 2 ^ 59
def prefixEnd_209868 : Nat := 4983230072969 + 3 ^ 40 * 209868 * 2
def baseEnd_209868 : Nat := 95789473775902332608747

theorem tailTrace_209868 : CollatzResearch.WordTrace tailWord_209868 prefixEnd_209868 95789473775902332608747 := by
  unfold tailWord_209868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827257401845776722967129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5103009869127702297289505 3827257401845776722967129)
  ·
    refine ⟨2870443051384332542225347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3827257401845776722967129 2870443051384332542225347)
    ·
      refine ⟨4305664577076498813338021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2870443051384332542225347 4305664577076498813338021)
      ·
        refine ⟨807312108201843527500879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4305664577076498813338021 807312108201843527500879)
        ·
          refine ⟨1210968162302765291251319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807312108201843527500879 1210968162302765291251319)
          ·
            refine ⟨1816452243454147936876979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210968162302765291251319 1816452243454147936876979)
            ·
              refine ⟨2724678365181221905315469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816452243454147936876979 2724678365181221905315469)
              ·
                refine ⟨1021754386942958214493301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2724678365181221905315469 1021754386942958214493301)
                ·
                  refine ⟨95789473775902332608747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1021754386942958214493301 95789473775902332608747)
                  ·
                    rfl

theorem cell20_209868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_209868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209868 prefixEnd_209868 := by exact prefixLift 209868
  have htrace : WordTrace (prefixWord ++ tailWord_209868) baseStart_209868 baseEnd_209868 := by
    simpa [prefixWord, tailWord_209868, baseEnd_209868] using wordTrace_append hprefix tailTrace_209868
  have hstable : (prefixWord ++ tailWord_209868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209868).length < 2 ^ (prefixWord ++ tailWord_209868).sum := by decide
  have hdescent : baseEnd_209868 < baseStart_209868 := by decide
  rcases family_descends (prefixWord ++ tailWord_209868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209878 : List Nat := [5, 2, 1, 1, 2, 1, 1, 7]
def baseStart_209878 : Nat := 118140960795 + 209878 * 2 ^ 59
def prefixEnd_209878 : Nat := 4983230072969 + 3 ^ 40 * 209878 * 2
def baseEnd_209878 : Nat := 31931346016128914091791

theorem tailTrace_209878 : CollatzResearch.WordTrace tailWord_209878 prefixEnd_209878 31931346016128914091791 := by
  unfold tailWord_209878
  simp only [CollatzResearch.WordTrace]
  refine ⟨478429970853457822112393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5103253022436883435865525 478429970853457822112393)
  ·
    refine ⟨358822478140093366584295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 478429970853457822112393 358822478140093366584295)
    ·
      refine ⟨538233717210140049876443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358822478140093366584295 538233717210140049876443)
      ·
        refine ⟨807350575815210074814665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538233717210140049876443 807350575815210074814665)
        ·
          refine ⟨605512931861407556110999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807350575815210074814665 605512931861407556110999)
          ·
            refine ⟨908269397792111334166499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605512931861407556110999 908269397792111334166499)
            ·
              refine ⟨1362404096688167001249749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908269397792111334166499 1362404096688167001249749)
              ·
                refine ⟨31931346016128914091791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1362404096688167001249749 31931346016128914091791)
                ·
                  rfl

theorem cell20_209878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_209878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209878 prefixEnd_209878 := by exact prefixLift 209878
  have htrace : WordTrace (prefixWord ++ tailWord_209878) baseStart_209878 baseEnd_209878 := by
    simpa [prefixWord, tailWord_209878, baseEnd_209878] using wordTrace_append hprefix tailTrace_209878
  have hstable : (prefixWord ++ tailWord_209878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209878).length < 2 ^ (prefixWord ++ tailWord_209878).sum := by decide
  have hdescent : baseEnd_209878 < baseStart_209878 := by decide
  rcases family_descends (prefixWord ++ tailWord_209878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209951 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_209951 : Nat := 118140960795 + 209951 * 2 ^ 59
def prefixEnd_209951 : Nat := 4983230072969 + 3 ^ 40 * 209951 * 2
def baseEnd_209951 : Nat := 95827357237522932841741

theorem tailTrace_209951 : CollatzResearch.WordTrace tailWord_209951 prefixEnd_209951 95827357237522932841741 := by
  unfold tailWord_209951
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657542062390858621205707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5105028041593905747470471 7657542062390858621205707)
  ·
    refine ⟨11486313093586287931808561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7657542062390858621205707 11486313093586287931808561)
    ·
      refine ⟨8614734820189715948856421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11486313093586287931808561 8614734820189715948856421)
      ·
        refine ⟨1615262778785571740410579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8614734820189715948856421 1615262778785571740410579)
        ·
          refine ⟨2422894168178357610615869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615262778785571740410579 2422894168178357610615869)
          ·
            refine ⟨908585313066884103980951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2422894168178357610615869 908585313066884103980951)
            ·
              refine ⟨1362877969600326155971427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908585313066884103980951 1362877969600326155971427)
              ·
                refine ⟨2044316954400489233957141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362877969600326155971427 2044316954400489233957141)
                ·
                  refine ⟨95827357237522932841741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2044316954400489233957141 95827357237522932841741)
                  ·
                    rfl

theorem cell20_209951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_209951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209951 prefixEnd_209951 := by exact prefixLift 209951
  have htrace : WordTrace (prefixWord ++ tailWord_209951) baseStart_209951 baseEnd_209951 := by
    simpa [prefixWord, tailWord_209951, baseEnd_209951] using wordTrace_append hprefix tailTrace_209951
  have hstable : (prefixWord ++ tailWord_209951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209951).length < 2 ^ (prefixWord ++ tailWord_209951).sum := by decide
  have hdescent : baseEnd_209951 < baseStart_209951 := by decide
  rcases family_descends (prefixWord ++ tailWord_209951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209954 : List Nat := [3, 3, 1, 1, 1, 4, 3, 4]
def baseStart_209954 : Nat := 118140960795 + 209954 * 2 ^ 59
def prefixEnd_209954 : Nat := 4983230072969 + 3 ^ 40 * 209954 * 2
def baseEnd_209954 : Nat := 31942908839756085247243

theorem tailTrace_209954 : CollatzResearch.WordTrace tailWord_209954 prefixEnd_209954 31942908839756085247243 := by
  unfold tailWord_209954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914412870344997533391229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5105100987586660089043277 1914412870344997533391229)
  ·
    refine ⟨717904826379374075021711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1914412870344997533391229 717904826379374075021711)
    ·
      refine ⟨1076857239569061112532567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717904826379374075021711 1076857239569061112532567)
      ·
        refine ⟨1615285859353591668798851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076857239569061112532567 1615285859353591668798851)
        ·
          refine ⟨2422928789030387503198277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615285859353591668798851 2422928789030387503198277)
          ·
            refine ⟨454299147943197656849677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2422928789030387503198277 454299147943197656849677)
            ·
              refine ⟨170362180478699121318629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454299147943197656849677 170362180478699121318629)
              ·
                refine ⟨31942908839756085247243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170362180478699121318629 31942908839756085247243)
                ·
                  rfl

theorem cell20_209954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_209954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209954 prefixEnd_209954 := by exact prefixLift 209954
  have htrace : WordTrace (prefixWord ++ tailWord_209954) baseStart_209954 baseEnd_209954 := by
    simpa [prefixWord, tailWord_209954, baseEnd_209954] using wordTrace_append hprefix tailTrace_209954
  have hstable : (prefixWord ++ tailWord_209954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209954).length < 2 ^ (prefixWord ++ tailWord_209954).sum := by decide
  have hdescent : baseEnd_209954 < baseStart_209954 := by decide
  rcases family_descends (prefixWord ++ tailWord_209954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209985 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 4]
def baseStart_209985 : Nat := 118140960795 + 209985 * 2 ^ 59
def prefixEnd_209985 : Nat := 4983230072969 + 3 ^ 40 * 209985 * 2
def baseEnd_209985 : Nat := 95842875763969925708269

theorem tailTrace_209985 : CollatzResearch.WordTrace tailWord_209985 prefixEnd_209985 95842875763969925708269 := by
  unfold tailWord_209985
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658782144267682427943409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5105854762845121618628939 7658782144267682427943409)
  ·
    refine ⟨5744086608200761820957557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7658782144267682427943409 5744086608200761820957557)
    ·
      refine ⟨538508119518821420714771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5744086608200761820957557 538508119518821420714771)
      ·
        refine ⟨807762179278232131072157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538508119518821420714771 807762179278232131072157)
        ·
          refine ⟨302910817229337049152059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 807762179278232131072157 302910817229337049152059)
          ·
            refine ⟨454366225844005573728089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302910817229337049152059 454366225844005573728089)
            ·
              refine ⟨340774669383004180296067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454366225844005573728089 340774669383004180296067)
              ·
                refine ⟨511162004074506270444101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340774669383004180296067 511162004074506270444101)
                ·
                  refine ⟨95842875763969925708269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511162004074506270444101 95842875763969925708269)
                  ·
                    rfl

theorem cell20_209985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_209985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209985 prefixEnd_209985 := by exact prefixLift 209985
  have htrace : WordTrace (prefixWord ++ tailWord_209985) baseStart_209985 baseEnd_209985 := by
    simpa [prefixWord, tailWord_209985, baseEnd_209985] using wordTrace_append hprefix tailTrace_209985
  have hstable : (prefixWord ++ tailWord_209985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209985).length < 2 ^ (prefixWord ++ tailWord_209985).sum := by decide
  have hdescent : baseEnd_209985 < baseStart_209985 := by decide
  rcases family_descends (prefixWord ++ tailWord_209985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209989 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_209989 : Nat := 118140960795 + 209989 * 2 ^ 59
def prefixEnd_209989 : Nat := 4983230072969 + 3 ^ 40 * 209989 * 2
def baseEnd_209989 : Nat := 95844701472963689574919

theorem tailTrace_209989 : CollatzResearch.WordTrace tailWord_209989 prefixEnd_209989 95844701472963689574919 := by
  unfold tailWord_209989
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658928036253191111089021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5105952024168794074059347 7658928036253191111089021)
  ·
    refine ⟨2872098013594946666658383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7658928036253191111089021 2872098013594946666658383)
    ·
      refine ⟨4308147020392419999987575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872098013594946666658383 4308147020392419999987575)
      ·
        refine ⟨6462220530588629999981363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308147020392419999987575 6462220530588629999981363)
        ·
          refine ⟨9693330795882944999972045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462220530588629999981363 9693330795882944999972045)
          ·
            refine ⟨3634999048456104374989517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9693330795882944999972045 3634999048456104374989517)
            ·
              refine ⟨1363124643171039140621069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3634999048456104374989517 1363124643171039140621069)
              ·
                refine ⟨511171741189139677732901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1363124643171039140621069 511171741189139677732901)
                ·
                  refine ⟨95844701472963689574919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511171741189139677732901 95844701472963689574919)
                  ·
                    rfl

theorem cell20_209989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_209989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209989 prefixEnd_209989 := by exact prefixLift 209989
  have htrace : WordTrace (prefixWord ++ tailWord_209989) baseStart_209989 baseEnd_209989 := by
    simpa [prefixWord, tailWord_209989, baseEnd_209989] using wordTrace_append hprefix tailTrace_209989
  have hstable : (prefixWord ++ tailWord_209989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209989).length < 2 ^ (prefixWord ++ tailWord_209989).sum := by decide
  have hdescent : baseEnd_209989 < baseStart_209989 := by decide
  rcases family_descends (prefixWord ++ tailWord_209989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209996 : List Nat := [2, 2, 1, 3, 1, 1, 1, 9]
def baseStart_209996 : Nat := 118140960795 + 209996 * 2 ^ 59
def prefixEnd_209996 : Nat := 4983230072969 + 3 ^ 40 * 209996 * 2
def baseEnd_209996 : Nat := 31949298821234258780519

theorem tailTrace_209996 : CollatzResearch.WordTrace tailWord_209996 prefixEnd_209996 31949298821234258780519 := by
  unfold tailWord_209996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829591673613915653296921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5106122231485220871062561 3829591673613915653296921)
  ·
    refine ⟨2872193755210436739972691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3829591673613915653296921 2872193755210436739972691)
    ·
      refine ⟨4308290632815655109959037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872193755210436739972691 4308290632815655109959037)
      ·
        refine ⟨1615608987305870666234639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4308290632815655109959037 1615608987305870666234639)
        ·
          refine ⟨2423413480958805999351959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615608987305870666234639 2423413480958805999351959)
          ·
            refine ⟨3635120221438208999027939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423413480958805999351959 3635120221438208999027939)
            ·
              refine ⟨5452680332157313498541909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635120221438208999027939 5452680332157313498541909)
              ·
                refine ⟨31949298821234258780519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5452680332157313498541909 31949298821234258780519)
                ·
                  rfl

theorem cell20_209996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_209996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_209996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_209996 prefixEnd_209996 := by exact prefixLift 209996
  have htrace : WordTrace (prefixWord ++ tailWord_209996) baseStart_209996 baseEnd_209996 := by
    simpa [prefixWord, tailWord_209996, baseEnd_209996] using wordTrace_append hprefix tailTrace_209996
  have hstable : (prefixWord ++ tailWord_209996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209996).length < 2 ^ (prefixWord ++ tailWord_209996).sum := by decide
  have hdescent : baseEnd_209996 < baseStart_209996 := by decide
  rcases family_descends (prefixWord ++ tailWord_209996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210003 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_210003 : Nat := 118140960795 + 210003 * 2 ^ 59
def prefixEnd_210003 : Nat := 4983230072969 + 3 ^ 40 * 210003 * 2
def baseEnd_210003 : Nat := 95851091454441863108195

theorem tailTrace_210003 : CollatzResearch.WordTrace tailWord_210003 prefixEnd_210003 95851091454441863108195 := by
  unfold tailWord_210003
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659438658202471502098663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5106292438801647668065775 7659438658202471502098663)
  ·
    refine ⟨11489157987303707253147995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7659438658202471502098663 11489157987303707253147995)
    ·
      refine ⟨17233736980955560879721993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11489157987303707253147995 17233736980955560879721993)
      ·
        refine ⟨12925302735716670659791495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17233736980955560879721993 12925302735716670659791495)
        ·
          refine ⟨19387954103575005989687243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12925302735716670659791495 19387954103575005989687243)
          ·
            refine ⟨29081931155362508984530865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19387954103575005989687243 29081931155362508984530865)
            ·
              refine ⟨21811448366521881738398149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29081931155362508984530865 21811448366521881738398149)
              ·
                refine ⟨4089646568722852825949653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21811448366521881738398149 4089646568722852825949653)
                ·
                  refine ⟨95851091454441863108195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4089646568722852825949653 95851091454441863108195)
                  ·
                    rfl

theorem cell20_210003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_210003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210003 prefixEnd_210003 := by exact prefixLift 210003
  have htrace : WordTrace (prefixWord ++ tailWord_210003) baseStart_210003 baseEnd_210003 := by
    simpa [prefixWord, tailWord_210003, baseEnd_210003] using wordTrace_append hprefix tailTrace_210003
  have hstable : (prefixWord ++ tailWord_210003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210003).length < 2 ^ (prefixWord ++ tailWord_210003).sum := by decide
  have hdescent : baseEnd_210003 < baseStart_210003 := by decide
  rcases family_descends (prefixWord ++ tailWord_210003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210023 : List Nat := [1, 1, 5, 1, 1, 3, 3, 3, 2]
def baseStart_210023 : Nat := 118140960795 + 210023 * 2 ^ 59
def prefixEnd_210023 : Nat := 4983230072969 + 3 ^ 40 * 210023 * 2
def baseEnd_210023 : Nat := 95860219999410682441447

theorem tailTrace_210023 : CollatzResearch.WordTrace tailWord_210023 prefixEnd_210023 95860219999410682441447 := by
  unfold tailWord_210023
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660168118130014917826723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5106778745420009945217815 7660168118130014917826723)
  ·
    refine ⟨11490252177195022376740085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7660168118130014917826723 11490252177195022376740085)
    ·
      refine ⟨1077211141612033347819383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11490252177195022376740085 1077211141612033347819383)
      ·
        refine ⟨1615816712418050021729075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077211141612033347819383 1615816712418050021729075)
        ·
          refine ⟨2423725068627075032593613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615816712418050021729075 2423725068627075032593613)
          ·
            refine ⟨908896900735153137222605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2423725068627075032593613 908896900735153137222605)
            ·
              refine ⟨340836337775682426458477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908896900735153137222605 340836337775682426458477)
              ·
                refine ⟨127813626665880909921929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340836337775682426458477 127813626665880909921929)
                ·
                  refine ⟨95860219999410682441447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127813626665880909921929 95860219999410682441447)
                  ·
                    rfl

theorem cell20_210023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 2].length) (baseStart_210023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210023 prefixEnd_210023 := by exact prefixLift 210023
  have htrace : WordTrace (prefixWord ++ tailWord_210023) baseStart_210023 baseEnd_210023 := by
    simpa [prefixWord, tailWord_210023, baseEnd_210023] using wordTrace_append hprefix tailTrace_210023
  have hstable : (prefixWord ++ tailWord_210023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210023).length < 2 ^ (prefixWord ++ tailWord_210023).sum := by decide
  have hdescent : baseEnd_210023 < baseStart_210023 := by decide
  rcases family_descends (prefixWord ++ tailWord_210023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210046 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_210046 : Nat := 118140960795 + 210046 * 2 ^ 59
def prefixEnd_210046 : Nat := 4983230072969 + 3 ^ 40 * 210046 * 2
def baseEnd_210046 : Nat := 95870717826124824674687

theorem tailTrace_210046 : CollatzResearch.WordTrace tailWord_210046 prefixEnd_210046 95870717826124824674687 := by
  unfold tailWord_210046
  simp only [CollatzResearch.WordTrace]
  refine ⟨957625874630836230739249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5107337998031126563942661 957625874630836230739249)
  ·
    refine ⟨718219405973127173054437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 957625874630836230739249 718219405973127173054437)
    ·
      refine ⟨134666138619961344947707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 718219405973127173054437 134666138619961344947707)
      ·
        refine ⟨201999207929942017421561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134666138619961344947707 201999207929942017421561)
        ·
          refine ⟨151499405947456513066171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201999207929942017421561 151499405947456513066171)
          ·
            refine ⟨227249108921184769599257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151499405947456513066171 227249108921184769599257)
            ·
              refine ⟨170436831690888577199443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227249108921184769599257 170436831690888577199443)
              ·
                refine ⟨255655247536332865799165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170436831690888577199443 255655247536332865799165)
                ·
                  refine ⟨95870717826124824674687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255655247536332865799165 95870717826124824674687)
                  ·
                    rfl

theorem cell20_210046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_210046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210046 prefixEnd_210046 := by exact prefixLift 210046
  have htrace : WordTrace (prefixWord ++ tailWord_210046) baseStart_210046 baseEnd_210046 := by
    simpa [prefixWord, tailWord_210046, baseEnd_210046] using wordTrace_append hprefix tailTrace_210046
  have hstable : (prefixWord ++ tailWord_210046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210046).length < 2 ^ (prefixWord ++ tailWord_210046).sum := by decide
  have hdescent : baseEnd_210046 < baseStart_210046 := by decide
  rcases family_descends (prefixWord ++ tailWord_210046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210099 : List Nat := [1, 1, 1, 2, 3, 2, 6, 2, 2]
def baseStart_210099 : Nat := 118140960795 + 210099 * 2 ^ 59
def prefixEnd_210099 : Nat := 4983230072969 + 3 ^ 40 * 210099 * 2
def baseEnd_210099 : Nat := 95894908470292195907803

theorem tailTrace_210099 : CollatzResearch.WordTrace tailWord_210099 prefixEnd_210099 95894908470292195907803 := by
  unfold tailWord_210099
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662940065854679897593351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5108626710569786598395567 7662940065854679897593351)
  ·
    refine ⟨11494410098782019846390027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7662940065854679897593351 11494410098782019846390027)
    ·
      refine ⟨17241615148173029769585041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11494410098782019846390027 17241615148173029769585041)
      ·
        refine ⟨12931211361129772327188781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17241615148173029769585041 12931211361129772327188781)
        ·
          refine ⟨4849204260423664622695793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12931211361129772327188781 4849204260423664622695793)
          ·
            refine ⟨3636903195317748467021845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4849204260423664622695793 3636903195317748467021845)
            ·
              refine ⟨170479837280519459391649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3636903195317748467021845 170479837280519459391649)
              ·
                refine ⟨127859877960389594543737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170479837280519459391649 127859877960389594543737)
                ·
                  refine ⟨95894908470292195907803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127859877960389594543737 95894908470292195907803)
                  ·
                    rfl

theorem cell20_210099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 2].length) (baseStart_210099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210099 prefixEnd_210099 := by exact prefixLift 210099
  have htrace : WordTrace (prefixWord ++ tailWord_210099) baseStart_210099 baseEnd_210099 := by
    simpa [prefixWord, tailWord_210099, baseEnd_210099] using wordTrace_append hprefix tailTrace_210099
  have hstable : (prefixWord ++ tailWord_210099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210099).length < 2 ^ (prefixWord ++ tailWord_210099).sum := by decide
  have hdescent : baseEnd_210099 < baseStart_210099 := by decide
  rcases family_descends (prefixWord ++ tailWord_210099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210102 : List Nat := [5, 1, 3, 2, 1, 2, 1, 5]
def baseStart_210102 : Nat := 118140960795 + 210102 * 2 ^ 59
def prefixEnd_210102 : Nat := 4983230072969 + 3 ^ 40 * 210102 * 2
def baseEnd_210102 : Nat := 31965425917345839602597

theorem tailTrace_210102 : CollatzResearch.WordTrace tailWord_210102 prefixEnd_210102 31965425917345839602597 := by
  unfold tailWord_210102
  simp only [CollatzResearch.WordTrace]
  refine ⟨478940592802738213122035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5108699656562540939968373 478940592802738213122035)
  ·
    refine ⟨718410889204107319683053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478940592802738213122035 718410889204107319683053)
    ·
      refine ⟨269404083451540244881145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 718410889204107319683053 269404083451540244881145)
      ·
        refine ⟨202053062588655183660859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269404083451540244881145 202053062588655183660859)
        ·
          refine ⟨303079593882982775491289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202053062588655183660859 303079593882982775491289)
          ·
            refine ⟨227309695412237081618467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303079593882982775491289 227309695412237081618467)
            ·
              refine ⟨340964543118355622427701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227309695412237081618467 340964543118355622427701)
              ·
                refine ⟨31965425917345839602597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 340964543118355622427701 31965425917345839602597)
                ·
                  rfl

theorem cell20_210102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_210102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210102 prefixEnd_210102 := by exact prefixLift 210102
  have htrace : WordTrace (prefixWord ++ tailWord_210102) baseStart_210102 baseEnd_210102 := by
    simpa [prefixWord, tailWord_210102, baseEnd_210102] using wordTrace_append hprefix tailTrace_210102
  have hstable : (prefixWord ++ tailWord_210102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210102).length < 2 ^ (prefixWord ++ tailWord_210102).sum := by decide
  have hdescent : baseEnd_210102 < baseStart_210102 := by decide
  rcases family_descends (prefixWord ++ tailWord_210102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210103 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_210103 : Nat := 118140960795 + 210103 * 2 ^ 59
def prefixEnd_210103 : Nat := 4983230072969 + 3 ^ 40 * 210103 * 2
def baseEnd_210103 : Nat := 95896734179285959774453

theorem tailTrace_210103 : CollatzResearch.WordTrace tailWord_210103 prefixEnd_210103 95896734179285959774453 := by
  unfold tailWord_210103
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663085957840188580738963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5108723971893459053825975 7663085957840188580738963)
  ·
    refine ⟨11494628936760282871108445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7663085957840188580738963 11494628936760282871108445)
    ·
      refine ⟨4310485851285106076665667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11494628936760282871108445 4310485851285106076665667)
      ·
        refine ⟨6465728776927659114998501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310485851285106076665667 6465728776927659114998501)
        ·
          refine ⟨1212324145673936084062219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6465728776927659114998501 1212324145673936084062219)
          ·
            refine ⟨1818486218510904126093329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212324145673936084062219 1818486218510904126093329)
            ·
              refine ⟨1363864663883178094569997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818486218510904126093329 1363864663883178094569997)
              ·
                refine ⟨511449248956191785463749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1363864663883178094569997 511449248956191785463749)
                ·
                  refine ⟨95896734179285959774453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511449248956191785463749 95896734179285959774453)
                  ·
                    rfl

theorem cell20_210103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_210103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210103 prefixEnd_210103 := by exact prefixLift 210103
  have htrace : WordTrace (prefixWord ++ tailWord_210103) baseStart_210103 baseEnd_210103 := by
    simpa [prefixWord, tailWord_210103, baseEnd_210103] using wordTrace_append hprefix tailTrace_210103
  have hstable : (prefixWord ++ tailWord_210103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210103).length < 2 ^ (prefixWord ++ tailWord_210103).sum := by decide
  have hdescent : baseEnd_210103 < baseStart_210103 := by decide
  rcases family_descends (prefixWord ++ tailWord_210103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210117 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_210117 : Nat := 118140960795 + 210117 * 2 ^ 59
def prefixEnd_210117 : Nat := 4983230072969 + 3 ^ 40 * 210117 * 2
def baseEnd_210117 : Nat := 95903124160764133307729

theorem tailTrace_210117 : CollatzResearch.WordTrace tailWord_210117 prefixEnd_210117 95903124160764133307729 := by
  unfold tailWord_210117
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663596579789468971748605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5109064386526312647832403 7663596579789468971748605)
  ·
    refine ⟨2873848717421050864405727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7663596579789468971748605 2873848717421050864405727)
    ·
      refine ⟨4310773076131576296608591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2873848717421050864405727 4310773076131576296608591)
      ·
        refine ⟨6466159614197364444912887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310773076131576296608591 6466159614197364444912887)
        ·
          refine ⟨9699239421296046667369331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6466159614197364444912887 9699239421296046667369331)
          ·
            refine ⟨14548859131944070001053997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9699239421296046667369331 14548859131944070001053997)
            ·
              refine ⟨5455822174479026250395249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14548859131944070001053997 5455822174479026250395249)
              ·
                refine ⟨4091866630859269687796437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5455822174479026250395249 4091866630859269687796437)
                ·
                  refine ⟨95903124160764133307729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4091866630859269687796437 95903124160764133307729)
                  ·
                    rfl

theorem cell20_210117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_210117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210117 prefixEnd_210117 := by exact prefixLift 210117
  have htrace : WordTrace (prefixWord ++ tailWord_210117) baseStart_210117 baseEnd_210117 := by
    simpa [prefixWord, tailWord_210117, baseEnd_210117] using wordTrace_append hprefix tailTrace_210117
  have hstable : (prefixWord ++ tailWord_210117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210117).length < 2 ^ (prefixWord ++ tailWord_210117).sum := by decide
  have hdescent : baseEnd_210117 < baseStart_210117 := by decide
  rcases family_descends (prefixWord ++ tailWord_210117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210151 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 5]
def baseStart_210151 : Nat := 118140960795 + 210151 * 2 ^ 59
def prefixEnd_210151 : Nat := 4983230072969 + 3 ^ 40 * 210151 * 2
def baseEnd_210151 : Nat := 95918642687211126174257

theorem tailTrace_210151 : CollatzResearch.WordTrace tailWord_210151 prefixEnd_210151 95918642687211126174257 := by
  unfold tailWord_210151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7664836661666292778486307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5109891107777528518990871 7664836661666292778486307)
  ·
    refine ⟨11497254992499439167729461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7664836661666292778486307 11497254992499439167729461)
    ·
      refine ⟨1077867655546822421974637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11497254992499439167729461 1077867655546822421974637)
      ·
        refine ⟨404200370830058408240489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1077867655546822421974637 404200370830058408240489)
        ·
          refine ⟨303150278122543806180367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404200370830058408240489 303150278122543806180367)
          ·
            refine ⟨454725417183815709270551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303150278122543806180367 454725417183815709270551)
            ·
              refine ⟨682088125775723563905827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454725417183815709270551 682088125775723563905827)
              ·
                refine ⟨1023132188663585345858741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682088125775723563905827 1023132188663585345858741)
                ·
                  refine ⟨95918642687211126174257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1023132188663585345858741 95918642687211126174257)
                  ·
                    rfl

theorem cell20_210151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_210151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210151 prefixEnd_210151 := by exact prefixLift 210151
  have htrace : WordTrace (prefixWord ++ tailWord_210151) baseStart_210151 baseEnd_210151 := by
    simpa [prefixWord, tailWord_210151, baseEnd_210151] using wordTrace_append hprefix tailTrace_210151
  have hstable : (prefixWord ++ tailWord_210151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210151).length < 2 ^ (prefixWord ++ tailWord_210151).sum := by decide
  have hdescent : baseEnd_210151 < baseStart_210151 := by decide
  rcases family_descends (prefixWord ++ tailWord_210151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210178 : List Nat := [3, 4, 1, 1, 4, 1, 2, 4]
def baseStart_210178 : Nat := 118140960795 + 210178 * 2 ^ 59
def prefixEnd_210178 : Nat := 4983230072969 + 3 ^ 40 * 210178 * 2
def baseEnd_210178 : Nat := 31976988740973010758049

theorem tailTrace_210178 : CollatzResearch.WordTrace tailWord_210178 prefixEnd_210178 31976988740973010758049 := by
  unfold tailWord_210178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916455358142119097429797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5110547621712317593146125 1916455358142119097429797)
  ·
    refine ⟨359335379651647330768087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1916455358142119097429797 359335379651647330768087)
    ·
      refine ⟨539003069477470996152131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359335379651647330768087 539003069477470996152131)
      ·
        refine ⟨808504604216206494228197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539003069477470996152131 808504604216206494228197)
        ·
          refine ⟨151594613290538717667787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 808504604216206494228197 151594613290538717667787)
          ·
            refine ⟨227391919935808076501681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151594613290538717667787 227391919935808076501681)
            ·
              refine ⟨170543939951856057376261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227391919935808076501681 170543939951856057376261)
              ·
                refine ⟨31976988740973010758049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170543939951856057376261 31976988740973010758049)
                ·
                  rfl

theorem cell20_210178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_210178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210178 prefixEnd_210178 := by exact prefixLift 210178
  have htrace : WordTrace (prefixWord ++ tailWord_210178) baseStart_210178 baseEnd_210178 := by
    simpa [prefixWord, tailWord_210178, baseEnd_210178] using wordTrace_append hprefix tailTrace_210178
  have hstable : (prefixWord ++ tailWord_210178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210178).length < 2 ^ (prefixWord ++ tailWord_210178).sum := by decide
  have hdescent : baseEnd_210178 < baseStart_210178 := by decide
  rcases family_descends (prefixWord ++ tailWord_210178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210179 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_210179 : Nat := 118140960795 + 210179 * 2 ^ 59
def prefixEnd_210179 : Nat := 4983230072969 + 3 ^ 40 * 210179 * 2
def baseEnd_210179 : Nat := 95931422650167473240809

theorem tailTrace_210179 : CollatzResearch.WordTrace tailWord_210179 prefixEnd_210179 95931422650167473240809 := by
  unfold tailWord_210179
  simp only [CollatzResearch.WordTrace]
  refine ⟨7665857905564853560505591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5110571937043235707003727 7665857905564853560505591)
  ·
    refine ⟨11498786858347280340758387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7665857905564853560505591 11498786858347280340758387)
    ·
      refine ⟨17248180287520920511137581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11498786858347280340758387 17248180287520920511137581)
      ·
        refine ⟨6468067607820345191676593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17248180287520920511137581 6468067607820345191676593)
        ·
          refine ⟨4851050705865258893757445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6468067607820345191676593 4851050705865258893757445)
          ·
            refine ⟨909572007349736042579521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4851050705865258893757445 909572007349736042579521)
            ·
              refine ⟨682179005512302031934641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909572007349736042579521 682179005512302031934641)
              ·
                refine ⟨511634254134226523950981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682179005512302031934641 511634254134226523950981)
                ·
                  refine ⟨95931422650167473240809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511634254134226523950981 95931422650167473240809)
                  ·
                    rfl

theorem cell20_210179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_210179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210179 prefixEnd_210179 := by exact prefixLift 210179
  have htrace : WordTrace (prefixWord ++ tailWord_210179) baseStart_210179 baseEnd_210179 := by
    simpa [prefixWord, tailWord_210179, baseEnd_210179] using wordTrace_append hprefix tailTrace_210179
  have hstable : (prefixWord ++ tailWord_210179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210179).length < 2 ^ (prefixWord ++ tailWord_210179).sum := by decide
  have hdescent : baseEnd_210179 < baseStart_210179 := by decide
  rcases family_descends (prefixWord ++ tailWord_210179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210193 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_210193 : Nat := 118140960795 + 210193 * 2 ^ 59
def prefixEnd_210193 : Nat := 4983230072969 + 3 ^ 40 * 210193 * 2
def baseEnd_210193 : Nat := 95937812631645646774085

theorem tailTrace_210193 : CollatzResearch.WordTrace tailWord_210193 prefixEnd_210193 95937812631645646774085 := by
  unfold tailWord_210193
  simp only [CollatzResearch.WordTrace]
  refine ⟨7666368527514133951515233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5110912351676089301010155 7666368527514133951515233)
  ·
    refine ⟨5749776395635600463636425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7666368527514133951515233 5749776395635600463636425)
    ·
      refine ⟨4312332296726700347727319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5749776395635600463636425 4312332296726700347727319)
      ·
        refine ⟨6468498445090050521590979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312332296726700347727319 6468498445090050521590979)
        ·
          refine ⟨9702747667635075782386469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6468498445090050521590979 9702747667635075782386469)
          ·
            refine ⟨1819265187681576709197463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9702747667635075782386469 1819265187681576709197463)
            ·
              refine ⟨2728897781522365063796195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819265187681576709197463 2728897781522365063796195)
              ·
                refine ⟨4093346672283547595694293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728897781522365063796195 4093346672283547595694293)
                ·
                  refine ⟨95937812631645646774085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4093346672283547595694293 95937812631645646774085)
                  ·
                    rfl

theorem cell20_210193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_210193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210193 prefixEnd_210193 := by exact prefixLift 210193
  have htrace : WordTrace (prefixWord ++ tailWord_210193) baseStart_210193 baseEnd_210193 := by
    simpa [prefixWord, tailWord_210193, baseEnd_210193] using wordTrace_append hprefix tailTrace_210193
  have hstable : (prefixWord ++ tailWord_210193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210193).length < 2 ^ (prefixWord ++ tailWord_210193).sum := by decide
  have hdescent : baseEnd_210193 < baseStart_210193 := by decide
  rcases family_descends (prefixWord ++ tailWord_210193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210224 : List Nat := [2, 1, 1, 1, 2, 2, 6, 5]
def baseStart_210224 : Nat := 118140960795 + 210224 * 2 ^ 59
def prefixEnd_210224 : Nat := 4983230072969 + 3 ^ 40 * 210224 * 2
def baseEnd_210224 : Nat := 31983987292115772246875

theorem tailTrace_210224 : CollatzResearch.WordTrace tailWord_210224 prefixEnd_210224 31983987292115772246875 := by
  unfold tailWord_210224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833749595200913122946863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5111666126934550830595817 3833749595200913122946863)
  ·
    refine ⟨5750624392801369684420295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3833749595200913122946863 5750624392801369684420295)
    ·
      refine ⟨8625936589202054526630443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5750624392801369684420295 8625936589202054526630443)
      ·
        refine ⟨12938904883803081789945665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8625936589202054526630443 12938904883803081789945665)
        ·
          refine ⟨9704178662852311342459249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12938904883803081789945665 9704178662852311342459249)
          ·
            refine ⟨7278133997139233506844437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9704178662852311342459249 7278133997139233506844437)
            ·
              refine ⟨341162531115901570633333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7278133997139233506844437 341162531115901570633333)
              ·
                refine ⟨31983987292115772246875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341162531115901570633333 31983987292115772246875)
                ·
                  rfl

theorem cell20_210224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_210224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210224 prefixEnd_210224 := by exact prefixLift 210224
  have htrace : WordTrace (prefixWord ++ tailWord_210224) baseStart_210224 baseEnd_210224 := by
    simpa [prefixWord, tailWord_210224, baseEnd_210224] using wordTrace_append hprefix tailTrace_210224
  have hstable : (prefixWord ++ tailWord_210224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210224).length < 2 ^ (prefixWord ++ tailWord_210224).sum := by decide
  have hdescent : baseEnd_210224 < baseStart_210224 := by decide
  rcases family_descends (prefixWord ++ tailWord_210224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210227 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 3]
def baseStart_210227 : Nat := 118140960795 + 210227 * 2 ^ 59
def prefixEnd_210227 : Nat := 4983230072969 + 3 ^ 40 * 210227 * 2
def baseEnd_210227 : Nat := 95953331158092639640613

theorem tailTrace_210227 : CollatzResearch.WordTrace tailWord_210227 prefixEnd_210227 95953331158092639640613 := by
  unfold tailWord_210227
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667608609390957758252935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5111739072927305172168623 7667608609390957758252935)
  ·
    refine ⟨11501412914086436637379403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7667608609390957758252935 11501412914086436637379403)
    ·
      refine ⟨17252119371129654956069105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11501412914086436637379403 17252119371129654956069105)
      ·
        refine ⟨12939089528347241217051829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17252119371129654956069105 12939089528347241217051829)
        ·
          refine ⟨1213039643282553864098609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12939089528347241217051829 1213039643282553864098609)
          ·
            refine ⟨909779732461915398073957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213039643282553864098609 909779732461915398073957)
            ·
              refine ⟨170583699836609137138867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 909779732461915398073957 170583699836609137138867)
              ·
                refine ⟨255875549754913705708301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170583699836609137138867 255875549754913705708301)
                ·
                  refine ⟨95953331158092639640613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255875549754913705708301 95953331158092639640613)
                  ·
                    rfl

theorem cell20_210227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 3].length) (baseStart_210227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210227 prefixEnd_210227 := by exact prefixLift 210227
  have htrace : WordTrace (prefixWord ++ tailWord_210227) baseStart_210227 baseEnd_210227 := by
    simpa [prefixWord, tailWord_210227, baseEnd_210227] using wordTrace_append hprefix tailTrace_210227
  have hstable : (prefixWord ++ tailWord_210227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210227).length < 2 ^ (prefixWord ++ tailWord_210227).sum := by decide
  have hdescent : baseEnd_210227 < baseStart_210227 := by decide
  rcases family_descends (prefixWord ++ tailWord_210227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210241 : List Nat := [1, 2, 5, 2, 1, 1, 2, 6]
def baseStart_210241 : Nat := 118140960795 + 210241 * 2 ^ 59
def prefixEnd_210241 : Nat := 4983230072969 + 3 ^ 40 * 210241 * 2
def baseEnd_210241 : Nat := 31986573713190271057963

theorem tailTrace_210241 : CollatzResearch.WordTrace tailWord_210241 prefixEnd_210241 31986573713190271057963 := by
  unfold tailWord_210241
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668119231340238149262577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5112079487560158766175051 7668119231340238149262577)
  ·
    refine ⟨5751089423505178611946933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7668119231340238149262577 5751089423505178611946933)
    ·
      refine ⟨539164633453610494870025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5751089423505178611946933 539164633453610494870025)
      ·
        refine ⟨404373475090207871152519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539164633453610494870025 404373475090207871152519)
        ·
          refine ⟨606560212635311806728779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404373475090207871152519 606560212635311806728779)
          ·
            refine ⟨909840318952967710093169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606560212635311806728779 909840318952967710093169)
            ·
              refine ⟨682380239214725782569877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909840318952967710093169 682380239214725782569877)
              ·
                refine ⟨31986573713190271057963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 682380239214725782569877 31986573713190271057963)
                ·
                  rfl

theorem cell20_210241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_210241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210241 prefixEnd_210241 := by exact prefixLift 210241
  have htrace : WordTrace (prefixWord ++ tailWord_210241) baseStart_210241 baseEnd_210241 := by
    simpa [prefixWord, tailWord_210241, baseEnd_210241] using wordTrace_append hprefix tailTrace_210241
  have hstable : (prefixWord ++ tailWord_210241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210241).length < 2 ^ (prefixWord ++ tailWord_210241).sum := by decide
  have hdescent : baseEnd_210241 < baseStart_210241 := by decide
  rcases family_descends (prefixWord ++ tailWord_210241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210306 : List Nat := [3, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_210306 : Nat := 118140960795 + 210306 * 2 ^ 59
def prefixEnd_210306 : Nat := 4983230072969 + 3 ^ 40 * 210306 * 2
def baseEnd_210306 : Nat := 95989388910719476006957

theorem tailTrace_210306 : CollatzResearch.WordTrace tailWord_210306 prefixEnd_210306 95989388910719476006957 := by
  unfold tailWord_210306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917622494026188562594693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5113659984069836166919181 1917622494026188562594693)
  ·
    refine ⟨359554217629910355486505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1917622494026188562594693 359554217629910355486505)
    ·
      refine ⟨269665663222432766614879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359554217629910355486505 269665663222432766614879)
      ·
        refine ⟨404498494833649149922319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269665663222432766614879 404498494833649149922319)
        ·
          refine ⟨606747742250473724883479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404498494833649149922319 606747742250473724883479)
          ·
            refine ⟨910121613375710587325219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606747742250473724883479 910121613375710587325219)
            ·
              refine ⟨1365182420063565880987829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910121613375710587325219 1365182420063565880987829)
              ·
                refine ⟨127985851880959301342609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1365182420063565880987829 127985851880959301342609)
                ·
                  refine ⟨95989388910719476006957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127985851880959301342609 95989388910719476006957)
                  ·
                    rfl

theorem cell20_210306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_210306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210306 prefixEnd_210306 := by exact prefixLift 210306
  have htrace : WordTrace (prefixWord ++ tailWord_210306) baseStart_210306 baseEnd_210306 := by
    simpa [prefixWord, tailWord_210306, baseEnd_210306] using wordTrace_append hprefix tailTrace_210306
  have hstable : (prefixWord ++ tailWord_210306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210306).length < 2 ^ (prefixWord ++ tailWord_210306).sum := by decide
  have hdescent : baseEnd_210306 < baseStart_210306 := by decide
  rcases family_descends (prefixWord ++ tailWord_210306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210352 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_210352 : Nat := 118140960795 + 210352 * 2 ^ 59
def prefixEnd_210352 : Nat := 4983230072969 + 3 ^ 40 * 210352 * 2
def baseEnd_210352 : Nat := 96010384564147760473435

theorem tailTrace_210352 : CollatzResearch.WordTrace tailWord_210352 prefixEnd_210352 96010384564147760473435 := by
  unfold tailWord_210352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836083866969052053276655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5114778489292069404368873 3836083866969052053276655)
  ·
    refine ⟨5754125800453578079914983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3836083866969052053276655 5754125800453578079914983)
    ·
      refine ⟨8631188700680367119872475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754125800453578079914983 8631188700680367119872475)
      ·
        refine ⟨12946783051020550679808713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631188700680367119872475 12946783051020550679808713)
        ·
          refine ⟨9710087288265413009856535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12946783051020550679808713 9710087288265413009856535)
          ·
            refine ⟨14565130932398119514784803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710087288265413009856535 14565130932398119514784803)
            ·
              refine ⟨21847696398597179272177205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14565130932398119514784803 21847696398597179272177205)
              ·
                refine ⟨2048221537368485556766613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21847696398597179272177205 2048221537368485556766613)
                ·
                  refine ⟨96010384564147760473435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2048221537368485556766613 96010384564147760473435)
                  ·
                    rfl

theorem cell20_210352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_210352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210352 prefixEnd_210352 := by exact prefixLift 210352
  have htrace : WordTrace (prefixWord ++ tailWord_210352) baseStart_210352 baseEnd_210352 := by
    simpa [prefixWord, tailWord_210352, baseEnd_210352] using wordTrace_append hprefix tailTrace_210352
  have hstable : (prefixWord ++ tailWord_210352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210352).length < 2 ^ (prefixWord ++ tailWord_210352).sum := by decide
  have hdescent : baseEnd_210352 < baseStart_210352 := by decide
  rcases family_descends (prefixWord ++ tailWord_210352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210383 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_210383 : Nat := 118140960795 + 210383 * 2 ^ 59
def prefixEnd_210383 : Nat := 4983230072969 + 3 ^ 40 * 210383 * 2
def baseEnd_210383 : Nat := 96024533808849430439975

theorem tailTrace_210383 : CollatzResearch.WordTrace tailWord_210383 prefixEnd_210383 96024533808849430439975 := by
  unfold tailWord_210383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7673298396825796400931803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5115532264550530933954535 7673298396825796400931803)
  ·
    refine ⟨11509947595238694601397705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7673298396825796400931803 11509947595238694601397705)
    ·
      refine ⟨8632460696429020951048279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11509947595238694601397705 8632460696429020951048279)
      ·
        refine ⟨12948691044643531426572419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8632460696429020951048279 12948691044643531426572419)
        ·
          refine ⟨19423036566965297139858629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12948691044643531426572419 19423036566965297139858629)
          ·
            refine ⟨3641819356305993213723493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19423036566965297139858629 3641819356305993213723493)
            ·
              refine ⟨682841129307373727573155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3641819356305993213723493 682841129307373727573155)
              ·
                refine ⟨1024261693961060591359733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682841129307373727573155 1024261693961060591359733)
                ·
                  refine ⟨96024533808849430439975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1024261693961060591359733 96024533808849430439975)
                  ·
                    rfl

theorem cell20_210383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_210383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210383 prefixEnd_210383 := by exact prefixLift 210383
  have htrace : WordTrace (prefixWord ++ tailWord_210383) baseStart_210383 baseEnd_210383 := by
    simpa [prefixWord, tailWord_210383, baseEnd_210383] using wordTrace_append hprefix tailTrace_210383
  have hstable : (prefixWord ++ tailWord_210383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210383).length < 2 ^ (prefixWord ++ tailWord_210383).sum := by decide
  have hdescent : baseEnd_210383 < baseStart_210383 := by decide
  rcases family_descends (prefixWord ++ tailWord_210383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210414 : List Nat := [4, 1, 2, 1, 2, 1, 1, 8]
def baseStart_210414 : Nat := 118140960795 + 210414 * 2 ^ 59
def prefixEnd_210414 : Nat := 4983230072969 + 3 ^ 40 * 210414 * 2
def baseEnd_210414 : Nat := 32012894351183700135505

theorem tailTrace_210414 : CollatzResearch.WordTrace tailWord_210414 prefixEnd_210414 32012894351183700135505 := by
  unfold tailWord_210414
  simp only [CollatzResearch.WordTrace]
  refine ⟨959303632464186086913787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5116286039808992463540197 959303632464186086913787)
  ·
    refine ⟨1438955448696279130370681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959303632464186086913787 1438955448696279130370681)
    ·
      refine ⟨1079216586522209347778011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1438955448696279130370681 1079216586522209347778011)
      ·
        refine ⟨1618824879783314021667017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079216586522209347778011 1618824879783314021667017)
        ·
          refine ⟨1214118659837485516250263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1618824879783314021667017 1214118659837485516250263)
          ·
            refine ⟨1821177989756228274375395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214118659837485516250263 1821177989756228274375395)
            ·
              refine ⟨2731766984634342411563093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821177989756228274375395 2731766984634342411563093)
              ·
                refine ⟨32012894351183700135505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2731766984634342411563093 32012894351183700135505)
                ·
                  rfl

theorem cell20_210414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_210414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210414 prefixEnd_210414 := by exact prefixLift 210414
  have htrace : WordTrace (prefixWord ++ tailWord_210414) baseStart_210414 baseEnd_210414 := by
    simpa [prefixWord, tailWord_210414, baseEnd_210414] using wordTrace_append hprefix tailTrace_210414
  have hstable : (prefixWord ++ tailWord_210414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210414).length < 2 ^ (prefixWord ++ tailWord_210414).sum := by decide
  have hdescent : baseEnd_210414 < baseStart_210414 := by decide
  rcases family_descends (prefixWord ++ tailWord_210414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210434 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_210434 : Nat := 118140960795 + 210434 * 2 ^ 59
def prefixEnd_210434 : Nat := 4983230072969 + 3 ^ 40 * 210434 * 2
def baseEnd_210434 : Nat := 96047811598519919739767

theorem tailTrace_210434 : CollatzResearch.WordTrace tailWord_210434 prefixEnd_210434 96047811598519919739767 := by
  unfold tailWord_210434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918789629910258027759589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5116772346427354740692237 1918789629910258027759589)
  ·
    refine ⟨359773055608173380204923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1918789629910258027759589 359773055608173380204923)
    ·
      refine ⟨539659583412260070307385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359773055608173380204923 539659583412260070307385)
      ·
        refine ⟨404744687559195052730539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539659583412260070307385 404744687559195052730539)
        ·
          refine ⟨607117031338792579095809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404744687559195052730539 607117031338792579095809)
          ·
            refine ⟨455337773504094434321857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607117031338792579095809 455337773504094434321857)
            ·
              refine ⟨341503330128070825741393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455337773504094434321857 341503330128070825741393)
              ·
                refine ⟨256127497596053119306045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341503330128070825741393 256127497596053119306045)
                ·
                  refine ⟨96047811598519919739767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256127497596053119306045 96047811598519919739767)
                  ·
                    rfl

theorem cell20_210434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_210434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210434 prefixEnd_210434 := by exact prefixLift 210434
  have htrace : WordTrace (prefixWord ++ tailWord_210434) baseStart_210434 baseEnd_210434 := by
    simpa [prefixWord, tailWord_210434, baseEnd_210434] using wordTrace_append hprefix tailTrace_210434
  have hstable : (prefixWord ++ tailWord_210434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210434).length < 2 ^ (prefixWord ++ tailWord_210434).sum := by decide
  have hdescent : baseEnd_210434 < baseStart_210434 := by decide
  rcases family_descends (prefixWord ++ tailWord_210434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210511 : List Nat := [1, 1, 2, 1, 1, 2, 3, 9]
def baseStart_210511 : Nat := 118140960795 + 210511 * 2 ^ 59
def prefixEnd_210511 : Nat := 4983230072969 + 3 ^ 40 * 210511 * 2
def baseEnd_210511 : Nat := 32027652165549958057595

theorem tailTrace_210511 : CollatzResearch.WordTrace tailWord_210511 prefixEnd_210511 32027652165549958057595 := by
  unfold tailWord_210511
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677966940362074261591387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5118644626908049507727591 7677966940362074261591387)
  ·
    refine ⟨11516950410543111392387081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677966940362074261591387 11516950410543111392387081)
    ·
      refine ⟨8637712807907333544290311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11516950410543111392387081 8637712807907333544290311)
      ·
        refine ⟨12956569211861000316435467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8637712807907333544290311 12956569211861000316435467)
        ·
          refine ⟨19434853817791500474653201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12956569211861000316435467 19434853817791500474653201)
          ·
            refine ⟨14576140363343625355989901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19434853817791500474653201 14576140363343625355989901)
            ·
              refine ⟨5466052636253859508496213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14576140363343625355989901 5466052636253859508496213)
              ·
                refine ⟨32027652165549958057595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5466052636253859508496213 32027652165549958057595)
                ·
                  rfl

theorem cell20_210511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_210511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210511 prefixEnd_210511 := by exact prefixLift 210511
  have htrace : WordTrace (prefixWord ++ tailWord_210511) baseStart_210511 baseEnd_210511 := by
    simpa [prefixWord, tailWord_210511, baseEnd_210511] using wordTrace_append hprefix tailTrace_210511
  have hstable : (prefixWord ++ tailWord_210511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210511).length < 2 ^ (prefixWord ++ tailWord_210511).sum := by decide
  have hdescent : baseEnd_210511 < baseStart_210511 := by decide
  rcases family_descends (prefixWord ++ tailWord_210511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210524 : List Nat := [2, 2, 4, 1, 2, 3, 2, 4]
def baseStart_210524 : Nat := 118140960795 + 210524 * 2 ^ 59
def prefixEnd_210524 : Nat := 4983230072969 + 3 ^ 40 * 210524 * 2
def baseEnd_210524 : Nat := 32029630016959868913133

theorem tailTrace_210524 : CollatzResearch.WordTrace tailWord_210524 prefixEnd_210524 32029630016959868913133 := by
  unfold tailWord_210524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839220544657488740907313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5118960726209984987876417 3839220544657488740907313)
  ·
    refine ⟨2879415408493116555680485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3839220544657488740907313 2879415408493116555680485)
    ·
      refine ⟨539890389092459354190091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2879415408493116555680485 539890389092459354190091)
      ·
        refine ⟨809835583638689031285137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539890389092459354190091 809835583638689031285137)
        ·
          refine ⟨607376687729016773463853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809835583638689031285137 607376687729016773463853)
          ·
            refine ⟨227766257898381290048945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607376687729016773463853 227766257898381290048945)
            ·
              refine ⟨170824693423785967536709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227766257898381290048945 170824693423785967536709)
              ·
                refine ⟨32029630016959868913133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170824693423785967536709 32029630016959868913133)
                ·
                  rfl

theorem cell20_210524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_210524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210524 prefixEnd_210524 := by exact prefixLift 210524
  have htrace : WordTrace (prefixWord ++ tailWord_210524) baseStart_210524 baseEnd_210524 := by
    simpa [prefixWord, tailWord_210524, baseEnd_210524] using wordTrace_append hprefix tailTrace_210524
  have hstable : (prefixWord ++ tailWord_210524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210524).length < 2 ^ (prefixWord ++ tailWord_210524).sum := by decide
  have hdescent : baseEnd_210524 < baseStart_210524 := by decide
  rcases family_descends (prefixWord ++ tailWord_210524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210535 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_210535 : Nat := 118140960795 + 210535 * 2 ^ 59
def prefixEnd_210535 : Nat := 4983230072969 + 3 ^ 40 * 210535 * 2
def baseEnd_210535 : Nat := 96093910750612457372687

theorem tailTrace_210535 : CollatzResearch.WordTrace tailWord_210535 prefixEnd_210535 96093910750612457372687 := by
  unfold tailWord_210535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7678842292275126360465059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5119228194850084240310039 7678842292275126360465059)
  ·
    refine ⟨11518263438412689540697589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7678842292275126360465059 11518263438412689540697589)
    ·
      refine ⟨1079837197351189644440399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11518263438412689540697589 1079837197351189644440399)
      ·
        refine ⟨1619755796026784466660599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079837197351189644440399 1619755796026784466660599)
        ·
          refine ⟨2429633694040176699990899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619755796026784466660599 2429633694040176699990899)
          ·
            refine ⟨3644450541060265049986349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429633694040176699990899 3644450541060265049986349)
            ·
              refine ⟨1366668952897599393744881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3644450541060265049986349 1366668952897599393744881)
              ·
                refine ⟨1025001714673199545308661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366668952897599393744881 1025001714673199545308661)
                ·
                  refine ⟨96093910750612457372687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025001714673199545308661 96093910750612457372687)
                  ·
                    rfl

theorem cell20_210535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_210535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210535 prefixEnd_210535 := by exact prefixLift 210535
  have htrace : WordTrace (prefixWord ++ tailWord_210535) baseStart_210535 baseEnd_210535 := by
    simpa [prefixWord, tailWord_210535, baseEnd_210535] using wordTrace_append hprefix tailTrace_210535
  have hstable : (prefixWord ++ tailWord_210535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210535).length < 2 ^ (prefixWord ++ tailWord_210535).sum := by decide
  have hdescent : baseEnd_210535 < baseStart_210535 := by decide
  rcases family_descends (prefixWord ++ tailWord_210535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210600 : List Nat := [2, 1, 7, 1, 1, 8]
def baseStart_210600 : Nat := 118140960795 + 210600 * 2 ^ 59
def prefixEnd_210600 : Nat := 4983230072969 + 3 ^ 40 * 210600 * 2
def baseEnd_210600 : Nat := 3560132537843004452065

theorem tailTrace_210600 : CollatzResearch.WordTrace tailWord_210600 prefixEnd_210600 3560132537843004452065 := by
  unfold tailWord_210600
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840606518519821230790627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5120808691359761641054169 3840606518519821230790627)
  ·
    refine ⟨5760909777779731846185941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3840606518519821230790627 5760909777779731846185941)
    ·
      refine ⟨135021322916712465144983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5760909777779731846185941 135021322916712465144983)
      ·
        refine ⟨202531984375068697717475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135021322916712465144983 202531984375068697717475)
        ·
          refine ⟨303797976562603046576213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202531984375068697717475 303797976562603046576213)
          ·
            refine ⟨3560132537843004452065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 303797976562603046576213 3560132537843004452065)
            ·
              rfl

theorem cell20_210600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 8].length) (baseStart_210600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210600 prefixEnd_210600 := by exact prefixLift 210600
  have htrace : WordTrace (prefixWord ++ tailWord_210600) baseStart_210600 baseEnd_210600 := by
    simpa [prefixWord, tailWord_210600, baseEnd_210600] using wordTrace_append hprefix tailTrace_210600
  have hstable : (prefixWord ++ tailWord_210600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210600).length < 2 ^ (prefixWord ++ tailWord_210600).sum := by decide
  have hdescent : baseEnd_210600 < baseStart_210600 := by decide
  rcases family_descends (prefixWord ++ tailWord_210600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210606 : List Nat := [4, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_210606 : Nat := 118140960795 + 210606 * 2 ^ 59
def prefixEnd_210606 : Nat := 4983230072969 + 3 ^ 40 * 210606 * 2
def baseEnd_210606 : Nat := 96126317085251766005731

theorem tailTrace_210606 : CollatzResearch.WordTrace tailWord_210606 prefixEnd_210606 96126317085251766005731 := by
  unfold tailWord_210606
  simp only [CollatzResearch.WordTrace]
  refine ⟨960178984377238185787459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5120954583345270324199781 960178984377238185787459)
  ·
    refine ⟨1440268476565857278681189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960178984377238185787459 1440268476565857278681189)
    ·
      refine ⟨270050339356098239752723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1440268476565857278681189 270050339356098239752723)
      ·
        refine ⟨405075509034147359629085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270050339356098239752723 405075509034147359629085)
        ·
          refine ⟨151903315887805259860907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405075509034147359629085 151903315887805259860907)
          ·
            refine ⟨227854973831707889791361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151903315887805259860907 227854973831707889791361)
            ·
              refine ⟨170891230373780917343521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227854973831707889791361 170891230373780917343521)
              ·
                refine ⟨128168422780335688007641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170891230373780917343521 128168422780335688007641)
                ·
                  refine ⟨96126317085251766005731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128168422780335688007641 96126317085251766005731)
                  ·
                    rfl

theorem cell20_210606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_210606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210606 prefixEnd_210606 := by exact prefixLift 210606
  have htrace : WordTrace (prefixWord ++ tailWord_210606) baseStart_210606 baseEnd_210606 := by
    simpa [prefixWord, tailWord_210606, baseEnd_210606] using wordTrace_append hprefix tailTrace_210606
  have hstable : (prefixWord ++ tailWord_210606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210606).length < 2 ^ (prefixWord ++ tailWord_210606).sum := by decide
  have hdescent : baseEnd_210606 < baseStart_210606 := by decide
  rcases family_descends (prefixWord ++ tailWord_210606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210628 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_210628 : Nat := 118140960795 + 210628 * 2 ^ 59
def prefixEnd_210628 : Nat := 4983230072969 + 3 ^ 40 * 210628 * 2
def baseEnd_210628 : Nat := 96136358484717467272307

theorem tailTrace_210628 : CollatzResearch.WordTrace tailWord_210628 prefixEnd_210628 96136358484717467272307 := by
  unfold tailWord_210628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3841117140469101621800269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5121489520625468829067025 3841117140469101621800269)
  ·
    refine ⟨1440418927675913108175101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3841117140469101621800269 1440418927675913108175101)
    ·
      refine ⟨540157097878467415565663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1440418927675913108175101 540157097878467415565663)
      ·
        refine ⟨810235646817701123348495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540157097878467415565663 810235646817701123348495)
        ·
          refine ⟨1215353470226551685022743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810235646817701123348495 1215353470226551685022743)
          ·
            refine ⟨1823030205339827527534115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215353470226551685022743 1823030205339827527534115)
            ·
              refine ⟨2734545308009741291301173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823030205339827527534115 2734545308009741291301173)
              ·
                refine ⟨256363622625913246059485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2734545308009741291301173 256363622625913246059485)
                ·
                  refine ⟨96136358484717467272307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256363622625913246059485 96136358484717467272307)
                  ·
                    rfl

theorem cell20_210628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_210628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210628 prefixEnd_210628 := by exact prefixLift 210628
  have htrace : WordTrace (prefixWord ++ tailWord_210628) baseStart_210628 baseEnd_210628 := by
    simpa [prefixWord, tailWord_210628, baseEnd_210628] using wordTrace_append hprefix tailTrace_210628
  have hstable : (prefixWord ++ tailWord_210628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210628).length < 2 ^ (prefixWord ++ tailWord_210628).sum := by decide
  have hdescent : baseEnd_210628 < baseStart_210628 := by decide
  rcases family_descends (prefixWord ++ tailWord_210628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210666 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_210666 : Nat := 118140960795 + 210666 * 2 ^ 59
def prefixEnd_210666 : Nat := 4983230072969 + 3 ^ 40 * 210666 * 2
def baseEnd_210666 : Nat := 96153702720158224005485

theorem tailTrace_210666 : CollatzResearch.WordTrace tailWord_210666 prefixEnd_210666 96153702720158224005485 := by
  unfold tailWord_210666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920905063700133933370963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5122413503200357155655901 1920905063700133933370963)
  ·
    refine ⟨2881357595550200900056445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1920905063700133933370963 2881357595550200900056445)
    ·
      refine ⟨1080509098331325337521167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2881357595550200900056445 1080509098331325337521167)
      ·
        refine ⟨1620763647496988006281751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080509098331325337521167 1620763647496988006281751)
        ·
          refine ⟨2431145471245482009422627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620763647496988006281751 2431145471245482009422627)
          ·
            refine ⟨3646718206868223014133941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431145471245482009422627 3646718206868223014133941)
            ·
              refine ⟨341879831893895907575057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3646718206868223014133941 341879831893895907575057)
              ·
                refine ⟨256409873920421930681293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341879831893895907575057 256409873920421930681293)
                ·
                  refine ⟨96153702720158224005485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256409873920421930681293 96153702720158224005485)
                  ·
                    rfl

theorem cell20_210666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_210666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210666 prefixEnd_210666 := by exact prefixLift 210666
  have htrace : WordTrace (prefixWord ++ tailWord_210666) baseStart_210666 baseEnd_210666 := by
    simpa [prefixWord, tailWord_210666, baseEnd_210666] using wordTrace_append hprefix tailTrace_210666
  have hstable : (prefixWord ++ tailWord_210666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210666).length < 2 ^ (prefixWord ++ tailWord_210666).sum := by decide
  have hdescent : baseEnd_210666 < baseStart_210666 := by decide
  rcases family_descends (prefixWord ++ tailWord_210666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210673 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_210673 : Nat := 118140960795 + 210673 * 2 ^ 59
def prefixEnd_210673 : Nat := 4983230072969 + 3 ^ 40 * 210673 * 2
def baseEnd_210673 : Nat := 96156897710897310772123

theorem tailTrace_210673 : CollatzResearch.WordTrace tailWord_210673 prefixEnd_210673 96156897710897310772123 := by
  unfold tailWord_210673
  simp only [CollatzResearch.WordTrace]
  refine ⟨7683875565775175928988673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5122583710516783952659115 7683875565775175928988673)
  ·
    refine ⟨5762906674331381946741505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7683875565775175928988673 5762906674331381946741505)
    ·
      refine ⟨4322180005748536460056129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5762906674331381946741505 4322180005748536460056129)
      ·
        refine ⟨3241635004311402345042097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4322180005748536460056129 3241635004311402345042097)
        ·
          refine ⟨2431226253233551758781573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3241635004311402345042097 2431226253233551758781573)
          ·
            refine ⟨455854922481290954771545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2431226253233551758781573 455854922481290954771545)
            ·
              refine ⟨341891191860968216078659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455854922481290954771545 341891191860968216078659)
              ·
                refine ⟨512836787791452324117989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341891191860968216078659 512836787791452324117989)
                ·
                  refine ⟨96156897710897310772123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512836787791452324117989 96156897710897310772123)
                  ·
                    rfl

theorem cell20_210673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_210673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210673 prefixEnd_210673 := by exact prefixLift 210673
  have htrace : WordTrace (prefixWord ++ tailWord_210673) baseStart_210673 baseEnd_210673 := by
    simpa [prefixWord, tailWord_210673, baseEnd_210673] using wordTrace_append hprefix tailTrace_210673
  have hstable : (prefixWord ++ tailWord_210673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210673).length < 2 ^ (prefixWord ++ tailWord_210673).sum := by decide
  have hdescent : baseEnd_210673 < baseStart_210673 := by decide
  rcases family_descends (prefixWord ++ tailWord_210673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210687 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 3]
def baseStart_210687 : Nat := 118140960795 + 210687 * 2 ^ 59
def prefixEnd_210687 : Nat := 4983230072969 + 3 ^ 40 * 210687 * 2
def baseEnd_210687 : Nat := 96163287692375484305399

theorem tailTrace_210687 : CollatzResearch.WordTrace tailWord_210687 prefixEnd_210687 96163287692375484305399 := by
  unfold tailWord_210687
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684386187724456319998315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5122924125149637546665543 7684386187724456319998315)
  ·
    refine ⟨11526579281586684479997473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7684386187724456319998315 11526579281586684479997473)
    ·
      refine ⟨8644934461190013359998105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11526579281586684479997473 8644934461190013359998105)
      ·
        refine ⟨6483700845892510019998579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8644934461190013359998105 6483700845892510019998579)
        ·
          refine ⟨9725551268838765029997869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6483700845892510019998579 9725551268838765029997869)
          ·
            refine ⟨3647081725814536886249201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9725551268838765029997869 3647081725814536886249201)
            ·
              refine ⟨2735311294360902664686901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647081725814536886249201 2735311294360902664686901)
              ·
                refine ⟨256435433846334624814397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2735311294360902664686901 256435433846334624814397)
                ·
                  refine ⟨96163287692375484305399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256435433846334624814397 96163287692375484305399)
                  ·
                    rfl

theorem cell20_210687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_210687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210687 prefixEnd_210687 := by exact prefixLift 210687
  have htrace : WordTrace (prefixWord ++ tailWord_210687) baseStart_210687 baseEnd_210687 := by
    simpa [prefixWord, tailWord_210687, baseEnd_210687] using wordTrace_append hprefix tailTrace_210687
  have hstable : (prefixWord ++ tailWord_210687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210687).length < 2 ^ (prefixWord ++ tailWord_210687).sum := by decide
  have hdescent : baseEnd_210687 < baseStart_210687 := by decide
  rcases family_descends (prefixWord ++ tailWord_210687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210725 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_210725 : Nat := 118140960795 + 210725 * 2 ^ 59
def prefixEnd_210725 : Nat := 4983230072969 + 3 ^ 40 * 210725 * 2
def baseEnd_210725 : Nat := 96180631927816241038577

theorem tailTrace_210725 : CollatzResearch.WordTrace tailWord_210725 prefixEnd_210725 96180631927816241038577 := by
  unfold tailWord_210725
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685772161586788809881629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5123848107724525873254419 7685772161586788809881629)
  ·
    refine ⟨2882164560595045803705611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7685772161586788809881629 2882164560595045803705611)
    ·
      refine ⟨4323246840892568705558417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882164560595045803705611 4323246840892568705558417)
      ·
        refine ⟨3242435130669426529168813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323246840892568705558417 3242435130669426529168813)
        ·
          refine ⟨1215913174001034948438305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3242435130669426529168813 1215913174001034948438305)
          ·
            refine ⟨911934880500776211328729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215913174001034948438305 911934880500776211328729)
            ·
              refine ⟨683951160375582158496547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911934880500776211328729 683951160375582158496547)
              ·
                refine ⟨1025926740563373237744821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683951160375582158496547 1025926740563373237744821)
                ·
                  refine ⟨96180631927816241038577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025926740563373237744821 96180631927816241038577)
                  ·
                    rfl

theorem cell20_210725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_210725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210725 prefixEnd_210725 := by exact prefixLift 210725
  have htrace : WordTrace (prefixWord ++ tailWord_210725) baseStart_210725 baseEnd_210725 := by
    simpa [prefixWord, tailWord_210725, baseEnd_210725] using wordTrace_append hprefix tailTrace_210725
  have hstable : (prefixWord ++ tailWord_210725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210725).length < 2 ^ (prefixWord ++ tailWord_210725).sum := by decide
  have hdescent : baseEnd_210725 < baseStart_210725 := by decide
  rcases family_descends (prefixWord ++ tailWord_210725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210728 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_210728 : Nat := 118140960795 + 210728 * 2 ^ 59
def prefixEnd_210728 : Nat := 4983230072969 + 3 ^ 40 * 210728 * 2
def baseEnd_210728 : Nat := 96182001209561563938565

theorem tailTrace_210728 : CollatzResearch.WordTrace tailWord_210728 prefixEnd_210728 96182001209561563938565 := by
  unfold tailWord_210728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842940790287960161120419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5123921053717280214827225 3842940790287960161120419)
  ·
    refine ⟨5764411185431940241680629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3842940790287960161120419 5764411185431940241680629)
    ·
      refine ⟨540413548634244397657559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5764411185431940241680629 540413548634244397657559)
      ·
        refine ⟨810620322951366596486339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540413548634244397657559 810620322951366596486339)
        ·
          refine ⟨1215930484427049894729509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810620322951366596486339 1215930484427049894729509)
          ·
            refine ⟨227986965830071855261783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1215930484427049894729509 227986965830071855261783)
            ·
              refine ⟨341980448745107782892675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227986965830071855261783 341980448745107782892675)
              ·
                refine ⟨512970673117661674339013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341980448745107782892675 512970673117661674339013)
                ·
                  refine ⟨96182001209561563938565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512970673117661674339013 96182001209561563938565)
                  ·
                    rfl

theorem cell20_210728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_210728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210728 prefixEnd_210728 := by exact prefixLift 210728
  have htrace : WordTrace (prefixWord ++ tailWord_210728) baseStart_210728 baseEnd_210728 := by
    simpa [prefixWord, tailWord_210728, baseEnd_210728] using wordTrace_append hprefix tailTrace_210728
  have hstable : (prefixWord ++ tailWord_210728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210728).length < 2 ^ (prefixWord ++ tailWord_210728).sum := by decide
  have hdescent : baseEnd_210728 < baseStart_210728 := by decide
  rcases family_descends (prefixWord ++ tailWord_210728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210783 : List Nat := [1, 1, 2, 3, 1, 6, 2, 2, 2]
def baseStart_210783 : Nat := 118140960795 + 210783 * 2 ^ 59
def prefixEnd_210783 : Nat := 4983230072969 + 3 ^ 40 * 210783 * 2
def baseEnd_210783 : Nat := 96207104708225817105007

theorem tailTrace_210783 : CollatzResearch.WordTrace tailWord_210783 prefixEnd_210783 96207104708225817105007 := by
  unfold tailWord_210783
  simp only [CollatzResearch.WordTrace]
  refine ⟨7687887595376664715493003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5125258396917776476995335 7687887595376664715493003)
  ·
    refine ⟨11531831393064997073239505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7687887595376664715493003 11531831393064997073239505)
    ·
      refine ⟨8648873544798747804929629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11531831393064997073239505 8648873544798747804929629)
      ·
        refine ⟨3243327579299530426848611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8648873544798747804929629 3243327579299530426848611)
        ·
          refine ⟨4864991368949295640272917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243327579299530426848611 4864991368949295640272917)
          ·
            refine ⟨228046470419498233137793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4864991368949295640272917 228046470419498233137793)
            ·
              refine ⟨171034852814623674853345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228046470419498233137793 171034852814623674853345)
              ·
                refine ⟨128276139610967756140009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171034852814623674853345 128276139610967756140009)
                ·
                  refine ⟨96207104708225817105007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128276139610967756140009 96207104708225817105007)
                  ·
                    rfl

theorem cell20_210783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 2].length) (baseStart_210783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210783 prefixEnd_210783 := by exact prefixLift 210783
  have htrace : WordTrace (prefixWord ++ tailWord_210783) baseStart_210783 baseEnd_210783 := by
    simpa [prefixWord, tailWord_210783, baseEnd_210783] using wordTrace_append hprefix tailTrace_210783
  have hstable : (prefixWord ++ tailWord_210783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210783).length < 2 ^ (prefixWord ++ tailWord_210783).sum := by decide
  have hdescent : baseEnd_210783 < baseStart_210783 := by decide
  rcases family_descends (prefixWord ++ tailWord_210783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210801 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 3]
def baseStart_210801 : Nat := 118140960795 + 210801 * 2 ^ 59
def prefixEnd_210801 : Nat := 4983230072969 + 3 ^ 40 * 210801 * 2
def baseEnd_210801 : Nat := 96215320398697754504933

theorem tailTrace_210801 : CollatzResearch.WordTrace tailWord_210801 prefixEnd_210801 96215320398697754504933 := by
  unfold tailWord_210801
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688544109311453789648257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5125696072874302526432171 7688544109311453789648257)
  ·
    refine ⟨5766408081983590342236193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7688544109311453789648257 5766408081983590342236193)
    ·
      refine ⟨4324806061487692756677145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5766408081983590342236193 4324806061487692756677145)
      ·
        refine ⟨3243604546115769567507859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324806061487692756677145 3243604546115769567507859)
        ·
          refine ⟨4865406819173654351261789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243604546115769567507859 4865406819173654351261789)
          ·
            refine ⟨1824527557190120381723171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4865406819173654351261789 1824527557190120381723171)
            ·
              refine ⟨2736791335785180572584757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824527557190120381723171 2736791335785180572584757)
              ·
                refine ⟨256574187729860678679821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2736791335785180572584757 256574187729860678679821)
                ·
                  refine ⟨96215320398697754504933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256574187729860678679821 96215320398697754504933)
                  ·
                    rfl

theorem cell20_210801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_210801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210801 prefixEnd_210801 := by exact prefixLift 210801
  have htrace : WordTrace (prefixWord ++ tailWord_210801) baseStart_210801 baseEnd_210801 := by
    simpa [prefixWord, tailWord_210801, baseEnd_210801] using wordTrace_append hprefix tailTrace_210801
  have hstable : (prefixWord ++ tailWord_210801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210801).length < 2 ^ (prefixWord ++ tailWord_210801).sum := by decide
  have hdescent : baseEnd_210801 < baseStart_210801 := by decide
  rcases family_descends (prefixWord ++ tailWord_210801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210838 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_210838 : Nat := 118140960795 + 210838 * 2 ^ 59
def prefixEnd_210838 : Nat := 4983230072969 + 3 ^ 40 * 210838 * 2
def baseEnd_210838 : Nat := 96232208206890070271449

theorem tailTrace_210838 : CollatzResearch.WordTrace tailWord_210838 prefixEnd_210838 96232208206890070271449 := by
  unfold tailWord_210838
  simp only [CollatzResearch.WordTrace]
  refine ⟨480618350636088069296573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5126595740118272739163445 480618350636088069296573)
  ·
    refine ⟨180231881488533025986215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 480618350636088069296573 180231881488533025986215)
    ·
      refine ⟨270347822232799538979323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180231881488533025986215 270347822232799538979323)
      ·
        refine ⟨405521733349199308468985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270347822232799538979323 405521733349199308468985)
        ·
          refine ⟨304141300011899481351739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405521733349199308468985 304141300011899481351739)
          ·
            refine ⟨456211950017849222027609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304141300011899481351739 456211950017849222027609)
            ·
              refine ⟨342158962513386916520707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456211950017849222027609 342158962513386916520707)
              ·
                refine ⟨513238443770080374781061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342158962513386916520707 513238443770080374781061)
                ·
                  refine ⟨96232208206890070271449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513238443770080374781061 96232208206890070271449)
                  ·
                    rfl

theorem cell20_210838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_210838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210838 prefixEnd_210838 := by exact prefixLift 210838
  have htrace : WordTrace (prefixWord ++ tailWord_210838) baseStart_210838 baseEnd_210838 := by
    simpa [prefixWord, tailWord_210838, baseEnd_210838] using wordTrace_append hprefix tailTrace_210838
  have hstable : (prefixWord ++ tailWord_210838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210838).length < 2 ^ (prefixWord ++ tailWord_210838).sum := by decide
  have hdescent : baseEnd_210838 < baseStart_210838 := by decide
  rcases family_descends (prefixWord ++ tailWord_210838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210839 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_210839 : Nat := 118140960795 + 210839 * 2 ^ 59
def prefixEnd_210839 : Nat := 4983230072969 + 3 ^ 40 * 210839 * 2
def baseEnd_210839 : Nat := 96232664634138511238111

theorem tailTrace_210839 : CollatzResearch.WordTrace tailWord_210839 prefixEnd_210839 96232664634138511238111 := by
  unfold tailWord_210839
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689930083173786279531571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5126620055449190853021047 7689930083173786279531571)
  ·
    refine ⟨11534895124760679419297357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7689930083173786279531571 11534895124760679419297357)
    ·
      refine ⟨4325585671785254782236509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11534895124760679419297357 4325585671785254782236509)
      ·
        refine ⟨1622094626919470543338691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4325585671785254782236509 1622094626919470543338691)
        ·
          refine ⟨2433141940379205815008037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622094626919470543338691 2433141940379205815008037)
          ·
            refine ⟨456214113821101090314007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2433141940379205815008037 456214113821101090314007)
            ·
              refine ⟨684321170731651635471011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456214113821101090314007 684321170731651635471011)
              ·
                refine ⟨1026481756097477453206517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684321170731651635471011 1026481756097477453206517)
                ·
                  refine ⟨96232664634138511238111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1026481756097477453206517 96232664634138511238111)
                  ·
                    rfl

theorem cell20_210839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_210839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210839 prefixEnd_210839 := by exact prefixLift 210839
  have htrace : WordTrace (prefixWord ++ tailWord_210839) baseStart_210839 baseEnd_210839 := by
    simpa [prefixWord, tailWord_210839, baseEnd_210839] using wordTrace_append hprefix tailTrace_210839
  have hstable : (prefixWord ++ tailWord_210839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210839).length < 2 ^ (prefixWord ++ tailWord_210839).sum := by decide
  have hdescent : baseEnd_210839 < baseStart_210839 := by decide
  rcases family_descends (prefixWord ++ tailWord_210839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210842 : List Nat := [3, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_210842 : Nat := 118140960795 + 210842 * 2 ^ 59
def prefixEnd_210842 : Nat := 4983230072969 + 3 ^ 40 * 210842 * 2
def baseEnd_210842 : Nat := 96234033915883834138099

theorem tailTrace_210842 : CollatzResearch.WordTrace tailWord_210842 prefixEnd_210842 96234033915883834138099 := by
  unfold tailWord_210842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922509875540729447972695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5126693001441945194593853 1922509875540729447972695)
  ·
    refine ⟨2883764813311094171959043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922509875540729447972695 2883764813311094171959043)
    ·
      refine ⟨4325647219966641257938565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883764813311094171959043 4325647219966641257938565)
      ·
        refine ⟨811058853743745235863481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4325647219966641257938565 811058853743745235863481)
        ·
          refine ⟨608294140307808926897611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811058853743745235863481 608294140307808926897611)
          ·
            refine ⟨912441210461713390346417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608294140307808926897611 912441210461713390346417)
            ·
              refine ⟨684330907846285042759813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912441210461713390346417 684330907846285042759813)
              ·
                refine ⟨128312045221178445517465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684330907846285042759813 128312045221178445517465)
                ·
                  refine ⟨96234033915883834138099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128312045221178445517465 96234033915883834138099)
                  ·
                    rfl

theorem cell20_210842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_210842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210842 prefixEnd_210842 := by exact prefixLift 210842
  have htrace : WordTrace (prefixWord ++ tailWord_210842) baseStart_210842 baseEnd_210842 := by
    simpa [prefixWord, tailWord_210842, baseEnd_210842] using wordTrace_append hprefix tailTrace_210842
  have hstable : (prefixWord ++ tailWord_210842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210842).length < 2 ^ (prefixWord ++ tailWord_210842).sum := by decide
  have hdescent : baseEnd_210842 < baseStart_210842 := by decide
  rcases family_descends (prefixWord ++ tailWord_210842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210860 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_210860 : Nat := 118140960795 + 210860 * 2 ^ 59
def prefixEnd_210860 : Nat := 4983230072969 + 3 ^ 40 * 210860 * 2
def baseEnd_210860 : Nat := 96242249606355771538025

theorem tailTrace_210860 : CollatzResearch.WordTrace tailWord_210860 prefixEnd_210860 96242249606355771538025 := by
  unfold tailWord_210860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845348008048853433023017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5127130677398471244030689 3845348008048853433023017)
  ·
    refine ⟨2884011006036640074767263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3845348008048853433023017 2884011006036640074767263)
    ·
      refine ⟨4326016509054960112150895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884011006036640074767263 4326016509054960112150895)
      ·
        refine ⟨6489024763582440168226343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326016509054960112150895 6489024763582440168226343)
        ·
          refine ⟨9733537145373660252339515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489024763582440168226343 9733537145373660252339515)
          ·
            refine ⟨14600305718060490378509273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9733537145373660252339515 14600305718060490378509273)
            ·
              refine ⟨10950229288545367783881955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14600305718060490378509273 10950229288545367783881955)
              ·
                refine ⟨16425343932818051675822933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10950229288545367783881955 16425343932818051675822933)
                ·
                  refine ⟨96242249606355771538025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16425343932818051675822933 96242249606355771538025)
                  ·
                    rfl

theorem cell20_210860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_210860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210860 prefixEnd_210860 := by exact prefixLift 210860
  have htrace : WordTrace (prefixWord ++ tailWord_210860) baseStart_210860 baseEnd_210860 := by
    simpa [prefixWord, tailWord_210860, baseEnd_210860] using wordTrace_append hprefix tailTrace_210860
  have hstable : (prefixWord ++ tailWord_210860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210860).length < 2 ^ (prefixWord ++ tailWord_210860).sum := by decide
  have hdescent : baseEnd_210860 < baseStart_210860 := by decide
  rcases family_descends (prefixWord ++ tailWord_210860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210862 : List Nat := [4, 1, 5, 1, 1, 2, 2, 4]
def baseStart_210862 : Nat := 118140960795 + 210862 * 2 ^ 59
def prefixEnd_210862 : Nat := 4983230072969 + 3 ^ 40 * 210862 * 2
def baseEnd_210862 : Nat := 32081054153617551157117

theorem tailTrace_210862 : CollatzResearch.WordTrace tailWord_210862 prefixEnd_210862 32081054153617551157117 := by
  unfold tailWord_210862
  simp only [CollatzResearch.WordTrace]
  refine ⟨961346120261307650952355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5127179308060307471745893 961346120261307650952355)
  ·
    refine ⟨1442019180391961476428533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961346120261307650952355 1442019180391961476428533)
    ·
      refine ⟨135189298161746388415175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1442019180391961476428533 135189298161746388415175)
      ·
        refine ⟨202783947242619582622763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135189298161746388415175 202783947242619582622763)
        ·
          refine ⟨304175920863929373934145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202783947242619582622763 304175920863929373934145)
          ·
            refine ⟨228131940647947030450609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304175920863929373934145 228131940647947030450609)
            ·
              refine ⟨171098955485960272837957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228131940647947030450609 171098955485960272837957)
              ·
                refine ⟨32081054153617551157117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171098955485960272837957 32081054153617551157117)
                ·
                  rfl

theorem cell20_210862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_210862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210862 prefixEnd_210862 := by exact prefixLift 210862
  have htrace : WordTrace (prefixWord ++ tailWord_210862) baseStart_210862 baseEnd_210862 := by
    simpa [prefixWord, tailWord_210862, baseEnd_210862] using wordTrace_append hprefix tailTrace_210862
  have hstable : (prefixWord ++ tailWord_210862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210862).length < 2 ^ (prefixWord ++ tailWord_210862).sum := by decide
  have hdescent : baseEnd_210862 < baseStart_210862 := by decide
  rcases family_descends (prefixWord ++ tailWord_210862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210876 : List Nat := [2, 2, 2, 5, 1, 2, 1, 3, 2]
def baseStart_210876 : Nat := 118140960795 + 210876 * 2 ^ 59
def prefixEnd_210876 : Nat := 4983230072969 + 3 ^ 40 * 210876 * 2
def baseEnd_210876 : Nat := 96249552442330827004627

theorem tailTrace_210876 : CollatzResearch.WordTrace tailWord_210876 prefixEnd_210876 96249552442330827004627 := by
  unfold tailWord_210876
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845639792019870799314241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5127519722693161065752321 3845639792019870799314241)
  ·
    refine ⟨2884229844014903099485681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3845639792019870799314241 2884229844014903099485681)
    ·
      refine ⟨2163172383011177324614261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2884229844014903099485681 2163172383011177324614261)
      ·
        refine ⟨202797410907297874182587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2163172383011177324614261 202797410907297874182587)
        ·
          refine ⟨304196116360946811273881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202797410907297874182587 304196116360946811273881)
          ·
            refine ⟨228147087270710108455411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304196116360946811273881 228147087270710108455411)
            ·
              refine ⟨342220630906065162683117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228147087270710108455411 342220630906065162683117)
              ·
                refine ⟨128332736589774436006169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342220630906065162683117 128332736589774436006169)
                ·
                  refine ⟨96249552442330827004627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128332736589774436006169 96249552442330827004627)
                  ·
                    rfl

theorem cell20_210876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_210876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210876 prefixEnd_210876 := by exact prefixLift 210876
  have htrace : WordTrace (prefixWord ++ tailWord_210876) baseStart_210876 baseEnd_210876 := by
    simpa [prefixWord, tailWord_210876, baseEnd_210876] using wordTrace_append hprefix tailTrace_210876
  have hstable : (prefixWord ++ tailWord_210876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210876).length < 2 ^ (prefixWord ++ tailWord_210876).sum := by decide
  have hdescent : baseEnd_210876 < baseStart_210876 := by decide
  rcases family_descends (prefixWord ++ tailWord_210876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210877 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_210877 : Nat := 118140960795 + 210877 * 2 ^ 59
def prefixEnd_210877 : Nat := 4983230072969 + 3 ^ 40 * 210877 * 2
def baseEnd_210877 : Nat := 96250008869579267971289

theorem tailTrace_210877 : CollatzResearch.WordTrace tailWord_210877 prefixEnd_210877 96250008869579267971289 := by
  unfold tailWord_210877
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691316057036118769414885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5127544038024079179609923 7691316057036118769414885)
  ·
    refine ⟨1442121760694272269265291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7691316057036118769414885 1442121760694272269265291)
    ·
      refine ⟨2163182641041408403897937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442121760694272269265291 2163182641041408403897937)
      ·
        refine ⟨1622386980781056302923453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2163182641041408403897937 1622386980781056302923453)
        ·
          refine ⟨608395117792896113596295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1622386980781056302923453 608395117792896113596295)
          ·
            refine ⟨912592676689344170394443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608395117792896113596295 912592676689344170394443)
            ·
              refine ⟨1368889015034016255591665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912592676689344170394443 1368889015034016255591665)
              ·
                refine ⟨1026666761275512191693749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368889015034016255591665 1026666761275512191693749)
                ·
                  refine ⟨96250008869579267971289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1026666761275512191693749 96250008869579267971289)
                  ·
                    rfl

theorem cell20_210877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_210877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210877 prefixEnd_210877 := by exact prefixLift 210877
  have htrace : WordTrace (prefixWord ++ tailWord_210877) baseStart_210877 baseEnd_210877 := by
    simpa [prefixWord, tailWord_210877, baseEnd_210877] using wordTrace_append hprefix tailTrace_210877
  have hstable : (prefixWord ++ tailWord_210877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210877).length < 2 ^ (prefixWord ++ tailWord_210877).sum := by decide
  have hdescent : baseEnd_210877 < baseStart_210877 := by decide
  rcases family_descends (prefixWord ++ tailWord_210877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210901 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_210901 : Nat := 118140960795 + 210901 * 2 ^ 59
def prefixEnd_210901 : Nat := 4983230072969 + 3 ^ 40 * 210901 * 2
def baseEnd_210901 : Nat := 96260963123541851171191

theorem tailTrace_210901 : CollatzResearch.WordTrace tailWord_210901 prefixEnd_210901 96260963123541851171191 := by
  unfold tailWord_210901
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692191408949170868288557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5128127605966113912192371 7692191408949170868288557)
  ·
    refine ⟨2884571778355939075608209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7692191408949170868288557 2884571778355939075608209)
    ·
      refine ⟨2163428833766954306706157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2884571778355939075608209 2163428833766954306706157)
      ·
        refine ⟨811285812662607865014809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2163428833766954306706157 811285812662607865014809)
        ·
          refine ⟨608464359496955898761107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811285812662607865014809 608464359496955898761107)
          ·
            refine ⟨912696539245433848141661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608464359496955898761107 912696539245433848141661)
            ·
              refine ⟨342261202217037693053123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 912696539245433848141661 342261202217037693053123)
              ·
                refine ⟨513391803325556539579685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342261202217037693053123 513391803325556539579685)
                ·
                  refine ⟨96260963123541851171191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513391803325556539579685 96260963123541851171191)
                  ·
                    rfl

theorem cell20_210901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_210901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210901 prefixEnd_210901 := by exact prefixLift 210901
  have htrace : WordTrace (prefixWord ++ tailWord_210901) baseStart_210901 baseEnd_210901 := by
    simpa [prefixWord, tailWord_210901, baseEnd_210901] using wordTrace_append hprefix tailTrace_210901
  have hstable : (prefixWord ++ tailWord_210901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210901).length < 2 ^ (prefixWord ++ tailWord_210901).sum := by decide
  have hdescent : baseEnd_210901 < baseStart_210901 := by decide
  rcases family_descends (prefixWord ++ tailWord_210901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210911 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 3]
def baseStart_210911 : Nat := 118140960795 + 210911 * 2 ^ 59
def prefixEnd_210911 : Nat := 4983230072969 + 3 ^ 40 * 210911 * 2
def baseEnd_210911 : Nat := 96265527396026260837817

theorem tailTrace_210911 : CollatzResearch.WordTrace tailWord_210911 prefixEnd_210911 96265527396026260837817 := by
  unfold tailWord_210911
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692556138912942576152587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5128370759275295050768391 7692556138912942576152587)
  ·
    refine ⟨11538834208369413864228881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7692556138912942576152587 11538834208369413864228881)
    ·
      refine ⟨8654125656277060398171661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11538834208369413864228881 8654125656277060398171661)
      ·
        refine ⟨3245297121103897649314373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8654125656277060398171661 3245297121103897649314373)
        ·
          refine ⟨608493210206980809246445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3245297121103897649314373 608493210206980809246445)
          ·
            refine ⟨228184953827617803467417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 608493210206980809246445 228184953827617803467417)
            ·
              refine ⟨171138715370713352600563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228184953827617803467417 171138715370713352600563)
              ·
                refine ⟨256708073056070028900845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171138715370713352600563 256708073056070028900845)
                ·
                  refine ⟨96265527396026260837817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256708073056070028900845 96265527396026260837817)
                  ·
                    rfl

theorem cell20_210911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 3].length) (baseStart_210911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210911 prefixEnd_210911 := by exact prefixLift 210911
  have htrace : WordTrace (prefixWord ++ tailWord_210911) baseStart_210911 baseEnd_210911 := by
    simpa [prefixWord, tailWord_210911, baseEnd_210911] using wordTrace_append hprefix tailTrace_210911
  have hstable : (prefixWord ++ tailWord_210911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210911).length < 2 ^ (prefixWord ++ tailWord_210911).sum := by decide
  have hdescent : baseEnd_210911 < baseStart_210911 := by decide
  rcases family_descends (prefixWord ++ tailWord_210911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210922 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_210922 : Nat := 118140960795 + 210922 * 2 ^ 59
def prefixEnd_210922 : Nat := 4983230072969 + 3 ^ 40 * 210922 * 2
def baseEnd_210922 : Nat := 96270548095759111471105

theorem tailTrace_210922 : CollatzResearch.WordTrace tailWord_210922 prefixEnd_210922 96270548095759111471105 := by
  unfold tailWord_210922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923239335468272863700755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5128638227915394303202013 1923239335468272863700755)
  ·
    refine ⟨2884859003202409295551133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1923239335468272863700755 2884859003202409295551133)
    ·
      refine ⟨1081822126200903485831675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2884859003202409295551133 1081822126200903485831675)
      ·
        refine ⟨1622733189301355228747513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081822126200903485831675 1622733189301355228747513)
        ·
          refine ⟨1217049891976016421560635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622733189301355228747513 1217049891976016421560635)
          ·
            refine ⟨1825574837964024632340953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217049891976016421560635 1825574837964024632340953)
            ·
              refine ⟨1369181128473018474255715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825574837964024632340953 1369181128473018474255715)
              ·
                refine ⟨2053771692709527711383573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369181128473018474255715 2053771692709527711383573)
                ·
                  refine ⟨96270548095759111471105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2053771692709527711383573 96270548095759111471105)
                  ·
                    rfl

theorem cell20_210922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_210922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210922 prefixEnd_210922 := by exact prefixLift 210922
  have htrace : WordTrace (prefixWord ++ tailWord_210922) baseStart_210922 baseEnd_210922 := by
    simpa [prefixWord, tailWord_210922, baseEnd_210922] using wordTrace_append hprefix tailTrace_210922
  have hstable : (prefixWord ++ tailWord_210922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210922).length < 2 ^ (prefixWord ++ tailWord_210922).sum := by decide
  have hdescent : baseEnd_210922 < baseStart_210922 := by decide
  rcases family_descends (prefixWord ++ tailWord_210922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210936 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_210936 : Nat := 118140960795 + 210936 * 2 ^ 59
def prefixEnd_210936 : Nat := 4983230072969 + 3 ^ 40 * 210936 * 2
def baseEnd_210936 : Nat := 96276938077237285004381

theorem tailTrace_210936 : CollatzResearch.WordTrace tailWord_210936 prefixEnd_210936 96276938077237285004381 := by
  unfold tailWord_210936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3846733981911185922906331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5128978642548247897208441 3846733981911185922906331)
  ·
    refine ⟨5770100972866778884359497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3846733981911185922906331 5770100972866778884359497)
    ·
      refine ⟨4327575729650084163269623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5770100972866778884359497 4327575729650084163269623)
      ·
        refine ⟨6491363594475126244904435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327575729650084163269623 6491363594475126244904435)
        ·
          refine ⟨9737045391712689367356653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6491363594475126244904435 9737045391712689367356653)
          ·
            refine ⟨3651392021892258512758745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9737045391712689367356653 3651392021892258512758745)
            ·
              refine ⟨2738544016419193884569059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3651392021892258512758745 2738544016419193884569059)
              ·
                refine ⟨4107816024628790826853589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738544016419193884569059 4107816024628790826853589)
                ·
                  refine ⟨96276938077237285004381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4107816024628790826853589 96276938077237285004381)
                  ·
                    rfl

theorem cell20_210936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_210936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210936 prefixEnd_210936 := by exact prefixLift 210936
  have htrace : WordTrace (prefixWord ++ tailWord_210936) baseStart_210936 baseEnd_210936 := by
    simpa [prefixWord, tailWord_210936, baseEnd_210936] using wordTrace_append hprefix tailTrace_210936
  have hstable : (prefixWord ++ tailWord_210936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210936).length < 2 ^ (prefixWord ++ tailWord_210936).sum := by decide
  have hdescent : baseEnd_210936 < baseStart_210936 := by decide
  rcases family_descends (prefixWord ++ tailWord_210936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210977 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 4]
def baseStart_210977 : Nat := 118140960795 + 210977 * 2 ^ 59
def prefixEnd_210977 : Nat := 4983230072969 + 3 ^ 40 * 210977 * 2
def baseEnd_210977 : Nat := 96295651594423364637547

theorem tailTrace_210977 : CollatzResearch.WordTrace tailWord_210977 prefixEnd_210977 96295651594423364637547 := by
  unfold tailWord_210977
  simp only [CollatzResearch.WordTrace]
  refine ⟨7694963356673835848055185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5129975571115890565370123 7694963356673835848055185)
  ·
    refine ⟨5771222517505376886041389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7694963356673835848055185 5771222517505376886041389)
    ·
      refine ⟨2164208444064516332265521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5771222517505376886041389 2164208444064516332265521)
      ·
        refine ⟨1623156333048387249199141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2164208444064516332265521 1623156333048387249199141)
        ·
          refine ⟨304341812446572609224839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1623156333048387249199141 304341812446572609224839)
          ·
            refine ⟨456512718669858913837259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304341812446572609224839 456512718669858913837259)
            ·
              refine ⟨684769078004788370755889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456512718669858913837259 684769078004788370755889)
              ·
                refine ⟨513576808503591278066917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684769078004788370755889 513576808503591278066917)
                ·
                  refine ⟨96295651594423364637547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513576808503591278066917 96295651594423364637547)
                  ·
                    rfl

theorem cell20_210977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_210977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210977 prefixEnd_210977 := by exact prefixLift 210977
  have htrace : WordTrace (prefixWord ++ tailWord_210977) baseStart_210977 baseEnd_210977 := by
    simpa [prefixWord, tailWord_210977, baseEnd_210977] using wordTrace_append hprefix tailTrace_210977
  have hstable : (prefixWord ++ tailWord_210977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210977).length < 2 ^ (prefixWord ++ tailWord_210977).sum := by decide
  have hdescent : baseEnd_210977 < baseStart_210977 := by decide
  rcases family_descends (prefixWord ++ tailWord_210977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210994 : List Nat := [3, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_210994 : Nat := 118140960795 + 210994 * 2 ^ 59
def prefixEnd_210994 : Nat := 4983230072969 + 3 ^ 40 * 210994 * 2
def baseEnd_210994 : Nat := 96303410857646861070811

theorem tailTrace_210994 : CollatzResearch.WordTrace tailWord_210994 prefixEnd_210994 96303410857646861070811 := by
  unfold tailWord_210994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923895849403061937856009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5130388931741498500949357 1923895849403061937856009)
  ·
    refine ⟨1442921887052296453392007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1923895849403061937856009 1442921887052296453392007)
    ·
      refine ⟨2164382830578444680088011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442921887052296453392007 2164382830578444680088011)
      ·
        refine ⟨3246574245867667020132017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164382830578444680088011 3246574245867667020132017)
        ·
          refine ⟨2434930684400750265099013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3246574245867667020132017 2434930684400750265099013)
          ·
            refine ⟨456549503325140674706065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2434930684400750265099013 456549503325140674706065)
            ·
              refine ⟨342412127493855506029549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456549503325140674706065 342412127493855506029549)
              ·
                refine ⟨128404547810195814761081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342412127493855506029549 128404547810195814761081)
                ·
                  refine ⟨96303410857646861070811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128404547810195814761081 96303410857646861070811)
                  ·
                    rfl

theorem cell20_210994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_210994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_210994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_210994 prefixEnd_210994 := by exact prefixLift 210994
  have htrace : WordTrace (prefixWord ++ tailWord_210994) baseStart_210994 baseEnd_210994 := by
    simpa [prefixWord, tailWord_210994, baseEnd_210994] using wordTrace_append hprefix tailTrace_210994
  have hstable : (prefixWord ++ tailWord_210994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210994).length < 2 ^ (prefixWord ++ tailWord_210994).sum := by decide
  have hdescent : baseEnd_210994 < baseStart_210994 := by decide
  rcases family_descends (prefixWord ++ tailWord_210994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211005 : List Nat := [1, 4, 1, 3, 1, 1, 9]
def baseStart_211005 : Nat := 118140960795 + 211005 * 2 ^ 59
def prefixEnd_211005 : Nat := 4983230072969 + 3 ^ 40 * 211005 * 2
def baseEnd_211005 : Nat := 10700936839708856856011

theorem tailTrace_211005 : CollatzResearch.WordTrace tailWord_211005 prefixEnd_211005 10700936839708856856011 := by
  unfold tailWord_211005
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695984600572396630074469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5130656400381597753382979 7695984600572396630074469)
  ·
    refine ⟨1442997112607324368138963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7695984600572396630074469 1442997112607324368138963)
    ·
      refine ⟨2164495668910986552208445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442997112607324368138963 2164495668910986552208445)
      ·
        refine ⟨811685875841619957078167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2164495668910986552208445 811685875841619957078167)
        ·
          refine ⟨1217528813762429935617251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811685875841619957078167 1217528813762429935617251)
          ·
            refine ⟨1826293220643644903425877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217528813762429935617251 1826293220643644903425877)
            ·
              refine ⟨10700936839708856856011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1826293220643644903425877 10700936839708856856011)
              ·
                rfl

theorem cell20_211005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_211005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211005 prefixEnd_211005 := by exact prefixLift 211005
  have htrace : WordTrace (prefixWord ++ tailWord_211005) baseStart_211005 baseEnd_211005 := by
    simpa [prefixWord, tailWord_211005, baseEnd_211005] using wordTrace_append hprefix tailTrace_211005
  have hstable : (prefixWord ++ tailWord_211005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211005).length < 2 ^ (prefixWord ++ tailWord_211005).sum := by decide
  have hdescent : baseEnd_211005 < baseStart_211005 := by decide
  rcases family_descends (prefixWord ++ tailWord_211005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211008 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_211008 : Nat := 118140960795 + 211008 * 2 ^ 59
def prefixEnd_211008 : Nat := 4983230072969 + 3 ^ 40 * 211008 * 2
def baseEnd_211008 : Nat := 96309800839125034604087

theorem tailTrace_211008 : CollatzResearch.WordTrace tailWord_211008 prefixEnd_211008 96309800839125034604087 := by
  unfold tailWord_211008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848047009780764071216839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5130729346374352094955785 3848047009780764071216839)
  ·
    refine ⟨5772070514671146106825259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3848047009780764071216839 5772070514671146106825259)
    ·
      refine ⟨8658105772006719160237889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772070514671146106825259 8658105772006719160237889)
      ·
        refine ⟨6493579329005039370178417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8658105772006719160237889 6493579329005039370178417)
        ·
          refine ⟨4870184496753779527633813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6493579329005039370178417 4870184496753779527633813)
          ·
            refine ⟨228289898285333415357835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4870184496753779527633813 228289898285333415357835)
            ·
              refine ⟨342434847428000123036753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228289898285333415357835 342434847428000123036753)
              ·
                refine ⟨256826135571000092277565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342434847428000123036753 256826135571000092277565)
                ·
                  refine ⟨96309800839125034604087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256826135571000092277565 96309800839125034604087)
                  ·
                    rfl

theorem cell20_211008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_211008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211008 prefixEnd_211008 := by exact prefixLift 211008
  have htrace : WordTrace (prefixWord ++ tailWord_211008) baseStart_211008 baseEnd_211008 := by
    simpa [prefixWord, tailWord_211008, baseEnd_211008] using wordTrace_append hprefix tailTrace_211008
  have hstable : (prefixWord ++ tailWord_211008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211008).length < 2 ^ (prefixWord ++ tailWord_211008).sum := by decide
  have hdescent : baseEnd_211008 < baseStart_211008 := by decide
  rcases family_descends (prefixWord ++ tailWord_211008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211015 : List Nat := [1, 1, 4, 1, 3, 1, 1, 6, 2]
def baseStart_211015 : Nat := 118140960795 + 211015 * 2 ^ 59
def prefixEnd_211015 : Nat := 4983230072969 + 3 ^ 40 * 211015 * 2
def baseEnd_211015 : Nat := 96312995829864121370725

theorem tailTrace_211015 : CollatzResearch.WordTrace tailWord_211015 prefixEnd_211015 96312995829864121370725 := by
  unfold tailWord_211015
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696349330536168337938499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5130899553690778891958999 7696349330536168337938499)
  ·
    refine ⟨11544523995804252506907749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7696349330536168337938499 11544523995804252506907749)
    ·
      refine ⟨2164598249213297345045203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11544523995804252506907749 2164598249213297345045203)
      ·
        refine ⟨3246897373819946017567805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164598249213297345045203 3246897373819946017567805)
        ·
          refine ⟨1217586515182479756587927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3246897373819946017567805 1217586515182479756587927)
          ·
            refine ⟨1826379772773719634881891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217586515182479756587927 1826379772773719634881891)
            ·
              refine ⟨2739569659160579452322837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826379772773719634881891 2739569659160579452322837)
              ·
                refine ⟨128417327773152161827633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2739569659160579452322837 128417327773152161827633)
                ·
                  refine ⟨96312995829864121370725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128417327773152161827633 96312995829864121370725)
                  ·
                    rfl

theorem cell20_211015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 2].length) (baseStart_211015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211015 prefixEnd_211015 := by exact prefixLift 211015
  have htrace : WordTrace (prefixWord ++ tailWord_211015) baseStart_211015 baseEnd_211015 := by
    simpa [prefixWord, tailWord_211015, baseEnd_211015] using wordTrace_append hprefix tailTrace_211015
  have hstable : (prefixWord ++ tailWord_211015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211015).length < 2 ^ (prefixWord ++ tailWord_211015).sum := by decide
  have hdescent : baseEnd_211015 < baseStart_211015 := by decide
  rcases family_descends (prefixWord ++ tailWord_211015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211019 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_211019 : Nat := 118140960795 + 211019 * 2 ^ 59
def prefixEnd_211019 : Nat := 4983230072969 + 3 ^ 40 * 211019 * 2
def baseEnd_211019 : Nat := 96314821538857885237375

theorem tailTrace_211019 : CollatzResearch.WordTrace tailWord_211019 prefixEnd_211019 96314821538857885237375 := by
  unfold tailWord_211019
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696495222521677021084111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5130996815014451347389407 7696495222521677021084111)
  ·
    refine ⟨11544742833782515531626167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7696495222521677021084111 11544742833782515531626167)
    ·
      refine ⟨17317114250673773297439251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11544742833782515531626167 17317114250673773297439251)
      ·
        refine ⟨25975671376010659946158877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17317114250673773297439251 25975671376010659946158877)
        ·
          refine ⟨9740876766003997479809579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25975671376010659946158877 9740876766003997479809579)
          ·
            refine ⟨14611315149005996219714369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740876766003997479809579 14611315149005996219714369)
            ·
              refine ⟨10958486361754497164785777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14611315149005996219714369 10958486361754497164785777)
              ·
                refine ⟨8218864771315872873589333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10958486361754497164785777 8218864771315872873589333)
                ·
                  refine ⟨96314821538857885237375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8218864771315872873589333 96314821538857885237375)
                  ·
                    rfl

theorem cell20_211019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_211019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211019 prefixEnd_211019 := by exact prefixLift 211019
  have htrace : WordTrace (prefixWord ++ tailWord_211019) baseStart_211019 baseEnd_211019 := by
    simpa [prefixWord, tailWord_211019, baseEnd_211019] using wordTrace_append hprefix tailTrace_211019
  have hstable : (prefixWord ++ tailWord_211019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211019).length < 2 ^ (prefixWord ++ tailWord_211019).sum := by decide
  have hdescent : baseEnd_211019 < baseStart_211019 := by decide
  rcases family_descends (prefixWord ++ tailWord_211019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211081 : List Nat := [1, 2, 1, 1, 4, 2, 4, 5]
def baseStart_211081 : Nat := 118140960795 + 211081 * 2 ^ 59
def prefixEnd_211081 : Nat := 4983230072969 + 3 ^ 40 * 211081 * 2
def baseEnd_211081 : Nat := 32114373342753741723485

theorem tailTrace_211081 : CollatzResearch.WordTrace tailWord_211081 prefixEnd_211081 32114373342753741723485 := by
  unfold tailWord_211081
  simp only [CollatzResearch.WordTrace]
  refine ⟨7698756548297061609841097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5132504365531374406560731 7698756548297061609841097)
  ·
    refine ⟨5774067411222796207380823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7698756548297061609841097 5774067411222796207380823)
    ·
      refine ⟨8661101116834194311071235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774067411222796207380823 8661101116834194311071235)
      ·
        refine ⟨12991651675251291466606853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8661101116834194311071235 12991651675251291466606853)
        ·
          refine ⟨2435934689109617149988785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12991651675251291466606853 2435934689109617149988785)
          ·
            refine ⟨1826951016832212862491589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435934689109617149988785 1826951016832212862491589)
            ·
              refine ⟨342553315656039911717173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1826951016832212862491589 342553315656039911717173)
              ·
                refine ⟨32114373342753741723485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342553315656039911717173 32114373342753741723485)
                ·
                  rfl

theorem cell20_211081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_211081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211081 prefixEnd_211081 := by exact prefixLift 211081
  have htrace : WordTrace (prefixWord ++ tailWord_211081) baseStart_211081 baseEnd_211081 := by
    simpa [prefixWord, tailWord_211081, baseEnd_211081] using wordTrace_append hprefix tailTrace_211081
  have hstable : (prefixWord ++ tailWord_211081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211081).length < 2 ^ (prefixWord ++ tailWord_211081).sum := by decide
  have hdescent : baseEnd_211081 < baseStart_211081 := by decide
  rcases family_descends (prefixWord ++ tailWord_211081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211118 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_211118 : Nat := 118140960795 + 211118 * 2 ^ 59
def prefixEnd_211118 : Nat := 4983230072969 + 3 ^ 40 * 211118 * 2
def baseEnd_211118 : Nat := 96360007836453540936971

theorem tailTrace_211118 : CollatzResearch.WordTrace tailWord_211118 prefixEnd_211118 96360007836453540936971 := by
  unfold tailWord_211118
  simp only [CollatzResearch.WordTrace]
  refine ⟨962513256145377116117251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5133404032775344619292005 962513256145377116117251)
  ·
    refine ⟨1443769884218065674175877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962513256145377116117251 1443769884218065674175877)
    ·
      refine ⟨270706853290887313907977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1443769884218065674175877 270706853290887313907977)
      ·
        refine ⟨203030139968165485430983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270706853290887313907977 203030139968165485430983)
        ·
          refine ⟨304545209952248228146475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203030139968165485430983 304545209952248228146475)
          ·
            refine ⟨456817814928372342219713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304545209952248228146475 456817814928372342219713)
            ·
              refine ⟨342613361196279256664785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456817814928372342219713 342613361196279256664785)
              ·
                refine ⟨256960020897209442498589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342613361196279256664785 256960020897209442498589)
                ·
                  refine ⟨96360007836453540936971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256960020897209442498589 96360007836453540936971)
                  ·
                    rfl

theorem cell20_211118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_211118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211118 prefixEnd_211118 := by exact prefixLift 211118
  have htrace : WordTrace (prefixWord ++ tailWord_211118) baseStart_211118 baseEnd_211118 := by
    simpa [prefixWord, tailWord_211118, baseEnd_211118] using wordTrace_append hprefix tailTrace_211118
  have hstable : (prefixWord ++ tailWord_211118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211118).length < 2 ^ (prefixWord ++ tailWord_211118).sum := by decide
  have hdescent : baseEnd_211118 < baseStart_211118 := by decide
  rcases family_descends (prefixWord ++ tailWord_211118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211125 : List Nat := [1, 3, 3, 4, 1, 1, 1, 4, 2]
def baseStart_211125 : Nat := 118140960795 + 211125 * 2 ^ 59
def prefixEnd_211125 : Nat := 4983230072969 + 3 ^ 40 * 211125 * 2
def baseEnd_211125 : Nat := 96363202827192627703609

theorem tailTrace_211125 : CollatzResearch.WordTrace tailWord_211125 prefixEnd_211125 96363202827192627703609 := by
  unfold tailWord_211125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700361360137657124442829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5133574240091771416295219 7700361360137657124442829)
  ·
    refine ⟨2887635510051621421666061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7700361360137657124442829 2887635510051621421666061)
    ·
      refine ⟨1082863316269358033124773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2887635510051621421666061 1082863316269358033124773)
      ·
        refine ⟨203036871800504631210895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1082863316269358033124773 203036871800504631210895)
        ·
          refine ⟨304555307700756946816343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203036871800504631210895 304555307700756946816343)
          ·
            refine ⟨456832961551135420224515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304555307700756946816343 456832961551135420224515)
            ·
              refine ⟨685249442326703130336773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456832961551135420224515 685249442326703130336773)
              ·
                refine ⟨128484270436256836938145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685249442326703130336773 128484270436256836938145)
                ·
                  refine ⟨96363202827192627703609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128484270436256836938145 96363202827192627703609)
                  ·
                    rfl

theorem cell20_211125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_211125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211125 prefixEnd_211125 := by exact prefixLift 211125
  have htrace : WordTrace (prefixWord ++ tailWord_211125) baseStart_211125 baseEnd_211125 := by
    simpa [prefixWord, tailWord_211125, baseEnd_211125] using wordTrace_append hprefix tailTrace_211125
  have hstable : (prefixWord ++ tailWord_211125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211125).length < 2 ^ (prefixWord ++ tailWord_211125).sum := by decide
  have hdescent : baseEnd_211125 < baseStart_211125 := by decide
  rcases family_descends (prefixWord ++ tailWord_211125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211129 : List Nat := [1, 2, 1, 4, 1, 2, 3, 4, 2]
def baseStart_211129 : Nat := 118140960795 + 211129 * 2 ^ 59
def prefixEnd_211129 : Nat := 4983230072969 + 3 ^ 40 * 211129 * 2
def baseEnd_211129 : Nat := 96365028536186391570259

theorem tailTrace_211129 : CollatzResearch.WordTrace tailWord_211129 prefixEnd_211129 96365028536186391570259 := by
  unfold tailWord_211129
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700507252123165807588441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5133671501415443871725627 7700507252123165807588441)
  ·
    refine ⟨5775380439092374355691331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7700507252123165807588441 5775380439092374355691331)
    ·
      refine ⟨8663070658638561533536997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5775380439092374355691331 8663070658638561533536997)
      ·
        refine ⟨1624325748494730287538187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8663070658638561533536997 1624325748494730287538187)
        ·
          refine ⟨2436488622742095431307281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624325748494730287538187 2436488622742095431307281)
          ·
            refine ⟨1827366467056571573480461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436488622742095431307281 1827366467056571573480461)
            ·
              refine ⟨685262425146214340055173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1827366467056571573480461 685262425146214340055173)
              ·
                refine ⟨128486704714915188760345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685262425146214340055173 128486704714915188760345)
                ·
                  refine ⟨96365028536186391570259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128486704714915188760345 96365028536186391570259)
                  ·
                    rfl

theorem cell20_211129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_211129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211129 prefixEnd_211129 := by exact prefixLift 211129
  have htrace : WordTrace (prefixWord ++ tailWord_211129) baseStart_211129 baseEnd_211129 := by
    simpa [prefixWord, tailWord_211129, baseEnd_211129] using wordTrace_append hprefix tailTrace_211129
  have hstable : (prefixWord ++ tailWord_211129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211129).length < 2 ^ (prefixWord ++ tailWord_211129).sum := by decide
  have hdescent : baseEnd_211129 < baseStart_211129 := by decide
  rcases family_descends (prefixWord ++ tailWord_211129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211136 : List Nat := [2, 1, 1, 2, 5, 3, 1, 5]
def baseStart_211136 : Nat := 118140960795 + 211136 * 2 ^ 59
def prefixEnd_211136 : Nat := 4983230072969 + 3 ^ 40 * 211136 * 2
def baseEnd_211136 : Nat := 32122741175641826112299

theorem tailTrace_211136 : CollatzResearch.WordTrace tailWord_211136 prefixEnd_211136 32122741175641826112299 := by
  unfold tailWord_211136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850381281548903001546631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5133841708731870668728841 3850381281548903001546631)
  ·
    refine ⟨5775571922323354502319947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850381281548903001546631 5775571922323354502319947)
    ·
      refine ⟨8663357883485031753479921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5775571922323354502319947 8663357883485031753479921)
      ·
        refine ⟨6497518412613773815109941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8663357883485031753479921 6497518412613773815109941)
        ·
          refine ⟨609142351182541295166557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6497518412613773815109941 609142351182541295166557)
          ·
            refine ⟨228428381693452985687459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609142351182541295166557 228428381693452985687459)
            ·
              refine ⟨342642572540179478531189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228428381693452985687459 342642572540179478531189)
              ·
                refine ⟨32122741175641826112299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342642572540179478531189 32122741175641826112299)
                ·
                  rfl

theorem cell20_211136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_211136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211136 prefixEnd_211136 := by exact prefixLift 211136
  have htrace : WordTrace (prefixWord ++ tailWord_211136) baseStart_211136 baseEnd_211136 := by
    simpa [prefixWord, tailWord_211136, baseEnd_211136] using wordTrace_append hprefix tailTrace_211136
  have hstable : (prefixWord ++ tailWord_211136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211136).length < 2 ^ (prefixWord ++ tailWord_211136).sum := by decide
  have hdescent : baseEnd_211136 < baseStart_211136 := by decide
  rcases family_descends (prefixWord ++ tailWord_211136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211150 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_211150 : Nat := 118140960795 + 211150 * 2 ^ 59
def prefixEnd_211150 : Nat := 4983230072969 + 3 ^ 40 * 211150 * 2
def baseEnd_211150 : Nat := 96374613508403651870173

theorem tailTrace_211150 : CollatzResearch.WordTrace tailWord_211150 prefixEnd_211150 96374613508403651870173 := by
  unfold tailWord_211150
  simp only [CollatzResearch.WordTrace]
  refine ⟨962659148130885799262863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5134182123364724262735269 962659148130885799262863)
  ·
    refine ⟨1443988722196328698894295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962659148130885799262863 1443988722196328698894295)
    ·
      refine ⟨2165983083294493048341443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443988722196328698894295 2165983083294493048341443)
      ·
        refine ⟨3248974624941739572512165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165983083294493048341443 3248974624941739572512165)
        ·
          refine ⟨609182742176576169846031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3248974624941739572512165 609182742176576169846031)
          ·
            refine ⟨913774113264864254769047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609182742176576169846031 913774113264864254769047)
            ·
              refine ⟨1370661169897296382153571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913774113264864254769047 1370661169897296382153571)
              ·
                refine ⟨2055991754845944573230357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370661169897296382153571 2055991754845944573230357)
                ·
                  refine ⟨96374613508403651870173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2055991754845944573230357 96374613508403651870173)
                  ·
                    rfl

theorem cell20_211150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_211150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211150 prefixEnd_211150 := by exact prefixLift 211150
  have htrace : WordTrace (prefixWord ++ tailWord_211150) baseStart_211150 baseEnd_211150 := by
    simpa [prefixWord, tailWord_211150, baseEnd_211150] using wordTrace_append hprefix tailTrace_211150
  have hstable : (prefixWord ++ tailWord_211150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211150).length < 2 ^ (prefixWord ++ tailWord_211150).sum := by decide
  have hdescent : baseEnd_211150 < baseStart_211150 := by decide
  rcases family_descends (prefixWord ++ tailWord_211150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211170 : List Nat := [3, 3, 4, 1, 1, 1, 7]
def baseStart_211170 : Nat := 118140960795 + 211170 * 2 ^ 59
def prefixEnd_211170 : Nat := 4983230072969 + 3 ^ 40 * 211170 * 2
def baseEnd_211170 : Nat := 10709304672596941244825

theorem tailTrace_211170 : CollatzResearch.WordTrace tailWord_211170 prefixEnd_211170 10709304672596941244825 := by
  unfold tailWord_211170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925500661243657452457741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5134668429983086539887309 1925500661243657452457741)
  ·
    refine ⟨722062747966371544671653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1925500661243657452457741 722062747966371544671653)
    ·
      refine ⟨135386765243694664625935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 722062747966371544671653 135386765243694664625935)
      ·
        refine ⟨203080147865541996938903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135386765243694664625935 203080147865541996938903)
        ·
          refine ⟨304620221798312995408355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203080147865541996938903 304620221798312995408355)
          ·
            refine ⟨456930332697469493112533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304620221798312995408355 456930332697469493112533)
            ·
              refine ⟨10709304672596941244825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 456930332697469493112533 10709304672596941244825)
              ·
                rfl

theorem cell20_211170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 7].length) (baseStart_211170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211170 prefixEnd_211170 := by exact prefixLift 211170
  have htrace : WordTrace (prefixWord ++ tailWord_211170) baseStart_211170 baseEnd_211170 := by
    simpa [prefixWord, tailWord_211170, baseEnd_211170] using wordTrace_append hprefix tailTrace_211170
  have hstable : (prefixWord ++ tailWord_211170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211170).length < 2 ^ (prefixWord ++ tailWord_211170).sum := by decide
  have hdescent : baseEnd_211170 < baseStart_211170 := by decide
  rcases family_descends (prefixWord ++ tailWord_211170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211229 : List Nat := [1, 4, 2, 3, 3, 1, 6]
def baseStart_211229 : Nat := 118140960795 + 211229 * 2 ^ 59
def prefixEnd_211229 : Nat := 4983230072969 + 3 ^ 40 * 211229 * 2
def baseEnd_211229 : Nat := 10712296806781165359613

theorem tailTrace_211229 : CollatzResearch.WordTrace tailWord_211229 prefixEnd_211229 10712296806781165359613 := by
  unfold tailWord_211229
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704154551760882886228741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5136103034507255257485827 7704154551760882886228741)
  ·
    refine ⟨1444528978455165541167889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7704154551760882886228741 1444528978455165541167889)
    ·
      refine ⟨1083396733841374155875917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1444528978455165541167889 1083396733841374155875917)
      ·
        refine ⟨406273775190515308453469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1083396733841374155875917 406273775190515308453469)
        ·
          refine ⟨152352665696443240670051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406273775190515308453469 152352665696443240670051)
          ·
            refine ⟨228528998544664861005077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152352665696443240670051 228528998544664861005077)
            ·
              refine ⟨10712296806781165359613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 228528998544664861005077 10712296806781165359613)
              ·
                rfl

theorem cell20_211229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 6].length) (baseStart_211229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211229 prefixEnd_211229 := by exact prefixLift 211229
  have htrace : WordTrace (prefixWord ++ tailWord_211229) baseStart_211229 baseEnd_211229 := by
    simpa [prefixWord, tailWord_211229, baseEnd_211229] using wordTrace_append hprefix tailTrace_211229
  have hstable : (prefixWord ++ tailWord_211229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211229).length < 2 ^ (prefixWord ++ tailWord_211229).sum := by decide
  have hdescent : baseEnd_211229 < baseStart_211229 := by decide
  rcases family_descends (prefixWord ++ tailWord_211229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211250 : List Nat := [3, 2, 1, 1, 5, 1, 2, 5]
def baseStart_211250 : Nat := 118140960795 + 211250 * 2 ^ 59
def prefixEnd_211250 : Nat := 4983230072969 + 3 ^ 40 * 211250 * 2
def baseEnd_211250 : Nat := 32140085411082582845477

theorem tailTrace_211250 : CollatzResearch.WordTrace tailWord_211250 prefixEnd_211250 32140085411082582845477 := by
  unfold tailWord_211250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926230121171200868185801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5136613656456535648495469 1926230121171200868185801)
  ·
    refine ⟨1444672590878400651139351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1926230121171200868185801 1444672590878400651139351)
    ·
      refine ⟨2167008886317600976709027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444672590878400651139351 2167008886317600976709027)
      ·
        refine ⟨3250513329476401465063541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167008886317600976709027 3250513329476401465063541)
        ·
          refine ⟨304735624638412637349707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3250513329476401465063541 304735624638412637349707)
          ·
            refine ⟨457103436957618956024561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304735624638412637349707 457103436957618956024561)
            ·
              refine ⟨342827577718214217018421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457103436957618956024561 342827577718214217018421)
              ·
                refine ⟨32140085411082582845477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342827577718214217018421 32140085411082582845477)
                ·
                  rfl

theorem cell20_211250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_211250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211250 prefixEnd_211250 := by exact prefixLift 211250
  have htrace : WordTrace (prefixWord ++ tailWord_211250) baseStart_211250 baseEnd_211250 := by
    simpa [prefixWord, tailWord_211250, baseEnd_211250] using wordTrace_append hprefix tailTrace_211250
  have hstable : (prefixWord ++ tailWord_211250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211250).length < 2 ^ (prefixWord ++ tailWord_211250).sum := by decide
  have hdescent : baseEnd_211250 < baseStart_211250 := by decide
  rcases family_descends (prefixWord ++ tailWord_211250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211278 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_211278 : Nat := 118140960795 + 211278 * 2 ^ 59
def prefixEnd_211278 : Nat := 4983230072969 + 3 ^ 40 * 211278 * 2
def baseEnd_211278 : Nat := 96433036196204095602983

theorem tailTrace_211278 : CollatzResearch.WordTrace tailWord_211278 prefixEnd_211278 96433036196204095602983 := by
  unfold tailWord_211278
  simp only [CollatzResearch.WordTrace]
  refine ⟨963242716072920531845311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5137294485722242836508325 963242716072920531845311)
  ·
    refine ⟨1444864074109380797767967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 963242716072920531845311 1444864074109380797767967)
    ·
      refine ⟨2167296111164071196651951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444864074109380797767967 2167296111164071196651951)
      ·
        refine ⟨3250944166746106794977927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167296111164071196651951 3250944166746106794977927)
        ·
          refine ⟨4876416250119160192466891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250944166746106794977927 4876416250119160192466891)
          ·
            refine ⟨7314624375178740288700337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876416250119160192466891 7314624375178740288700337)
            ·
              refine ⟨5485968281384055216525253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7314624375178740288700337 5485968281384055216525253)
              ·
                refine ⟨1028619052759510353098485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5485968281384055216525253 1028619052759510353098485)
                ·
                  refine ⟨96433036196204095602983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1028619052759510353098485 96433036196204095602983)
                  ·
                    rfl

theorem cell20_211278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_211278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211278 prefixEnd_211278 := by exact prefixLift 211278
  have htrace : WordTrace (prefixWord ++ tailWord_211278) baseStart_211278 baseEnd_211278 := by
    simpa [prefixWord, tailWord_211278, baseEnd_211278] using wordTrace_append hprefix tailTrace_211278
  have hstable : (prefixWord ++ tailWord_211278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211278).length < 2 ^ (prefixWord ++ tailWord_211278).sum := by decide
  have hdescent : baseEnd_211278 < baseStart_211278 := by decide
  rcases family_descends (prefixWord ++ tailWord_211278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211298 : List Nat := [3, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_211298 : Nat := 118140960795 + 211298 * 2 ^ 59
def prefixEnd_211298 : Nat := 4983230072969 + 3 ^ 40 * 211298 * 2
def baseEnd_211298 : Nat := 96442164741172914936235

theorem tailTrace_211298 : CollatzResearch.WordTrace tailWord_211298 prefixEnd_211298 96442164741172914936235 := by
  unfold tailWord_211298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926667797127726917622637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5137780792340605113660365 1926667797127726917622637)
  ·
    refine ⟨722500423922897594108489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1926667797127726917622637 722500423922897594108489)
    ·
      refine ⟨541875317942173195581367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722500423922897594108489 541875317942173195581367)
      ·
        refine ⟨812812976913259793372051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541875317942173195581367 812812976913259793372051)
        ·
          refine ⟨1219219465369889690058077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812812976913259793372051 1219219465369889690058077)
          ·
            refine ⟨457207299513708633771779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1219219465369889690058077 457207299513708633771779)
            ·
              refine ⟨685810949270562950657669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457207299513708633771779 685810949270562950657669)
              ·
                refine ⟨128589552988230553248313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685810949270562950657669 128589552988230553248313)
                ·
                  refine ⟨96442164741172914936235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128589552988230553248313 96442164741172914936235)
                  ·
                    rfl

theorem cell20_211298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_211298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211298 prefixEnd_211298 := by exact prefixLift 211298
  have htrace : WordTrace (prefixWord ++ tailWord_211298) baseStart_211298 baseEnd_211298 := by
    simpa [prefixWord, tailWord_211298, baseEnd_211298] using wordTrace_append hprefix tailTrace_211298
  have hstable : (prefixWord ++ tailWord_211298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211298).length < 2 ^ (prefixWord ++ tailWord_211298).sum := by decide
  have hdescent : baseEnd_211298 < baseStart_211298 := by decide
  rcases family_descends (prefixWord ++ tailWord_211298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211323 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_211323 : Nat := 118140960795 + 211323 * 2 ^ 59
def prefixEnd_211323 : Nat := 4983230072969 + 3 ^ 40 * 211323 * 2
def baseEnd_211323 : Nat := 96453575422383939102799

theorem tailTrace_211323 : CollatzResearch.WordTrace tailWord_211323 prefixEnd_211323 96453575422383939102799 := by
  unfold tailWord_211323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707583013420336940150623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5138388675613557960100415 7707583013420336940150623)
  ·
    refine ⟨11561374520130505410225935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7707583013420336940150623 11561374520130505410225935)
    ·
      refine ⟨17342061780195758115338903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11561374520130505410225935 17342061780195758115338903)
      ·
        refine ⟨26013092670293637173008355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17342061780195758115338903 26013092670293637173008355)
        ·
          refine ⟨39019639005440455759512533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26013092670293637173008355 39019639005440455759512533)
          ·
            refine ⟨914522789190010681863575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 39019639005440455759512533 914522789190010681863575)
            ·
              refine ⟨1371784183785016022795363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914522789190010681863575 1371784183785016022795363)
              ·
                refine ⟨2057676275677524034193045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371784183785016022795363 2057676275677524034193045)
                ·
                  refine ⟨96453575422383939102799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2057676275677524034193045 96453575422383939102799)
                  ·
                    rfl

theorem cell20_211323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_211323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211323 prefixEnd_211323 := by exact prefixLift 211323
  have htrace : WordTrace (prefixWord ++ tailWord_211323) baseStart_211323 baseEnd_211323 := by
    simpa [prefixWord, tailWord_211323, baseEnd_211323] using wordTrace_append hprefix tailTrace_211323
  have hstable : (prefixWord ++ tailWord_211323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211323).length < 2 ^ (prefixWord ++ tailWord_211323).sum := by decide
  have hdescent : baseEnd_211323 < baseStart_211323 := by decide
  rcases family_descends (prefixWord ++ tailWord_211323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211357 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 4]
def baseStart_211357 : Nat := 118140960795 + 211357 * 2 ^ 59
def prefixEnd_211357 : Nat := 4983230072969 + 3 ^ 40 * 211357 * 2
def baseEnd_211357 : Nat := 96469093948830931969327

theorem tailTrace_211357 : CollatzResearch.WordTrace tailWord_211357 prefixEnd_211357 96469093948830931969327 := by
  unfold tailWord_211357
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708823095297160746888325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5139215396864773831258883 7708823095297160746888325)
  ·
    refine ⟨1445404330368217640041561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7708823095297160746888325 1445404330368217640041561)
    ·
      refine ⟨1084053247776163230031171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1445404330368217640041561 1084053247776163230031171)
      ·
        refine ⟨1626079871664244845046757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084053247776163230031171 1626079871664244845046757)
        ·
          refine ⟨304889975937045908446267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1626079871664244845046757 304889975937045908446267)
          ·
            refine ⟨457334963905568862669401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304889975937045908446267 457334963905568862669401)
            ·
              refine ⟨343001222929176647002051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457334963905568862669401 343001222929176647002051)
              ·
                refine ⟨514501834393764970503077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343001222929176647002051 514501834393764970503077)
                ·
                  refine ⟨96469093948830931969327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514501834393764970503077 96469093948830931969327)
                  ·
                    rfl

theorem cell20_211357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_211357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211357 prefixEnd_211357 := by exact prefixLift 211357
  have htrace : WordTrace (prefixWord ++ tailWord_211357) baseStart_211357 baseEnd_211357 := by
    simpa [prefixWord, tailWord_211357, baseEnd_211357] using wordTrace_append hprefix tailTrace_211357
  have hstable : (prefixWord ++ tailWord_211357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211357).length < 2 ^ (prefixWord ++ tailWord_211357).sum := by decide
  have hdescent : baseEnd_211357 < baseStart_211357 := by decide
  rcases family_descends (prefixWord ++ tailWord_211357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211381 : List Nat := [1, 3, 3, 2, 3, 2, 2, 4]
def baseStart_211381 : Nat := 118140960795 + 211381 * 2 ^ 59
def prefixEnd_211381 : Nat := 4983230072969 + 3 ^ 40 * 211381 * 2
def baseEnd_211381 : Nat := 32160016067597838389743

theorem tailTrace_211381 : CollatzResearch.WordTrace tailWord_211381 prefixEnd_211381 32160016067597838389743 := by
  unfold tailWord_211381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709698447210212845761997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5139798964806808563841331 7709698447210212845761997)
  ·
    refine ⟨2891136917703829817160749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7709698447210212845761997 2891136917703829817160749)
    ·
      refine ⟨1084176344138936181435281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2891136917703829817160749 1084176344138936181435281)
      ·
        refine ⟨813132258104202136076461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1084176344138936181435281 813132258104202136076461)
        ·
          refine ⟨304924596789075801028673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 813132258104202136076461 304924596789075801028673)
          ·
            refine ⟨228693447591806850771505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304924596789075801028673 228693447591806850771505)
            ·
              refine ⟨171520085693855138078629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228693447591806850771505 171520085693855138078629)
              ·
                refine ⟨32160016067597838389743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171520085693855138078629 32160016067597838389743)
                ·
                  rfl

theorem cell20_211381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_211381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211381 prefixEnd_211381 := by exact prefixLift 211381
  have htrace : WordTrace (prefixWord ++ tailWord_211381) baseStart_211381 baseEnd_211381 := by
    simpa [prefixWord, tailWord_211381, baseEnd_211381] using wordTrace_append hprefix tailTrace_211381
  have hstable : (prefixWord ++ tailWord_211381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211381).length < 2 ^ (prefixWord ++ tailWord_211381).sum := by decide
  have hdescent : baseEnd_211381 < baseStart_211381 := by decide
  rcases family_descends (prefixWord ++ tailWord_211381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211385 : List Nat := [1, 2, 1, 4, 3, 2, 1, 6]
def baseStart_211385 : Nat := 118140960795 + 211385 * 2 ^ 59
def prefixEnd_211385 : Nat := 4983230072969 + 3 ^ 40 * 211385 * 2
def baseEnd_211385 : Nat := 32160624637262426345293

theorem tailTrace_211385 : CollatzResearch.WordTrace tailWord_211385 prefixEnd_211385 32160624637262426345293 := by
  unfold tailWord_211385
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709844339195721528907609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5139896226130481019271739 7709844339195721528907609)
  ·
    refine ⟨5782383254396791146680707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7709844339195721528907609 5782383254396791146680707)
    ·
      refine ⟨8673574881595186720021061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782383254396791146680707 8673574881595186720021061)
      ·
        refine ⟨1626295290299097510003949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8673574881595186720021061 1626295290299097510003949)
        ·
          refine ⟨609860733862161566251481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1626295290299097510003949 609860733862161566251481)
          ·
            refine ⟨457395550396621174688611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609860733862161566251481 457395550396621174688611)
            ·
              refine ⟨686093325594931762032917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457395550396621174688611 686093325594931762032917)
              ·
                refine ⟨32160624637262426345293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686093325594931762032917 32160624637262426345293)
                ·
                  rfl

theorem cell20_211385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_211385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211385 prefixEnd_211385 := by exact prefixLift 211385
  have htrace : WordTrace (prefixWord ++ tailWord_211385) baseStart_211385 baseEnd_211385 := by
    simpa [prefixWord, tailWord_211385, baseEnd_211385] using wordTrace_append hprefix tailTrace_211385
  have hstable : (prefixWord ++ tailWord_211385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211385).length < 2 ^ (prefixWord ++ tailWord_211385).sum := by decide
  have hdescent : baseEnd_211385 < baseStart_211385 := by decide
  rcases family_descends (prefixWord ++ tailWord_211385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211423 : List Nat := [1, 1, 2, 3, 3, 3, 2, 5]
def baseStart_211423 : Nat := 118140960795 + 211423 * 2 ^ 59
def prefixEnd_211423 : Nat := 4983230072969 + 3 ^ 40 * 211423 * 2
def baseEnd_211423 : Nat := 32166406049076011923019

theorem tailTrace_211423 : CollatzResearch.WordTrace tailWord_211423 prefixEnd_211423 32166406049076011923019 := by
  unfold tailWord_211423
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711230313058054018790923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5140820208705369345860615 7711230313058054018790923)
  ·
    refine ⟨11566845469587081028186385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711230313058054018790923 11566845469587081028186385)
    ·
      refine ⟨8675134102190310771139789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11566845469587081028186385 8675134102190310771139789)
      ·
        refine ⟨3253175288321366539177421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8675134102190310771139789 3253175288321366539177421)
        ·
          refine ⟨1219940733120512452191533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3253175288321366539177421 1219940733120512452191533)
          ·
            refine ⟨457477774920192169571825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1219940733120512452191533 457477774920192169571825)
            ·
              refine ⟨343108331190144127178869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457477774920192169571825 343108331190144127178869)
              ·
                refine ⟨32166406049076011923019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343108331190144127178869 32166406049076011923019)
                ·
                  rfl

theorem cell20_211423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_211423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211423 prefixEnd_211423 := by exact prefixLift 211423
  have htrace : WordTrace (prefixWord ++ tailWord_211423) baseStart_211423 baseEnd_211423 := by
    simpa [prefixWord, tailWord_211423, baseEnd_211423] using wordTrace_append hprefix tailTrace_211423
  have hstable : (prefixWord ++ tailWord_211423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211423).length < 2 ^ (prefixWord ++ tailWord_211423).sum := by decide
  have hdescent : baseEnd_211423 < baseStart_211423 := by decide
  rcases family_descends (prefixWord ++ tailWord_211423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211475 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_211475 : Nat := 118140960795 + 211475 * 2 ^ 59
def prefixEnd_211475 : Nat := 4983230072969 + 3 ^ 40 * 211475 * 2
def baseEnd_211475 : Nat := 96522952364146966035511

theorem tailTrace_211475 : CollatzResearch.WordTrace tailWord_211475 prefixEnd_211475 96522952364146966035511 := by
  unfold tailWord_211475
  simp only [CollatzResearch.WordTrace]
  refine ⟨7713126908869666899683879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5142084605913111266455919 7713126908869666899683879)
  ·
    refine ⟨11569690363304500349525819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7713126908869666899683879 11569690363304500349525819)
    ·
      refine ⟨17354535544956750524288729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11569690363304500349525819 17354535544956750524288729)
      ·
        refine ⟨13015901658717562893216547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17354535544956750524288729 13015901658717562893216547)
        ·
          refine ⟨19523852488076344339824821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13015901658717562893216547 19523852488076344339824821)
          ·
            refine ⟨1830361170757157281858577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19523852488076344339824821 1830361170757157281858577)
            ·
              refine ⟨1372770878067867961393933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830361170757157281858577 1372770878067867961393933)
              ·
                refine ⟨514789079275450485522725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1372770878067867961393933 514789079275450485522725)
                ·
                  refine ⟨96522952364146966035511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514789079275450485522725 96522952364146966035511)
                  ·
                    rfl

theorem cell20_211475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_211475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211475 prefixEnd_211475 := by exact prefixLift 211475
  have htrace : WordTrace (prefixWord ++ tailWord_211475) baseStart_211475 baseEnd_211475 := by
    simpa [prefixWord, tailWord_211475, baseEnd_211475] using wordTrace_append hprefix tailTrace_211475
  have hstable : (prefixWord ++ tailWord_211475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211475).length < 2 ^ (prefixWord ++ tailWord_211475).sum := by decide
  have hdescent : baseEnd_211475 < baseStart_211475 := by decide
  rcases family_descends (prefixWord ++ tailWord_211475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211485 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 3]
def baseStart_211485 : Nat := 118140960795 + 211485 * 2 ^ 59
def prefixEnd_211485 : Nat := 4983230072969 + 3 ^ 40 * 211485 * 2
def baseEnd_211485 : Nat := 96527516636631375702137

theorem tailTrace_211485 : CollatzResearch.WordTrace tailWord_211485 prefixEnd_211485 96527516636631375702137 := by
  unfold tailWord_211485
  simp only [CollatzResearch.WordTrace]
  refine ⟨7713491638833438607547909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5142327759222292405031939 7713491638833438607547909)
  ·
    refine ⟨1446279682281269738915233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7713491638833438607547909 1446279682281269738915233)
    ·
      refine ⟨1084709761710952304186425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1446279682281269738915233 1084709761710952304186425)
      ·
        refine ⟨813532321283214228139819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1084709761710952304186425 813532321283214228139819)
        ·
          refine ⟨1220298481924821342209729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813532321283214228139819 1220298481924821342209729)
          ·
            refine ⟨915223861443616006657297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220298481924821342209729 915223861443616006657297)
            ·
              refine ⟨686417896082712004992973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915223861443616006657297 686417896082712004992973)
              ·
                refine ⟨257406711031017001872365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 686417896082712004992973 257406711031017001872365)
                ·
                  refine ⟨96527516636631375702137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257406711031017001872365 96527516636631375702137)
                  ·
                    rfl

theorem cell20_211485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_211485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211485 prefixEnd_211485 := by exact prefixLift 211485
  have htrace : WordTrace (prefixWord ++ tailWord_211485) baseStart_211485 baseEnd_211485 := by
    simpa [prefixWord, tailWord_211485, baseEnd_211485] using wordTrace_append hprefix tailTrace_211485
  have hstable : (prefixWord ++ tailWord_211485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211485).length < 2 ^ (prefixWord ++ tailWord_211485).sum := by decide
  have hdescent : baseEnd_211485 < baseStart_211485 := by decide
  rcases family_descends (prefixWord ++ tailWord_211485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211509 : List Nat := [1, 3, 3, 1, 1, 2, 4, 3, 2]
def baseStart_211509 : Nat := 118140960795 + 211509 * 2 ^ 59
def prefixEnd_211509 : Nat := 4983230072969 + 3 ^ 40 * 211509 * 2
def baseEnd_211509 : Nat := 96538470890593958902039

theorem tailTrace_211509 : CollatzResearch.WordTrace tailWord_211509 prefixEnd_211509 96538470890593958902039 := by
  unfold tailWord_211509
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714366990746490706421581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5142911327164327137614387 7714366990746490706421581)
  ·
    refine ⟨2892887621529934014908093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7714366990746490706421581 2892887621529934014908093)
    ·
      refine ⟨1084832858073725255590535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2892887621529934014908093 1084832858073725255590535)
      ·
        refine ⟨1627249287110587883385803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084832858073725255590535 1627249287110587883385803)
        ·
          refine ⟨2440873930665881825078705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627249287110587883385803 2440873930665881825078705)
          ·
            refine ⟨1830655447999411368809029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440873930665881825078705 1830655447999411368809029)
            ·
              refine ⟨343247896499889631651693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1830655447999411368809029 343247896499889631651693)
              ·
                refine ⟨128717961187458611869385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343247896499889631651693 128717961187458611869385)
                ·
                  refine ⟨96538470890593958902039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128717961187458611869385 96538470890593958902039)
                  ·
                    rfl

theorem cell20_211509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_211509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211509 prefixEnd_211509 := by exact prefixLift 211509
  have htrace : WordTrace (prefixWord ++ tailWord_211509) baseStart_211509 baseEnd_211509 := by
    simpa [prefixWord, tailWord_211509, baseEnd_211509] using wordTrace_append hprefix tailTrace_211509
  have hstable : (prefixWord ++ tailWord_211509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211509).length < 2 ^ (prefixWord ++ tailWord_211509).sum := by decide
  have hdescent : baseEnd_211509 < baseStart_211509 := by decide
  rcases family_descends (prefixWord ++ tailWord_211509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211513 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_211513 : Nat := 118140960795 + 211513 * 2 ^ 59
def prefixEnd_211513 : Nat := 4983230072969 + 3 ^ 40 * 211513 * 2
def baseEnd_211513 : Nat := 96540296599587722768689

theorem tailTrace_211513 : CollatzResearch.WordTrace tailWord_211513 prefixEnd_211513 96540296599587722768689 := by
  unfold tailWord_211513
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714512882731999389567193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5143008588487999593044795 7714512882731999389567193)
  ·
    refine ⟨5785884662048999542175395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7714512882731999389567193 5785884662048999542175395)
    ·
      refine ⟨8678826993073499313263093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785884662048999542175395 8678826993073499313263093)
      ·
        refine ⟨813640030600640560618415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8678826993073499313263093 813640030600640560618415)
        ·
          refine ⟨1220460045900960840927623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813640030600640560618415 1220460045900960840927623)
          ·
            refine ⟨1830690068851441261391435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220460045900960840927623 1830690068851441261391435)
            ·
              refine ⟨2746035103277161892087153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830690068851441261391435 2746035103277161892087153)
              ·
                refine ⟨2059526327457871419065365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746035103277161892087153 2059526327457871419065365)
                ·
                  refine ⟨96540296599587722768689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2059526327457871419065365 96540296599587722768689)
                  ·
                    rfl

theorem cell20_211513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_211513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211513 prefixEnd_211513 := by exact prefixLift 211513
  have htrace : WordTrace (prefixWord ++ tailWord_211513) baseStart_211513 baseEnd_211513 := by
    simpa [prefixWord, tailWord_211513, baseEnd_211513] using wordTrace_append hprefix tailTrace_211513
  have hstable : (prefixWord ++ tailWord_211513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211513).length < 2 ^ (prefixWord ++ tailWord_211513).sum := by decide
  have hdescent : baseEnd_211513 < baseStart_211513 := by decide
  rcases family_descends (prefixWord ++ tailWord_211513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211526 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_211526 : Nat := 118140960795 + 211526 * 2 ^ 59
def prefixEnd_211526 : Nat := 4983230072969 + 3 ^ 40 * 211526 * 2
def baseEnd_211526 : Nat := 96546230153817455335303

theorem tailTrace_211526 : CollatzResearch.WordTrace tailWord_211526 prefixEnd_211526 96546230153817455335303 := by
  unfold tailWord_211526
  simp only [CollatzResearch.WordTrace]
  refine ⟨241093344740153206555951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5143324687789935073193621 241093344740153206555951)
  ·
    refine ⟨361640017110229809833927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241093344740153206555951 361640017110229809833927)
    ·
      refine ⟨542460025665344714750891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361640017110229809833927 542460025665344714750891)
      ·
        refine ⟨813690038498017072126337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542460025665344714750891 813690038498017072126337)
        ·
          refine ⟨610267528873512804094753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813690038498017072126337 610267528873512804094753)
          ·
            refine ⟨457700646655134603071065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610267528873512804094753 457700646655134603071065)
            ·
              refine ⟨343275484991350952303299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457700646655134603071065 343275484991350952303299)
              ·
                refine ⟨514913227487026428454949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343275484991350952303299 514913227487026428454949)
                ·
                  refine ⟨96546230153817455335303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514913227487026428454949 96546230153817455335303)
                  ·
                    rfl

theorem cell20_211526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_211526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211526 prefixEnd_211526 := by exact prefixLift 211526
  have htrace : WordTrace (prefixWord ++ tailWord_211526) baseStart_211526 baseEnd_211526 := by
    simpa [prefixWord, tailWord_211526, baseEnd_211526] using wordTrace_append hprefix tailTrace_211526
  have hstable : (prefixWord ++ tailWord_211526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211526).length < 2 ^ (prefixWord ++ tailWord_211526).sum := by decide
  have hdescent : baseEnd_211526 < baseStart_211526 := by decide
  rcases family_descends (prefixWord ++ tailWord_211526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211530 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_211530 : Nat := 118140960795 + 211530 * 2 ^ 59
def prefixEnd_211530 : Nat := 4983230072969 + 3 ^ 40 * 211530 * 2
def baseEnd_211530 : Nat := 96548055862811219201953

theorem tailTrace_211530 : CollatzResearch.WordTrace tailWord_211530 prefixEnd_211530 96548055862811219201953 := by
  unfold tailWord_211530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928783230917602823234011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5143421949113607528624029 1928783230917602823234011)
  ·
    refine ⟨2893174846376404234851017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1928783230917602823234011 2893174846376404234851017)
    ·
      refine ⟨2169881134782303176138263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2893174846376404234851017 2169881134782303176138263)
      ·
        refine ⟨3254821702173454764207395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169881134782303176138263 3254821702173454764207395)
        ·
          refine ⟨4882232553260182146311093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254821702173454764207395 4882232553260182146311093)
          ·
            refine ⟨457709301868142076216665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4882232553260182146311093 457709301868142076216665)
            ·
              refine ⟨343281976401106557162499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457709301868142076216665 343281976401106557162499)
              ·
                refine ⟨514922964601659835743749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343281976401106557162499 514922964601659835743749)
                ·
                  refine ⟨96548055862811219201953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514922964601659835743749 96548055862811219201953)
                  ·
                    rfl

theorem cell20_211530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_211530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211530 prefixEnd_211530 := by exact prefixLift 211530
  have htrace : WordTrace (prefixWord ++ tailWord_211530) baseStart_211530 baseEnd_211530 := by
    simpa [prefixWord, tailWord_211530, baseEnd_211530] using wordTrace_append hprefix tailTrace_211530
  have hstable : (prefixWord ++ tailWord_211530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211530).length < 2 ^ (prefixWord ++ tailWord_211530).sum := by decide
  have hdescent : baseEnd_211530 < baseStart_211530 := by decide
  rcases family_descends (prefixWord ++ tailWord_211530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211540 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_211540 : Nat := 118140960795 + 211540 * 2 ^ 59
def prefixEnd_211540 : Nat := 4983230072969 + 3 ^ 40 * 211540 * 2
def baseEnd_211540 : Nat := 96552620135295628868579

theorem tailTrace_211540 : CollatzResearch.WordTrace tailWord_211540 prefixEnd_211540 96552620135295628868579 := by
  unfold tailWord_211540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857748826817091500400037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5143665102422788667200049 3857748826817091500400037)
  ·
    refine ⟨723327905028204656325007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3857748826817091500400037 723327905028204656325007)
    ·
      refine ⟨1084991857542306984487511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723327905028204656325007 1084991857542306984487511)
      ·
        refine ⟨1627487786313460476731267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084991857542306984487511 1627487786313460476731267)
        ·
          refine ⟨2441231679470190715096901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627487786313460476731267 2441231679470190715096901)
          ·
            refine ⟨457730939900660759080669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2441231679470190715096901 457730939900660759080669)
            ·
              refine ⟨171649102462747784655251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457730939900660759080669 171649102462747784655251)
              ·
                refine ⟨257473653694121676982877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171649102462747784655251 257473653694121676982877)
                ·
                  refine ⟨96552620135295628868579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257473653694121676982877 96552620135295628868579)
                  ·
                    rfl

theorem cell20_211540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_211540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211540 prefixEnd_211540 := by exact prefixLift 211540
  have htrace : WordTrace (prefixWord ++ tailWord_211540) baseStart_211540 baseEnd_211540 := by
    simpa [prefixWord, tailWord_211540, baseEnd_211540] using wordTrace_append hprefix tailTrace_211540
  have hstable : (prefixWord ++ tailWord_211540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211540).length < 2 ^ (prefixWord ++ tailWord_211540).sum := by decide
  have hdescent : baseEnd_211540 < baseStart_211540 := by decide
  rcases family_descends (prefixWord ++ tailWord_211540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211544 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_211544 : Nat := 118140960795 + 211544 * 2 ^ 59
def prefixEnd_211544 : Nat := 4983230072969 + 3 ^ 40 * 211544 * 2
def baseEnd_211544 : Nat := 96554445844289392735229

theorem tailTrace_211544 : CollatzResearch.WordTrace tailWord_211544 prefixEnd_211544 96554445844289392735229 := by
  unfold tailWord_211544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857821772809845841972843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5143762363746461122630457 3857821772809845841972843)
  ·
    refine ⟨5786732659214768762959265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3857821772809845841972843 5786732659214768762959265)
    ·
      refine ⟨4340049494411076572219449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5786732659214768762959265 4340049494411076572219449)
      ·
        refine ⟨3255037120808307429164587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4340049494411076572219449 3255037120808307429164587)
        ·
          refine ⟨4882555681212461143746881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255037120808307429164587 4882555681212461143746881)
          ·
            refine ⟨3661916760909345857810161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4882555681212461143746881 3661916760909345857810161)
            ·
              refine ⟨2746437570682009393357621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3661916760909345857810161 2746437570682009393357621)
              ·
                refine ⟨257478522251438380627277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2746437570682009393357621 257478522251438380627277)
                ·
                  refine ⟨96554445844289392735229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257478522251438380627277 96554445844289392735229)
                  ·
                    rfl

theorem cell20_211544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_211544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211544 prefixEnd_211544 := by exact prefixLift 211544
  have htrace : WordTrace (prefixWord ++ tailWord_211544) baseStart_211544 baseEnd_211544 := by
    simpa [prefixWord, tailWord_211544, baseEnd_211544] using wordTrace_append hprefix tailTrace_211544
  have hstable : (prefixWord ++ tailWord_211544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211544).length < 2 ^ (prefixWord ++ tailWord_211544).sum := by decide
  have hdescent : baseEnd_211544 < baseStart_211544 := by decide
  rcases family_descends (prefixWord ++ tailWord_211544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211550 : List Nat := [4, 4, 1, 2, 1, 1, 1, 6]
def baseStart_211550 : Nat := 118140960795 + 211550 * 2 ^ 59
def prefixEnd_211550 : Nat := 4983230072969 + 3 ^ 40 * 211550 * 2
def baseEnd_211550 : Nat := 32185728135926679511735

theorem tailTrace_211550 : CollatzResearch.WordTrace tailWord_211550 prefixEnd_211550 32185728135926679511735 := by
  unfold tailWord_211550
  simp only [CollatzResearch.WordTrace]
  refine ⟨964482797949744338583013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5143908255731969805776069 964482797949744338583013)
  ·
    refine ⟨180840524615577063484315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 964482797949744338583013 180840524615577063484315)
    ·
      refine ⟨271260786923365595226473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180840524615577063484315 271260786923365595226473)
      ·
        refine ⟨203445590192524196419855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271260786923365595226473 203445590192524196419855)
        ·
          refine ⟨305168385288786294629783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203445590192524196419855 305168385288786294629783)
          ·
            refine ⟨457752577933179441944675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305168385288786294629783 457752577933179441944675)
            ·
              refine ⟨686628866899769162917013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457752577933179441944675 686628866899769162917013)
              ·
                refine ⟨32185728135926679511735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686628866899769162917013 32185728135926679511735)
                ·
                  rfl

theorem cell20_211550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_211550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211550 prefixEnd_211550 := by exact prefixLift 211550
  have htrace : WordTrace (prefixWord ++ tailWord_211550) baseStart_211550 baseEnd_211550 := by
    simpa [prefixWord, tailWord_211550, baseEnd_211550] using wordTrace_append hprefix tailTrace_211550
  have hstable : (prefixWord ++ tailWord_211550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211550).length < 2 ^ (prefixWord ++ tailWord_211550).sum := by decide
  have hdescent : baseEnd_211550 < baseStart_211550 := by decide
  rcases family_descends (prefixWord ++ tailWord_211550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211637 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 3]
def baseStart_211637 : Nat := 118140960795 + 211637 * 2 ^ 59
def prefixEnd_211637 : Nat := 4983230072969 + 3 ^ 40 * 211637 * 2
def baseEnd_211637 : Nat := 96596893578394402634849

theorem tailTrace_211637 : CollatzResearch.WordTrace tailWord_211637 prefixEnd_211637 96596893578394402634849 := by
  unfold tailWord_211637
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719035534282768567081165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5146023689521845711387443 7719035534282768567081165)
  ·
    refine ⟨2894638325356038212655437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7719035534282768567081165 2894638325356038212655437)
    ·
      refine ⟨1085489372008514329745789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2894638325356038212655437 1085489372008514329745789)
      ·
        refine ⟨407058514503192873654671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1085489372008514329745789 407058514503192873654671)
        ·
          refine ⟨610587771754789310482007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407058514503192873654671 610587771754789310482007)
          ·
            refine ⟨915881657632183965723011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610587771754789310482007 915881657632183965723011)
            ·
              refine ⟨1373822486448275948584517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915881657632183965723011 1373822486448275948584517)
              ·
                refine ⟨257591716209051740359597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1373822486448275948584517 257591716209051740359597)
                ·
                  refine ⟨96596893578394402634849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257591716209051740359597 96596893578394402634849)
                  ·
                    rfl

theorem cell20_211637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_211637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211637 prefixEnd_211637 := by exact prefixLift 211637
  have htrace : WordTrace (prefixWord ++ tailWord_211637) baseStart_211637 baseEnd_211637 := by
    simpa [prefixWord, tailWord_211637, baseEnd_211637] using wordTrace_append hprefix tailTrace_211637
  have hstable : (prefixWord ++ tailWord_211637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211637).length < 2 ^ (prefixWord ++ tailWord_211637).sum := by decide
  have hdescent : baseEnd_211637 < baseStart_211637 := by decide
  rcases family_descends (prefixWord ++ tailWord_211637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211665 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_211665 : Nat := 118140960795 + 211665 * 2 ^ 59
def prefixEnd_211665 : Nat := 4983230072969 + 3 ^ 40 * 211665 * 2
def baseEnd_211665 : Nat := 96609673541350749701401

theorem tailTrace_211665 : CollatzResearch.WordTrace tailWord_211665 prefixEnd_211665 96609673541350749701401 := by
  unfold tailWord_211665
  simp only [CollatzResearch.WordTrace]
  refine ⟨7720056778181329349100449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5146704518787552899400299 7720056778181329349100449)
  ·
    refine ⟨5790042583635997011825337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7720056778181329349100449 5790042583635997011825337)
    ·
      refine ⟨4342531937726997758869003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5790042583635997011825337 4342531937726997758869003)
      ·
        refine ⟨6513797906590496638303505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4342531937726997758869003 6513797906590496638303505)
        ·
          refine ⟨4885348429942872478727629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6513797906590496638303505 4885348429942872478727629)
          ·
            refine ⟨1832005661228577179522861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4885348429942872478727629 1832005661228577179522861)
            ·
              refine ⟨687002122960716442321073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832005661228577179522861 687002122960716442321073)
              ·
                refine ⟨515251592220537331740805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687002122960716442321073 515251592220537331740805)
                ·
                  refine ⟨96609673541350749701401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515251592220537331740805 96609673541350749701401)
                  ·
                    rfl

theorem cell20_211665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_211665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211665 prefixEnd_211665 := by exact prefixLift 211665
  have htrace : WordTrace (prefixWord ++ tailWord_211665) baseStart_211665 baseEnd_211665 := by
    simpa [prefixWord, tailWord_211665, baseEnd_211665] using wordTrace_append hprefix tailTrace_211665
  have hstable : (prefixWord ++ tailWord_211665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211665).length < 2 ^ (prefixWord ++ tailWord_211665).sum := by decide
  have hdescent : baseEnd_211665 < baseStart_211665 := by decide
  rcases family_descends (prefixWord ++ tailWord_211665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211754 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_211754 : Nat := 118140960795 + 211754 * 2 ^ 59
def prefixEnd_211754 : Nat := 4983230072969 + 3 ^ 40 * 211754 * 2
def baseEnd_211754 : Nat := 96650295566461995734371

theorem tailTrace_211754 : CollatzResearch.WordTrace tailWord_211754 prefixEnd_211754 96650295566461995734371 := by
  unfold tailWord_211754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930825718714724387272579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5148868583239265032726877 1930825718714724387272579)
  ·
    refine ⟨2896238578072086580908869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1930825718714724387272579 2896238578072086580908869)
    ·
      refine ⟨543044733388516233920413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2896238578072086580908869 543044733388516233920413)
      ·
        refine ⟨203641775020693587720155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543044733388516233920413 203641775020693587720155)
        ·
          refine ⟨305462662531040381580233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203641775020693587720155 305462662531040381580233)
          ·
            refine ⟨229096996898280286185175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305462662531040381580233 229096996898280286185175)
            ·
              refine ⟨343645495347420429277763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229096996898280286185175 343645495347420429277763)
              ·
                refine ⟨515468243021130643916645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343645495347420429277763 515468243021130643916645)
                ·
                  refine ⟨96650295566461995734371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515468243021130643916645 96650295566461995734371)
                  ·
                    rfl

theorem cell20_211754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_211754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211754 prefixEnd_211754 := by exact prefixLift 211754
  have htrace : WordTrace (prefixWord ++ tailWord_211754) baseStart_211754 baseEnd_211754 := by
    simpa [prefixWord, tailWord_211754, baseEnd_211754] using wordTrace_append hprefix tailTrace_211754
  have hstable : (prefixWord ++ tailWord_211754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211754).length < 2 ^ (prefixWord ++ tailWord_211754).sum := by decide
  have hdescent : baseEnd_211754 < baseStart_211754 := by decide
  rcases family_descends (prefixWord ++ tailWord_211754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211764 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 3]
def baseStart_211764 : Nat := 118140960795 + 211764 * 2 ^ 59
def prefixEnd_211764 : Nat := 4983230072969 + 3 ^ 40 * 211764 * 2
def baseEnd_211764 : Nat := 96654859838946405400997

theorem tailTrace_211764 : CollatzResearch.WordTrace tailWord_211764 prefixEnd_211764 96654859838946405400997 := by
  unfold tailWord_211764
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861833802411334628477173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5149111736548446171302897 3861833802411334628477173)
  ·
    refine ⟨362046918976062621419735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3861833802411334628477173 362046918976062621419735)
    ·
      refine ⟨543070378464093932129603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362046918976062621419735 543070378464093932129603)
      ·
        refine ⟨814605567696140898194405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543070378464093932129603 814605567696140898194405)
        ·
          refine ⟨152738543943026418411451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 814605567696140898194405 152738543943026418411451)
          ·
            refine ⟨229107815914539627617177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152738543943026418411451 229107815914539627617177)
            ·
              refine ⟨171830861935904720712883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229107815914539627617177 171830861935904720712883)
              ·
                refine ⟨257746292903857081069325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171830861935904720712883 257746292903857081069325)
                ·
                  refine ⟨96654859838946405400997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257746292903857081069325 96654859838946405400997)
                  ·
                    rfl

theorem cell20_211764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_211764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211764 prefixEnd_211764 := by exact prefixLift 211764
  have htrace : WordTrace (prefixWord ++ tailWord_211764) baseStart_211764 baseEnd_211764 := by
    simpa [prefixWord, tailWord_211764, baseEnd_211764] using wordTrace_append hprefix tailTrace_211764
  have hstable : (prefixWord ++ tailWord_211764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211764).length < 2 ^ (prefixWord ++ tailWord_211764).sum := by decide
  have hdescent : baseEnd_211764 < baseStart_211764 := by decide
  rcases family_descends (prefixWord ++ tailWord_211764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211765 : List Nat := [1, 3, 3, 1, 3, 2, 2, 5]
def baseStart_211765 : Nat := 118140960795 + 211765 * 2 ^ 59
def prefixEnd_211765 : Nat := 4983230072969 + 3 ^ 40 * 211765 * 2
def baseEnd_211765 : Nat := 32218438755398282122553

theorem tailTrace_211765 : CollatzResearch.WordTrace tailWord_211765 prefixEnd_211765 32218438755398282122553 := by
  unfold tailWord_211765
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723704077819046427740749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5149136051879364285160499 7723704077819046427740749)
  ·
    refine ⟨2896389029182142410402781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7723704077819046427740749 2896389029182142410402781)
    ·
      refine ⟨1086145885943303403901043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2896389029182142410402781 1086145885943303403901043)
      ·
        refine ⟨1629218828914955105851565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086145885943303403901043 1629218828914955105851565)
        ·
          refine ⟨610957060843108164694337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1629218828914955105851565 610957060843108164694337)
          ·
            refine ⟨458217795632331123520753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610957060843108164694337 458217795632331123520753)
            ·
              refine ⟨343663346724248342640565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458217795632331123520753 343663346724248342640565)
              ·
                refine ⟨32218438755398282122553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343663346724248342640565 32218438755398282122553)
                ·
                  rfl

theorem cell20_211765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_211765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211765 prefixEnd_211765 := by exact prefixLift 211765
  have htrace : WordTrace (prefixWord ++ tailWord_211765) baseStart_211765 baseEnd_211765 := by
    simpa [prefixWord, tailWord_211765, baseEnd_211765] using wordTrace_append hprefix tailTrace_211765
  have hstable : (prefixWord ++ tailWord_211765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211765).length < 2 ^ (prefixWord ++ tailWord_211765).sum := by decide
  have hdescent : baseEnd_211765 < baseStart_211765 := by decide
  rcases family_descends (prefixWord ++ tailWord_211765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211813 : List Nat := [1, 3, 1, 3, 1, 1, 6, 2, 2]
def baseStart_211813 : Nat := 118140960795 + 211813 * 2 ^ 59
def prefixEnd_211813 : Nat := 4983230072969 + 3 ^ 40 * 211813 * 2
def baseEnd_211813 : Nat := 96677224774120012767463

theorem tailTrace_211813 : CollatzResearch.WordTrace tailWord_211813 prefixEnd_211813 96677224774120012767463 := by
  unfold tailWord_211813
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725454781645150625488093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5150303187763433750325395 7725454781645150625488093)
  ·
    refine ⟨2897045543116931484558035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7725454781645150625488093 2897045543116931484558035)
    ·
      refine ⟨4345568314675397226837053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2897045543116931484558035 4345568314675397226837053)
      ·
        refine ⟨1629588118003273960063895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4345568314675397226837053 1629588118003273960063895)
        ·
          refine ⟨2444382177004910940095843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629588118003273960063895 2444382177004910940095843)
          ·
            refine ⟨3666573265507366410143765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444382177004910940095843 3666573265507366410143765)
            ·
              refine ⟨171870621820657800475489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3666573265507366410143765 171870621820657800475489)
              ·
                refine ⟨128902966365493350356617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171870621820657800475489 128902966365493350356617)
                ·
                  refine ⟨96677224774120012767463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128902966365493350356617 96677224774120012767463)
                  ·
                    rfl

theorem cell20_211813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_211813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211813 prefixEnd_211813 := by exact prefixLift 211813
  have htrace : WordTrace (prefixWord ++ tailWord_211813) baseStart_211813 baseEnd_211813 := by
    simpa [prefixWord, tailWord_211813, baseEnd_211813] using wordTrace_append hprefix tailTrace_211813
  have hstable : (prefixWord ++ tailWord_211813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211813).length < 2 ^ (prefixWord ++ tailWord_211813).sum := by decide
  have hdescent : baseEnd_211813 < baseStart_211813 := by decide
  rcases family_descends (prefixWord ++ tailWord_211813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211824 : List Nat := [2, 1, 1, 1, 4, 1, 5, 5]
def baseStart_211824 : Nat := 118140960795 + 211824 * 2 ^ 59
def prefixEnd_211824 : Nat := 4983230072969 + 3 ^ 40 * 211824 * 2
def baseEnd_211824 : Nat := 32227415157950954466917

theorem tailTrace_211824 : CollatzResearch.WordTrace tailWord_211824 prefixEnd_211824 32227415157950954466917 := by
  unfold tailWord_211824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862927992302649752069263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5150570656403533002759017 3862927992302649752069263)
  ·
    refine ⟨5794391988453974628103895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3862927992302649752069263 5794391988453974628103895)
    ·
      refine ⟨8691587982680961942155843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5794391988453974628103895 8691587982680961942155843)
      ·
        refine ⟨13037381974021442913233765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691587982680961942155843 13037381974021442913233765)
        ·
          refine ⟨2444509120129020546231331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13037381974021442913233765 2444509120129020546231331)
          ·
            refine ⟨3666763680193530819346997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444509120129020546231331 3666763680193530819346997)
            ·
              refine ⟨343759095018143514313781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3666763680193530819346997 343759095018143514313781)
              ·
                refine ⟨32227415157950954466917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343759095018143514313781 32227415157950954466917)
                ·
                  rfl

theorem cell20_211824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_211824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211824 prefixEnd_211824 := by exact prefixLift 211824
  have htrace : WordTrace (prefixWord ++ tailWord_211824) baseStart_211824 baseEnd_211824 := by
    simpa [prefixWord, tailWord_211824, baseEnd_211824] using wordTrace_append hprefix tailTrace_211824
  have hstable : (prefixWord ++ tailWord_211824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211824).length < 2 ^ (prefixWord ++ tailWord_211824).sum := by decide
  have hdescent : baseEnd_211824 < baseStart_211824 := by decide
  rcases family_descends (prefixWord ++ tailWord_211824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211872 : List Nat := [2, 1, 1, 4, 1, 1, 4, 4, 2]
def baseStart_211872 : Nat := 118140960795 + 211872 * 2 ^ 59
def prefixEnd_211872 : Nat := 4983230072969 + 3 ^ 40 * 211872 * 2
def baseEnd_211872 : Nat := 96704153981778029800555

theorem tailTrace_211872 : CollatzResearch.WordTrace tailWord_211872 prefixEnd_211872 96704153981778029800555 := by
  unfold tailWord_211872
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863803344215701850942935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5151737792287602467923913 3863803344215701850942935)
  ·
    refine ⟨5795705016323552776414403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3863803344215701850942935 5795705016323552776414403)
    ·
      refine ⟨8693557524485329164621605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795705016323552776414403 8693557524485329164621605)
      ·
        refine ⟨1630042035840999218366551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8693557524485329164621605 1630042035840999218366551)
        ·
          refine ⟨2445063053761498827549827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630042035840999218366551 2445063053761498827549827)
          ·
            refine ⟨3667594580642248241324741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445063053761498827549827 3667594580642248241324741)
            ·
              refine ⟨687673983870421545248389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3667594580642248241324741 687673983870421545248389)
              ·
                refine ⟨128938871975704039734073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687673983870421545248389 128938871975704039734073)
                ·
                  refine ⟨96704153981778029800555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128938871975704039734073 96704153981778029800555)
                  ·
                    rfl

theorem cell20_211872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_211872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211872 prefixEnd_211872 := by exact prefixLift 211872
  have htrace : WordTrace (prefixWord ++ tailWord_211872) baseStart_211872 baseEnd_211872 := by
    simpa [prefixWord, tailWord_211872, baseEnd_211872] using wordTrace_append hprefix tailTrace_211872
  have hstable : (prefixWord ++ tailWord_211872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211872).length < 2 ^ (prefixWord ++ tailWord_211872).sum := by decide
  have hdescent : baseEnd_211872 < baseStart_211872 := by decide
  rcases family_descends (prefixWord ++ tailWord_211872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211893 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_211893 : Nat := 118140960795 + 211893 * 2 ^ 59
def prefixEnd_211893 : Nat := 4983230072969 + 3 ^ 40 * 211893 * 2
def baseEnd_211893 : Nat := 96713738953995290100469

theorem tailTrace_211893 : CollatzResearch.WordTrace tailWord_211893 prefixEnd_211893 96713738953995290100469 := by
  unfold tailWord_211893
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728372621355324288400333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5152248414236882858933555 7728372621355324288400333)
  ·
    refine ⟨2898139733008246608150125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7728372621355324288400333 2898139733008246608150125)
    ·
      refine ⟨1086802399878092478056297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2898139733008246608150125 1086802399878092478056297)
      ·
        refine ⟨815101799908569358542223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086802399878092478056297 815101799908569358542223)
        ·
          refine ⟨1222652699862854037813335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815101799908569358542223 1222652699862854037813335)
          ·
            refine ⟨1833979049794281056720003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222652699862854037813335 1833979049794281056720003)
            ·
              refine ⟨2750968574691421585080005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833979049794281056720003 2750968574691421585080005)
              ·
                refine ⟨515806607754641547202501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2750968574691421585080005 515806607754641547202501)
                ·
                  refine ⟨96713738953995290100469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515806607754641547202501 96713738953995290100469)
                  ·
                    rfl

theorem cell20_211893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_211893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211893 prefixEnd_211893 := by exact prefixLift 211893
  have htrace : WordTrace (prefixWord ++ tailWord_211893) baseStart_211893 baseEnd_211893 := by
    simpa [prefixWord, tailWord_211893, baseEnd_211893] using wordTrace_append hprefix tailTrace_211893
  have hstable : (prefixWord ++ tailWord_211893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211893).length < 2 ^ (prefixWord ++ tailWord_211893).sum := by decide
  have hdescent : baseEnd_211893 < baseStart_211893 := by decide
  rcases family_descends (prefixWord ++ tailWord_211893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211924 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_211924 : Nat := 118140960795 + 211924 * 2 ^ 59
def prefixEnd_211924 : Nat := 4983230072969 + 3 ^ 40 * 211924 * 2
def baseEnd_211924 : Nat := 96727888198696960067009

theorem tailTrace_211924 : CollatzResearch.WordTrace tailWord_211924 prefixEnd_211924 96727888198696960067009 := by
  unfold tailWord_211924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864751642121508291389413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5153002189495344388519217 3864751642121508291389413)
  ·
    refine ⟨724640932897782804635515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3864751642121508291389413 724640932897782804635515)
    ·
      refine ⟨1086961399346674206953273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724640932897782804635515 1086961399346674206953273)
      ·
        refine ⟨815221049510005655214955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086961399346674206953273 815221049510005655214955)
        ·
          refine ⟨1222831574265008482822433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815221049510005655214955 1222831574265008482822433)
          ·
            refine ⟨917123680698756362116825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1222831574265008482822433 917123680698756362116825)
            ·
              refine ⟨687842760524067271587619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917123680698756362116825 687842760524067271587619)
              ·
                refine ⟨1031764140786100907381429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687842760524067271587619 1031764140786100907381429)
                ·
                  refine ⟨96727888198696960067009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1031764140786100907381429 96727888198696960067009)
                  ·
                    rfl

theorem cell20_211924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_211924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211924 prefixEnd_211924 := by exact prefixLift 211924
  have htrace : WordTrace (prefixWord ++ tailWord_211924) baseStart_211924 baseEnd_211924 := by
    simpa [prefixWord, tailWord_211924, baseEnd_211924] using wordTrace_append hprefix tailTrace_211924
  have hstable : (prefixWord ++ tailWord_211924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211924).length < 2 ^ (prefixWord ++ tailWord_211924).sum := by decide
  have hdescent : baseEnd_211924 < baseStart_211924 := by decide
  rcases family_descends (prefixWord ++ tailWord_211924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211952 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_211952 : Nat := 118140960795 + 211952 * 2 ^ 59
def prefixEnd_211952 : Nat := 4983230072969 + 3 ^ 40 * 211952 * 2
def baseEnd_211952 : Nat := 96740668161653307133561

theorem tailTrace_211952 : CollatzResearch.WordTrace tailWord_211952 prefixEnd_211952 96740668161653307133561 := by
  unfold tailWord_211952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865262264070788682399055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5153683018761051576532073 3865262264070788682399055)
  ·
    refine ⟨5797893396106183023598583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3865262264070788682399055 5797893396106183023598583)
    ·
      refine ⟨8696840094159274535397875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5797893396106183023598583 8696840094159274535397875)
      ·
        refine ⟨13045260141238911803096813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8696840094159274535397875 13045260141238911803096813)
        ·
          refine ⟨4891972552964591926161305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13045260141238911803096813 4891972552964591926161305)
          ·
            refine ⟨3668979414723443944620979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4891972552964591926161305 3668979414723443944620979)
            ·
              refine ⟨5503469122085165916931469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668979414723443944620979 5503469122085165916931469)
              ·
                refine ⟨2063800920781937218849301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5503469122085165916931469 2063800920781937218849301)
                ·
                  refine ⟨96740668161653307133561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2063800920781937218849301 96740668161653307133561)
                  ·
                    rfl

theorem cell20_211952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_211952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211952 prefixEnd_211952 := by exact prefixLift 211952
  have htrace : WordTrace (prefixWord ++ tailWord_211952) baseStart_211952 baseEnd_211952 := by
    simpa [prefixWord, tailWord_211952, baseEnd_211952] using wordTrace_append hprefix tailTrace_211952
  have hstable : (prefixWord ++ tailWord_211952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211952).length < 2 ^ (prefixWord ++ tailWord_211952).sum := by decide
  have hdescent : baseEnd_211952 < baseStart_211952 := by decide
  rcases family_descends (prefixWord ++ tailWord_211952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211982 : List Nat := [4, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_211982 : Nat := 118140960795 + 211982 * 2 ^ 59
def prefixEnd_211982 : Nat := 4983230072969 + 3 ^ 40 * 211982 * 2
def baseEnd_211982 : Nat := 96754360979106536133439

theorem tailTrace_211982 : CollatzResearch.WordTrace tailWord_211982 prefixEnd_211982 96754360979106536133439 := by
  unfold tailWord_211982
  simp only [CollatzResearch.WordTrace]
  refine ⟨966452339754111561048775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5154412478688594992260133 966452339754111561048775)
  ·
    refine ⟨1449678509631167341573163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 966452339754111561048775 1449678509631167341573163)
    ·
      refine ⟨2174517764446751012359745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1449678509631167341573163 2174517764446751012359745)
      ·
        refine ⟨1630888323335063259269809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2174517764446751012359745 1630888323335063259269809)
        ·
          refine ⟨1223166242501297444452357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630888323335063259269809 1223166242501297444452357)
          ·
            refine ⟨229343670468993270834817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1223166242501297444452357 229343670468993270834817)
            ·
              refine ⟨172007752851744953126113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229343670468993270834817 172007752851744953126113)
              ·
                refine ⟨129005814638808714844585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172007752851744953126113 129005814638808714844585)
                ·
                  refine ⟨96754360979106536133439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129005814638808714844585 96754360979106536133439)
                  ·
                    rfl

theorem cell20_211982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_211982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_211982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_211982 prefixEnd_211982 := by exact prefixLift 211982
  have htrace : WordTrace (prefixWord ++ tailWord_211982) baseStart_211982 baseEnd_211982 := by
    simpa [prefixWord, tailWord_211982, baseEnd_211982] using wordTrace_append hprefix tailTrace_211982
  have hstable : (prefixWord ++ tailWord_211982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211982).length < 2 ^ (prefixWord ++ tailWord_211982).sum := by decide
  have hdescent : baseEnd_211982 < baseStart_211982 := by decide
  rcases family_descends (prefixWord ++ tailWord_211982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212010 : List Nat := [3, 1, 4, 1, 3, 1, 3, 4]
def baseStart_212010 : Nat := 118140960795 + 212010 * 2 ^ 59
def prefixEnd_212010 : Nat := 4983230072969 + 3 ^ 40 * 212010 * 2
def baseEnd_212010 : Nat := 32255713647354294399997

theorem tailTrace_212010 : CollatzResearch.WordTrace tailWord_212010 prefixEnd_212010 32255713647354294399997 := by
  unfold tailWord_212010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933159990482863317602371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5155093307954302180272989 1933159990482863317602371)
  ·
    refine ⟨2899739985724294976403557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1933159990482863317602371 2899739985724294976403557)
    ·
      refine ⟨543701247323305308075667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2899739985724294976403557 543701247323305308075667)
      ·
        refine ⟨815551870984957962113501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543701247323305308075667 815551870984957962113501)
        ·
          refine ⟨305831951619359235792563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 815551870984957962113501 305831951619359235792563)
          ·
            refine ⟨458747927429038853688845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305831951619359235792563 458747927429038853688845)
            ·
              refine ⟨172030472785889570133317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458747927429038853688845 172030472785889570133317)
              ·
                refine ⟨32255713647354294399997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172030472785889570133317 32255713647354294399997)
                ·
                  rfl

theorem cell20_212010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_212010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212010 prefixEnd_212010 := by exact prefixLift 212010
  have htrace : WordTrace (prefixWord ++ tailWord_212010) baseStart_212010 baseEnd_212010 := by
    simpa [prefixWord, tailWord_212010, baseEnd_212010] using wordTrace_append hprefix tailTrace_212010
  have hstable : (prefixWord ++ tailWord_212010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212010).length < 2 ^ (prefixWord ++ tailWord_212010).sum := by decide
  have hdescent : baseEnd_212010 < baseStart_212010 := by decide
  rcases family_descends (prefixWord ++ tailWord_212010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212020 : List Nat := [2, 5, 1, 2, 1, 2, 2, 3, 2]
def baseStart_212020 : Nat := 118140960795 + 212020 * 2 ^ 59
def prefixEnd_212020 : Nat := 4983230072969 + 3 ^ 40 * 212020 * 2
def baseEnd_212020 : Nat := 96771705214547292866617

theorem tailTrace_212020 : CollatzResearch.WordTrace tailWord_212020 prefixEnd_212020 96771705214547292866617 := by
  unfold tailWord_212020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866502345947612489136757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5155336461263483318849009 3866502345947612489136757)
  ·
    refine ⟨362484594932588670856571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3866502345947612489136757 362484594932588670856571)
    ·
      refine ⟨543726892398883006284857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362484594932588670856571 543726892398883006284857)
      ·
        refine ⟨407795169299162254713643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543726892398883006284857 407795169299162254713643)
        ·
          refine ⟨611692753948743382070465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407795169299162254713643 611692753948743382070465)
          ·
            refine ⟨458769565461557536552849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611692753948743382070465 458769565461557536552849)
            ·
              refine ⟨344077174096168152414637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458769565461557536552849 344077174096168152414637)
              ·
                refine ⟨129028940286063057155489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344077174096168152414637 129028940286063057155489)
                ·
                  refine ⟨96771705214547292866617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129028940286063057155489 96771705214547292866617)
                  ·
                    rfl

theorem cell20_212020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_212020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212020 prefixEnd_212020 := by exact prefixLift 212020
  have htrace : WordTrace (prefixWord ++ tailWord_212020) baseStart_212020 baseEnd_212020 := by
    simpa [prefixWord, tailWord_212020, baseEnd_212020] using wordTrace_append hprefix tailTrace_212020
  have hstable : (prefixWord ++ tailWord_212020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212020).length < 2 ^ (prefixWord ++ tailWord_212020).sum := by decide
  have hdescent : baseEnd_212020 < baseStart_212020 := by decide
  rcases family_descends (prefixWord ++ tailWord_212020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212021 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_212021 : Nat := 118140960795 + 212021 * 2 ^ 59
def prefixEnd_212021 : Nat := 4983230072969 + 3 ^ 40 * 212021 * 2
def baseEnd_212021 : Nat := 96772161641795733833279

theorem tailTrace_212021 : CollatzResearch.WordTrace tailWord_212021 prefixEnd_212021 96772161641795733833279 := by
  unfold tailWord_212021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733041164891602149059917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5155360776594401432706611 7733041164891602149059917)
  ·
    refine ⟨2899890436834350805897469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7733041164891602149059917 2899890436834350805897469)
    ·
      refine ⟨1087458913812881552211551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2899890436834350805897469 1087458913812881552211551)
      ·
        refine ⟨1631188370719322328317327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087458913812881552211551 1631188370719322328317327)
        ·
          refine ⟨2446782556078983492475991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631188370719322328317327 2446782556078983492475991)
          ·
            refine ⟨3670173834118475238713987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446782556078983492475991 3670173834118475238713987)
            ·
              refine ⟨5505260751177712858070981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670173834118475238713987 5505260751177712858070981)
              ·
                refine ⟨1032236390845821160888309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5505260751177712858070981 1032236390845821160888309)
                ·
                  refine ⟨96772161641795733833279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1032236390845821160888309 96772161641795733833279)
                  ·
                    rfl

theorem cell20_212021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_212021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212021 prefixEnd_212021 := by exact prefixLift 212021
  have htrace : WordTrace (prefixWord ++ tailWord_212021) baseStart_212021 baseEnd_212021 := by
    simpa [prefixWord, tailWord_212021, baseEnd_212021] using wordTrace_append hprefix tailTrace_212021
  have hstable : (prefixWord ++ tailWord_212021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212021).length < 2 ^ (prefixWord ++ tailWord_212021).sum := by decide
  have hdescent : baseEnd_212021 < baseStart_212021 := by decide
  rcases family_descends (prefixWord ++ tailWord_212021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212024 : List Nat := [2, 1, 2, 1, 5, 1, 1, 5, 2]
def baseStart_212024 : Nat := 118140960795 + 212024 * 2 ^ 59
def prefixEnd_212024 : Nat := 4983230072969 + 3 ^ 40 * 212024 * 2
def baseEnd_212024 : Nat := 96773530923541056733267

theorem tailTrace_212024 : CollatzResearch.WordTrace tailWord_212024 prefixEnd_212024 96773530923541056733267 := by
  unfold tailWord_212024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866575291940366830709563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5155433722587155774279417 3866575291940366830709563)
  ·
    refine ⟨5799862937910550246064345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3866575291940366830709563 5799862937910550246064345)
    ·
      refine ⟨4349897203432912684548259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5799862937910550246064345 4349897203432912684548259)
      ·
        refine ⟨6524845805149369026822389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349897203432912684548259 6524845805149369026822389)
        ·
          refine ⟨611704294232753346264599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6524845805149369026822389 611704294232753346264599)
          ·
            refine ⟨917556441349130019396899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611704294232753346264599 917556441349130019396899)
            ·
              refine ⟨1376334662023695029095349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917556441349130019396899 1376334662023695029095349)
              ·
                refine ⟨129031374564721408977689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1376334662023695029095349 129031374564721408977689)
                ·
                  refine ⟨96773530923541056733267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129031374564721408977689 96773530923541056733267)
                  ·
                    rfl

theorem cell20_212024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_212024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212024 prefixEnd_212024 := by exact prefixLift 212024
  have htrace : WordTrace (prefixWord ++ tailWord_212024) baseStart_212024 baseEnd_212024 := by
    simpa [prefixWord, tailWord_212024, baseEnd_212024] using wordTrace_append hprefix tailTrace_212024
  have hstable : (prefixWord ++ tailWord_212024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212024).length < 2 ^ (prefixWord ++ tailWord_212024).sum := by decide
  have hdescent : baseEnd_212024 < baseStart_212024 := by decide
  rcases family_descends (prefixWord ++ tailWord_212024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212035 : List Nat := [1, 1, 1, 3, 1, 2, 11]
def baseStart_212035 : Nat := 118140960795 + 212035 * 2 ^ 59
def prefixEnd_212035 : Nat := 4983230072969 + 3 ^ 40 * 212035 * 2
def baseEnd_212035 : Nat := 10753172402585989707395

theorem tailTrace_212035 : CollatzResearch.WordTrace tailWord_212035 prefixEnd_212035 10753172402585989707395 := by
  unfold tailWord_212035
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733551786840882540069559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5155701191227255026713039 7733551786840882540069559)
  ·
    refine ⟨11600327680261323810104339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7733551786840882540069559 11600327680261323810104339)
    ·
      refine ⟨17400491520391985715156509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11600327680261323810104339 17400491520391985715156509)
      ·
        refine ⟨6525184320146994643183691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17400491520391985715156509 6525184320146994643183691)
        ·
          refine ⟨9787776480220491964775537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6525184320146994643183691 9787776480220491964775537)
          ·
            refine ⟨7340832360165368973581653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9787776480220491964775537 7340832360165368973581653)
            ·
              refine ⟨10753172402585989707395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7340832360165368973581653 10753172402585989707395)
              ·
                rfl

theorem cell20_212035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_212035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212035 prefixEnd_212035 := by exact prefixLift 212035
  have htrace : WordTrace (prefixWord ++ tailWord_212035) baseStart_212035 baseEnd_212035 := by
    simpa [prefixWord, tailWord_212035, baseEnd_212035] using wordTrace_append hprefix tailTrace_212035
  have hstable : (prefixWord ++ tailWord_212035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212035).length < 2 ^ (prefixWord ++ tailWord_212035).sum := by decide
  have hdescent : baseEnd_212035 < baseStart_212035 := by decide
  rcases family_descends (prefixWord ++ tailWord_212035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212100 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_212100 : Nat := 118140960795 + 212100 * 2 ^ 59
def prefixEnd_212100 : Nat := 4983230072969 + 3 ^ 40 * 212100 * 2
def baseEnd_212100 : Nat := 96808219394422570199623

theorem tailTrace_212100 : CollatzResearch.WordTrace tailWord_212100 prefixEnd_212100 96808219394422570199623 := by
  unfold tailWord_212100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3867961265802699320592877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5157281687736932427457169 3867961265802699320592877)
  ·
    refine ⟨1450485474676012245222329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3867961265802699320592877 1450485474676012245222329)
    ·
      refine ⟨1087864106007009183916747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1450485474676012245222329 1087864106007009183916747)
      ·
        refine ⟨1631796159010513775875121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087864106007009183916747 1631796159010513775875121)
        ·
          refine ⟨1223847119257885331906341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1631796159010513775875121 1223847119257885331906341)
          ·
            refine ⟨229471334860853499732439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1223847119257885331906341 229471334860853499732439)
            ·
              refine ⟨344207002291280249598659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229471334860853499732439 344207002291280249598659)
              ·
                refine ⟨516310503436920374397989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344207002291280249598659 516310503436920374397989)
                ·
                  refine ⟨96808219394422570199623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516310503436920374397989 96808219394422570199623)
                  ·
                    rfl

theorem cell20_212100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_212100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212100 prefixEnd_212100 := by exact prefixLift 212100
  have htrace : WordTrace (prefixWord ++ tailWord_212100) baseStart_212100 baseEnd_212100 := by
    simpa [prefixWord, tailWord_212100, baseEnd_212100] using wordTrace_append hprefix tailTrace_212100
  have hstable : (prefixWord ++ tailWord_212100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212100).length < 2 ^ (prefixWord ++ tailWord_212100).sum := by decide
  have hdescent : baseEnd_212100 < baseStart_212100 := by decide
  rcases family_descends (prefixWord ++ tailWord_212100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212110 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_212110 : Nat := 118140960795 + 212110 * 2 ^ 59
def prefixEnd_212110 : Nat := 4983230072969 + 3 ^ 40 * 212110 * 2
def baseEnd_212110 : Nat := 96812783666906979866249

theorem tailTrace_212110 : CollatzResearch.WordTrace tailWord_212110 prefixEnd_212110 96812783666906979866249 := by
  unfold tailWord_212110
  simp only [CollatzResearch.WordTrace]
  refine ⟨967035907696146293631223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5157524841046113566033189 967035907696146293631223)
  ·
    refine ⟨1450553861544219440446835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967035907696146293631223 1450553861544219440446835)
    ·
      refine ⟨2175830792316329160670253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450553861544219440446835 2175830792316329160670253)
      ·
        refine ⟨815936547118623435251345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2175830792316329160670253 815936547118623435251345)
        ·
          refine ⟨611952410338967576438509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815936547118623435251345 611952410338967576438509)
          ·
            refine ⟨229482153877112841164441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611952410338967576438509 229482153877112841164441)
            ·
              refine ⟨172111615407834630873331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229482153877112841164441 172111615407834630873331)
              ·
                refine ⟨258167423111751946309997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172111615407834630873331 258167423111751946309997)
                ·
                  refine ⟨96812783666906979866249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258167423111751946309997 96812783666906979866249)
                  ·
                    rfl

theorem cell20_212110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_212110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212110 prefixEnd_212110 := by exact prefixLift 212110
  have htrace : WordTrace (prefixWord ++ tailWord_212110) baseStart_212110 baseEnd_212110 := by
    simpa [prefixWord, tailWord_212110, baseEnd_212110] using wordTrace_append hprefix tailTrace_212110
  have hstable : (prefixWord ++ tailWord_212110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212110).length < 2 ^ (prefixWord ++ tailWord_212110).sum := by decide
  have hdescent : baseEnd_212110 < baseStart_212110 := by decide
  rcases family_descends (prefixWord ++ tailWord_212110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212149 : List Nat := [1, 3, 3, 13]
def baseStart_212149 : Nat := 118140960795 + 212149 * 2 ^ 59
def prefixEnd_212149 : Nat := 4983230072969 + 3 ^ 40 * 212149 * 2
def baseEnd_212149 : Nat := 398479770903687973523

theorem tailTrace_212149 : CollatzResearch.WordTrace tailWord_212149 prefixEnd_212149 398479770903687973523 := by
  unfold tailWord_212149
  simp only [CollatzResearch.WordTrace]
  refine ⟨7737709708427880009719501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5158473138951920006479667 7737709708427880009719501)
  ·
    refine ⟨2901641140660455003644813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7737709708427880009719501 2901641140660455003644813)
    ·
      refine ⟨1088115427747670626366805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2901641140660455003644813 1088115427747670626366805)
      ·
        refine ⟨398479770903687973523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1088115427747670626366805 398479770903687973523)
        ·
          rfl

theorem cell20_212149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 13].length) (baseStart_212149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212149 prefixEnd_212149 := by exact prefixLift 212149
  have htrace : WordTrace (prefixWord ++ tailWord_212149) baseStart_212149 baseEnd_212149 := by
    simpa [prefixWord, tailWord_212149, baseEnd_212149] using wordTrace_append hprefix tailTrace_212149
  have hstable : (prefixWord ++ tailWord_212149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212149).length < 2 ^ (prefixWord ++ tailWord_212149).sum := by decide
  have hdescent : baseEnd_212149 < baseStart_212149 := by decide
  rcases family_descends (prefixWord ++ tailWord_212149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212207 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 3]
def baseStart_212207 : Nat := 118140960795 + 212207 * 2 ^ 59
def prefixEnd_212207 : Nat := 4983230072969 + 3 ^ 40 * 212207 * 2
def baseEnd_212207 : Nat := 96857057110005753632519

theorem tailTrace_212207 : CollatzResearch.WordTrace tailWord_212207 prefixEnd_212207 96857057110005753632519 := by
  unfold tailWord_212207
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739825142217755915330875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5159883428145170610220583 7739825142217755915330875)
  ·
    refine ⟨11609737713326633872996313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7739825142217755915330875 11609737713326633872996313)
    ·
      refine ⟨8707303284994975404747235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11609737713326633872996313 8707303284994975404747235)
      ·
        refine ⟨13060954927492463107120853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8707303284994975404747235 13060954927492463107120853)
        ·
          refine ⟨306116131113104604073145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13060954927492463107120853 306116131113104604073145)
          ·
            refine ⟨229587098334828453054859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306116131113104604073145 229587098334828453054859)
            ·
              refine ⟨344380647502242679582289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229587098334828453054859 344380647502242679582289)
              ·
                refine ⟨258285485626682009686717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344380647502242679582289 258285485626682009686717)
                ·
                  refine ⟨96857057110005753632519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258285485626682009686717 96857057110005753632519)
                  ·
                    rfl

theorem cell20_212207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_212207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212207 prefixEnd_212207 := by exact prefixLift 212207
  have htrace : WordTrace (prefixWord ++ tailWord_212207) baseStart_212207 baseEnd_212207 := by
    simpa [prefixWord, tailWord_212207, baseEnd_212207] using wordTrace_append hprefix tailTrace_212207
  have hstable : (prefixWord ++ tailWord_212207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212207).length < 2 ^ (prefixWord ++ tailWord_212207).sum := by decide
  have hdescent : baseEnd_212207 < baseStart_212207 := by decide
  rcases family_descends (prefixWord ++ tailWord_212207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212211 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_212211 : Nat := 118140960795 + 212211 * 2 ^ 59
def prefixEnd_212211 : Nat := 4983230072969 + 3 ^ 40 * 212211 * 2
def baseEnd_212211 : Nat := 96858882818999517499169

theorem tailTrace_212211 : CollatzResearch.WordTrace tailWord_212211 prefixEnd_212211 96858882818999517499169 := by
  unfold tailWord_212211
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739971034203264598476487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5159980689468843065650991 7739971034203264598476487)
  ·
    refine ⟨11609956551304896897714731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7739971034203264598476487 11609956551304896897714731)
    ·
      refine ⟨17414934826957345346572097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11609956551304896897714731 17414934826957345346572097)
      ·
        refine ⟨13061201120218009009929073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17414934826957345346572097 13061201120218009009929073)
        ·
          refine ⟨9795900840163506757446805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13061201120218009009929073 9795900840163506757446805)
          ·
            refine ⟨459182851882664379255319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9795900840163506757446805 459182851882664379255319)
            ·
              refine ⟨688774277823996568882979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459182851882664379255319 688774277823996568882979)
              ·
                refine ⟨1033161416735994853324469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688774277823996568882979 1033161416735994853324469)
                ·
                  refine ⟨96858882818999517499169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1033161416735994853324469 96858882818999517499169)
                  ·
                    rfl

theorem cell20_212211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_212211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212211 prefixEnd_212211 := by exact prefixLift 212211
  have htrace : WordTrace (prefixWord ++ tailWord_212211) baseStart_212211 baseEnd_212211 := by
    simpa [prefixWord, tailWord_212211, baseEnd_212211] using wordTrace_append hprefix tailTrace_212211
  have hstable : (prefixWord ++ tailWord_212211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212211).length < 2 ^ (prefixWord ++ tailWord_212211).sum := by decide
  have hdescent : baseEnd_212211 < baseStart_212211 := by decide
  rcases family_descends (prefixWord ++ tailWord_212211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212252 : List Nat := [2, 2, 3, 1, 1, 1, 5, 3, 2]
def baseStart_212252 : Nat := 118140960795 + 212252 * 2 ^ 59
def prefixEnd_212252 : Nat := 4983230072969 + 3 ^ 40 * 212252 * 2
def baseEnd_212252 : Nat := 96877596336185597132335

theorem tailTrace_212252 : CollatzResearch.WordTrace tailWord_212252 prefixEnd_212252 96877596336185597132335 := by
  unfold tailWord_212252
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870733213527364300359505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5160977618036485733812673 3870733213527364300359505)
  ·
    refine ⟨2903049910145523225269629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3870733213527364300359505 2903049910145523225269629)
    ·
      refine ⟨1088643716304571209476111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2903049910145523225269629 1088643716304571209476111)
      ·
        refine ⟨1632965574456856814214167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088643716304571209476111 1632965574456856814214167)
        ·
          refine ⟨2449448361685285221321251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632965574456856814214167 2449448361685285221321251)
          ·
            refine ⟨3674172542527927831981877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449448361685285221321251 3674172542527927831981877)
            ·
              refine ⟨344453675861993234248301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3674172542527927831981877 344453675861993234248301)
              ·
                refine ⟨129170128448247462843113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344453675861993234248301 129170128448247462843113)
                ·
                  refine ⟨96877596336185597132335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129170128448247462843113 96877596336185597132335)
                  ·
                    rfl

theorem cell20_212252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_212252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212252 prefixEnd_212252 := by exact prefixLift 212252
  have htrace : WordTrace (prefixWord ++ tailWord_212252) baseStart_212252 baseEnd_212252 := by
    simpa [prefixWord, tailWord_212252, baseEnd_212252] using wordTrace_append hprefix tailTrace_212252
  have hstable : (prefixWord ++ tailWord_212252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212252).length < 2 ^ (prefixWord ++ tailWord_212252).sum := by decide
  have hdescent : baseEnd_212252 < baseStart_212252 := by decide
  rcases family_descends (prefixWord ++ tailWord_212252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212266 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_212266 : Nat := 118140960795 + 212266 * 2 ^ 59
def prefixEnd_212266 : Nat := 4983230072969 + 3 ^ 40 * 212266 * 2
def baseEnd_212266 : Nat := 96883986317663770665611

theorem tailTrace_212266 : CollatzResearch.WordTrace tailWord_212266 prefixEnd_212266 96883986317663770665611 := by
  unfold tailWord_212266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935494262251002247932163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5161318032669339327819101 1935494262251002247932163)
  ·
    refine ⟨2903241393376503371898245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935494262251002247932163 2903241393376503371898245)
    ·
      refine ⟨544357761258094382230921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2903241393376503371898245 544357761258094382230921)
      ·
        refine ⟨408268320943570786673191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544357761258094382230921 408268320943570786673191)
        ·
          refine ⟨612402481415356180009787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408268320943570786673191 612402481415356180009787)
          ·
            refine ⟨918603722123034270014681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612402481415356180009787 918603722123034270014681)
            ·
              refine ⟨688952791592275702511011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918603722123034270014681 688952791592275702511011)
              ·
                refine ⟨1033429187388413553766517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688952791592275702511011 1033429187388413553766517)
                ·
                  refine ⟨96883986317663770665611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1033429187388413553766517 96883986317663770665611)
                  ·
                    rfl

theorem cell20_212266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_212266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212266 prefixEnd_212266 := by exact prefixLift 212266
  have htrace : WordTrace (prefixWord ++ tailWord_212266) baseStart_212266 baseEnd_212266 := by
    simpa [prefixWord, tailWord_212266, baseEnd_212266] using wordTrace_append hprefix tailTrace_212266
  have hstable : (prefixWord ++ tailWord_212266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212266).length < 2 ^ (prefixWord ++ tailWord_212266).sum := by decide
  have hdescent : baseEnd_212266 < baseStart_212266 := by decide
  rcases family_descends (prefixWord ++ tailWord_212266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212269 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 4]
def baseStart_212269 : Nat := 118140960795 + 212269 * 2 ^ 59
def prefixEnd_212269 : Nat := 4983230072969 + 3 ^ 40 * 212269 * 2
def baseEnd_212269 : Nat := 96885355599409093565599

theorem tailTrace_212269 : CollatzResearch.WordTrace tailWord_212269 prefixEnd_212269 96885355599409093565599 := by
  unfold tailWord_212269
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742086467993140504087861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5161390978662093669391907 7742086467993140504087861)
  ·
    refine ⟨725820606374356922258237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7742086467993140504087861 725820606374356922258237)
    ·
      refine ⟨272182727390383845846839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 725820606374356922258237 272182727390383845846839)
      ·
        refine ⟨408274091085575768770259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272182727390383845846839 408274091085575768770259)
        ·
          refine ⟨612411136628363653155389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408274091085575768770259 612411136628363653155389)
          ·
            refine ⟨229654176235636369933271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612411136628363653155389 229654176235636369933271)
            ·
              refine ⟨344481264353454554899907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229654176235636369933271 344481264353454554899907)
              ·
                refine ⟨516721896530181832349861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344481264353454554899907 516721896530181832349861)
                ·
                  refine ⟨96885355599409093565599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516721896530181832349861 96885355599409093565599)
                  ·
                    rfl

theorem cell20_212269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_212269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212269 prefixEnd_212269 := by exact prefixLift 212269
  have htrace : WordTrace (prefixWord ++ tailWord_212269) baseStart_212269 baseEnd_212269 := by
    simpa [prefixWord, tailWord_212269, baseEnd_212269] using wordTrace_append hprefix tailTrace_212269
  have hstable : (prefixWord ++ tailWord_212269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212269).length < 2 ^ (prefixWord ++ tailWord_212269).sum := by decide
  have hdescent : baseEnd_212269 < baseStart_212269 := by decide
  rcases family_descends (prefixWord ++ tailWord_212269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212273 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_212273 : Nat := 118140960795 + 212273 * 2 ^ 59
def prefixEnd_212273 : Nat := 4983230072969 + 3 ^ 40 * 212273 * 2
def baseEnd_212273 : Nat := 96887181308402857432249

theorem tailTrace_212273 : CollatzResearch.WordTrace tailWord_212273 prefixEnd_212273 96887181308402857432249 := by
  unfold tailWord_212273
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742232359978649187233473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5161488239985766124822315 7742232359978649187233473)
  ·
    refine ⟨5806674269983986890425105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7742232359978649187233473 5806674269983986890425105)
    ·
      refine ⟨4355005702487990167818829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5806674269983986890425105 4355005702487990167818829)
      ·
        refine ⟨1633127138432996312932061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4355005702487990167818829 1633127138432996312932061)
        ·
          refine ⟨612422676912373617349523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1633127138432996312932061 612422676912373617349523)
          ·
            refine ⟨918634015368560426024285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612422676912373617349523 918634015368560426024285)
            ·
              refine ⟨344487755763210159759107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 918634015368560426024285 344487755763210159759107)
              ·
                refine ⟨516731633644815239638661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344487755763210159759107 516731633644815239638661)
                ·
                  refine ⟨96887181308402857432249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516731633644815239638661 96887181308402857432249)
                  ·
                    rfl

theorem cell20_212273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_212273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212273 prefixEnd_212273 := by exact prefixLift 212273
  have htrace : WordTrace (prefixWord ++ tailWord_212273) baseStart_212273 baseEnd_212273 := by
    simpa [prefixWord, tailWord_212273, baseEnd_212273] using wordTrace_append hprefix tailTrace_212273
  have hstable : (prefixWord ++ tailWord_212273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212273).length < 2 ^ (prefixWord ++ tailWord_212273).sum := by decide
  have hdescent : baseEnd_212273 < baseStart_212273 := by decide
  rcases family_descends (prefixWord ++ tailWord_212273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212317 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 3]
def baseStart_212317 : Nat := 118140960795 + 212317 * 2 ^ 59
def prefixEnd_212317 : Nat := 4983230072969 + 3 ^ 40 * 212317 * 2
def baseEnd_212317 : Nat := 96907264107334259965403

theorem tailTrace_212317 : CollatzResearch.WordTrace tailWord_212317 prefixEnd_212317 96907264107334259965403 := by
  unfold tailWord_212317
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743837171819244701835205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5162558114546163134556803 7743837171819244701835205)
  ·
    refine ⟨1451969469716108381594101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7743837171819244701835205 1451969469716108381594101)
    ·
      refine ⟨136122137785885160774447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1451969469716108381594101 136122137785885160774447)
      ·
        refine ⟨204183206678827741161671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136122137785885160774447 204183206678827741161671)
        ·
          refine ⟨306274810018241611742507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204183206678827741161671 306274810018241611742507)
          ·
            refine ⟨459412215027362417613761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306274810018241611742507 459412215027362417613761)
            ·
              refine ⟨344559161270521813210321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459412215027362417613761 344559161270521813210321)
              ·
                refine ⟨258419370952891359907741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344559161270521813210321 258419370952891359907741)
                ·
                  refine ⟨96907264107334259965403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258419370952891359907741 96907264107334259965403)
                  ·
                    rfl

theorem cell20_212317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_212317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212317 prefixEnd_212317 := by exact prefixLift 212317
  have htrace : WordTrace (prefixWord ++ tailWord_212317) baseStart_212317 baseEnd_212317 := by
    simpa [prefixWord, tailWord_212317, baseEnd_212317] using wordTrace_append hprefix tailTrace_212317
  have hstable : (prefixWord ++ tailWord_212317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212317).length < 2 ^ (prefixWord ++ tailWord_212317).sum := by decide
  have hdescent : baseEnd_212317 < baseStart_212317 := by decide
  rcases family_descends (prefixWord ++ tailWord_212317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212376 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 3]
def baseStart_212376 : Nat := 118140960795 + 212376 * 2 ^ 59
def prefixEnd_212376 : Nat := 4983230072969 + 3 ^ 40 * 212376 * 2
def baseEnd_212376 : Nat := 96934193314992276998495

theorem tailTrace_212376 : CollatzResearch.WordTrace tailWord_212376 prefixEnd_212376 96934193314992276998495 := by
  unfold tailWord_212376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872994539302748889116491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5163992719070331852155321 3872994539302748889116491)
  ·
    refine ⟨5809491808954123333674737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872994539302748889116491 5809491808954123333674737)
    ·
      refine ⟨4357118856715592500256053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5809491808954123333674737 4357118856715592500256053)
      ·
        refine ⟨408479892817086796899005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4357118856715592500256053 408479892817086796899005)
        ·
          refine ⟨153179959806407548837127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408479892817086796899005 153179959806407548837127)
          ·
            refine ⟨229769939709611323255691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153179959806407548837127 229769939709611323255691)
            ·
              refine ⟨344654909564416984883537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229769939709611323255691 344654909564416984883537)
              ·
                refine ⟨258491182173312738662653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344654909564416984883537 258491182173312738662653)
                ·
                  refine ⟨96934193314992276998495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258491182173312738662653 96934193314992276998495)
                  ·
                    rfl

theorem cell20_212376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_212376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212376 prefixEnd_212376 := by exact prefixLift 212376
  have htrace : WordTrace (prefixWord ++ tailWord_212376) baseStart_212376 baseEnd_212376 := by
    simpa [prefixWord, tailWord_212376, baseEnd_212376] using wordTrace_append hprefix tailTrace_212376
  have hstable : (prefixWord ++ tailWord_212376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212376).length < 2 ^ (prefixWord ++ tailWord_212376).sum := by decide
  have hdescent : baseEnd_212376 < baseStart_212376 := by decide
  rcases family_descends (prefixWord ++ tailWord_212376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212377 : List Nat := [1, 2, 1, 2, 1, 6, 7]
def baseStart_212377 : Nat := 118140960795 + 212377 * 2 ^ 59
def prefixEnd_212377 : Nat := 4983230072969 + 3 ^ 40 * 212377 * 2
def baseEnd_212377 : Nat := 10770516638026746440573

theorem tailTrace_212377 : CollatzResearch.WordTrace tailWord_212377 prefixEnd_212377 10770516638026746440573 := by
  unfold tailWord_212377
  simp only [CollatzResearch.WordTrace]
  refine ⟨7746025551601874949019385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5164017034401249966012923 7746025551601874949019385)
  ·
    refine ⟨5809519163701406211764539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7746025551601874949019385 5809519163701406211764539)
    ·
      refine ⟨8714278745552109317646809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5809519163701406211764539 8714278745552109317646809)
      ·
        refine ⟨6535709059164081988235107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8714278745552109317646809 6535709059164081988235107)
        ·
          refine ⟨9803563588746122982352661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535709059164081988235107 9803563588746122982352661)
          ·
            refine ⟨459542043222474514797781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9803563588746122982352661 459542043222474514797781)
            ·
              refine ⟨10770516638026746440573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 459542043222474514797781 10770516638026746440573)
              ·
                rfl

theorem cell20_212377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_212377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212377 prefixEnd_212377 := by exact prefixLift 212377
  have htrace : WordTrace (prefixWord ++ tailWord_212377) baseStart_212377 baseEnd_212377 := by
    simpa [prefixWord, tailWord_212377, baseEnd_212377] using wordTrace_append hprefix tailTrace_212377
  have hstable : (prefixWord ++ tailWord_212377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212377).length < 2 ^ (prefixWord ++ tailWord_212377).sum := by decide
  have hdescent : baseEnd_212377 < baseStart_212377 := by decide
  rcases family_descends (prefixWord ++ tailWord_212377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212387 : List Nat := [1, 1, 1, 4, 1, 3, 1, 6, 2]
def baseStart_212387 : Nat := 118140960795 + 212387 * 2 ^ 59
def prefixEnd_212387 : Nat := 4983230072969 + 3 ^ 40 * 212387 * 2
def baseEnd_212387 : Nat := 96939214014725127631783

theorem tailTrace_212387 : CollatzResearch.WordTrace tailWord_212387 prefixEnd_212387 96939214014725127631783 := by
  unfold tailWord_212387
  simp only [CollatzResearch.WordTrace]
  refine ⟨7746390281565646656883415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5164260187710431104588943 7746390281565646656883415)
  ·
    refine ⟨11619585422348469985325123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7746390281565646656883415 11619585422348469985325123)
    ·
      refine ⟨17429378133522704977987685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11619585422348469985325123 17429378133522704977987685)
      ·
        refine ⟨3268008400035507183372691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17429378133522704977987685 3268008400035507183372691)
        ·
          refine ⟨4902012600053260775059037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268008400035507183372691 4902012600053260775059037)
          ·
            refine ⟨1838254725019972790647139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4902012600053260775059037 1838254725019972790647139)
            ·
              refine ⟨2757382087529959185970709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838254725019972790647139 2757382087529959185970709)
              ·
                refine ⟨129252285352966836842377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2757382087529959185970709 129252285352966836842377)
                ·
                  refine ⟨96939214014725127631783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129252285352966836842377 96939214014725127631783)
                  ·
                    rfl

theorem cell20_212387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 2].length) (baseStart_212387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212387 prefixEnd_212387 := by exact prefixLift 212387
  have htrace : WordTrace (prefixWord ++ tailWord_212387) baseStart_212387 baseEnd_212387 := by
    simpa [prefixWord, tailWord_212387, baseEnd_212387] using wordTrace_append hprefix tailTrace_212387
  have hstable : (prefixWord ++ tailWord_212387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212387).length < 2 ^ (prefixWord ++ tailWord_212387).sum := by decide
  have hdescent : baseEnd_212387 < baseStart_212387 := by decide
  rcases family_descends (prefixWord ++ tailWord_212387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212408 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_212408 : Nat := 118140960795 + 212408 * 2 ^ 59
def prefixEnd_212408 : Nat := 4983230072969 + 3 ^ 40 * 212408 * 2
def baseEnd_212408 : Nat := 96948798986942387931697

theorem tailTrace_212408 : CollatzResearch.WordTrace tailWord_212408 prefixEnd_212408 96948798986942387931697 := by
  unfold tailWord_212408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873578107244783621698939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5164770809659711495598585 3873578107244783621698939)
  ·
    refine ⟨5810367160867175432548409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3873578107244783621698939 5810367160867175432548409)
    ·
      refine ⟨4357775370650381574411307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5810367160867175432548409 4357775370650381574411307)
      ·
        refine ⟨6536663055975572361616961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4357775370650381574411307 6536663055975572361616961)
        ·
          refine ⟨4902497291981679271212721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6536663055975572361616961 4902497291981679271212721)
          ·
            refine ⟨3676872968986259453409541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4902497291981679271212721 3676872968986259453409541)
            ·
              refine ⟨689413681684923647514289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3676872968986259453409541 689413681684923647514289)
              ·
                refine ⟨517060261263692735635717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689413681684923647514289 517060261263692735635717)
                ·
                  refine ⟨96948798986942387931697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517060261263692735635717 96948798986942387931697)
                  ·
                    rfl

theorem cell20_212408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_212408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212408 prefixEnd_212408 := by exact prefixLift 212408
  have htrace : WordTrace (prefixWord ++ tailWord_212408) baseStart_212408 baseEnd_212408 := by
    simpa [prefixWord, tailWord_212408, baseEnd_212408] using wordTrace_append hprefix tailTrace_212408
  have hstable : (prefixWord ++ tailWord_212408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212408).length < 2 ^ (prefixWord ++ tailWord_212408).sum := by decide
  have hdescent : baseEnd_212408 < baseStart_212408 := by decide
  rcases family_descends (prefixWord ++ tailWord_212408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212438 : List Nat := [5, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_212438 : Nat := 118140960795 + 212438 * 2 ^ 59
def prefixEnd_212438 : Nat := 4983230072969 + 3 ^ 40 * 212438 * 2
def baseEnd_212438 : Nat := 96962491804395616931575

theorem tailTrace_212438 : CollatzResearch.WordTrace tailWord_212438 prefixEnd_212438 96962491804395616931575 := by
  unfold tailWord_212438
  simp only [CollatzResearch.WordTrace]
  refine ⟨484265650273805147936873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5165500269587254911326645 484265650273805147936873)
  ·
    refine ⟨363199237705353860952655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 484265650273805147936873 363199237705353860952655)
    ·
      refine ⟨544798856558030791428983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363199237705353860952655 544798856558030791428983)
      ·
        refine ⟨817198284837046187143475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544798856558030791428983 817198284837046187143475)
        ·
          refine ⟨1225797427255569280715213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817198284837046187143475 1225797427255569280715213)
          ·
            refine ⟨459674035220838480268205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225797427255569280715213 459674035220838480268205)
            ·
              refine ⟨172377763207814430100577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459674035220838480268205 172377763207814430100577)
              ·
                refine ⟨129283322405860822575433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172377763207814430100577 129283322405860822575433)
                ·
                  refine ⟨96962491804395616931575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129283322405860822575433 96962491804395616931575)
                  ·
                    rfl

theorem cell20_212438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_212438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212438 prefixEnd_212438 := by exact prefixLift 212438
  have htrace : WordTrace (prefixWord ++ tailWord_212438) baseStart_212438 baseEnd_212438 := by
    simpa [prefixWord, tailWord_212438, baseEnd_212438] using wordTrace_append hprefix tailTrace_212438
  have hstable : (prefixWord ++ tailWord_212438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212438).length < 2 ^ (prefixWord ++ tailWord_212438).sum := by decide
  have hdescent : baseEnd_212438 < baseStart_212438 := by decide
  rcases family_descends (prefixWord ++ tailWord_212438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212460 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_212460 : Nat := 118140960795 + 212460 * 2 ^ 59
def prefixEnd_212460 : Nat := 4983230072969 + 3 ^ 40 * 212460 * 2
def baseEnd_212460 : Nat := 96972533203861318198151

theorem tailTrace_212460 : CollatzResearch.WordTrace tailWord_212460 prefixEnd_212460 96972533203861318198151 := by
  unfold tailWord_212460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874526405150590062145417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5166035206867453416193889 3874526405150590062145417)
  ·
    refine ⟨2905894803862942546609063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3874526405150590062145417 2905894803862942546609063)
    ·
      refine ⟨4358842205794413819913595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2905894803862942546609063 4358842205794413819913595)
      ·
        refine ⟨6538263308691620729870393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4358842205794413819913595 6538263308691620729870393)
        ·
          refine ⟨4903697481518715547402795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538263308691620729870393 4903697481518715547402795)
          ·
            refine ⟨7355546222278073321104193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903697481518715547402795 7355546222278073321104193)
            ·
              refine ⟨5516659666708554990828145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7355546222278073321104193 5516659666708554990828145)
              ·
                refine ⟨4137494750031416243121109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516659666708554990828145 4137494750031416243121109)
                ·
                  refine ⟨96972533203861318198151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4137494750031416243121109 96972533203861318198151)
                  ·
                    rfl

theorem cell20_212460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_212460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212460 prefixEnd_212460 := by exact prefixLift 212460
  have htrace : WordTrace (prefixWord ++ tailWord_212460) baseStart_212460 baseEnd_212460 := by
    simpa [prefixWord, tailWord_212460, baseEnd_212460] using wordTrace_append hprefix tailTrace_212460
  have hstable : (prefixWord ++ tailWord_212460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212460).length < 2 ^ (prefixWord ++ tailWord_212460).sum := by decide
  have hdescent : baseEnd_212460 < baseStart_212460 := by decide
  rcases family_descends (prefixWord ++ tailWord_212460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212470 : List Nat := [5, 1, 1, 1, 2, 2, 2, 6]
def baseStart_212470 : Nat := 118140960795 + 212470 * 2 ^ 59
def prefixEnd_212470 : Nat := 4983230072969 + 3 ^ 40 * 212470 * 2
def baseEnd_212470 : Nat := 32325699158781909288259

theorem tailTrace_212470 : CollatzResearch.WordTrace tailWord_212470 prefixEnd_212470 32325699158781909288259 := by
  unfold tailWord_212470
  simp only [CollatzResearch.WordTrace]
  refine ⟨484338596266559489509679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5166278360176634554769909 484338596266559489509679)
  ·
    refine ⟨726507894399839234264519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484338596266559489509679 726507894399839234264519)
    ·
      refine ⟨1089761841599758851396779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726507894399839234264519 1089761841599758851396779)
      ·
        refine ⟨1634642762399638277095169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089761841599758851396779 1634642762399638277095169)
        ·
          refine ⟨1225982071799728707821377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1634642762399638277095169 1225982071799728707821377)
          ·
            refine ⟨919486553849796530866033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225982071799728707821377 919486553849796530866033)
            ·
              refine ⟨689614915387347398149525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919486553849796530866033 689614915387347398149525)
              ·
                refine ⟨32325699158781909288259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 689614915387347398149525 32325699158781909288259)
                ·
                  rfl

theorem cell20_212470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_212470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212470 prefixEnd_212470 := by exact prefixLift 212470
  have htrace : WordTrace (prefixWord ++ tailWord_212470) baseStart_212470 baseEnd_212470 := by
    simpa [prefixWord, tailWord_212470, baseEnd_212470] using wordTrace_append hprefix tailTrace_212470
  have hstable : (prefixWord ++ tailWord_212470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212470).length < 2 ^ (prefixWord ++ tailWord_212470).sum := by decide
  have hdescent : baseEnd_212470 < baseStart_212470 := by decide
  rcases family_descends (prefixWord ++ tailWord_212470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212491 : List Nat := [1, 1, 1, 1, 8, 8]
def baseStart_212491 : Nat := 118140960795 + 212491 * 2 ^ 59
def prefixEnd_212491 : Nat := 4983230072969 + 3 ^ 40 * 212491 * 2
def baseEnd_212491 : Nat := 3592099349946777339433

theorem tailTrace_212491 : CollatzResearch.WordTrace tailWord_212491 prefixEnd_212491 3592099349946777339433 := by
  unfold tailWord_212491
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750183473188872418669327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5166788982125914945779551 7750183473188872418669327)
  ·
    refine ⟨11625275209783308628003991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7750183473188872418669327 11625275209783308628003991)
    ·
      refine ⟨17437912814674962942005987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11625275209783308628003991 17437912814674962942005987)
      ·
        refine ⟨26156869222012444413008981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17437912814674962942005987 26156869222012444413008981)
        ·
          refine ⟨306525811195458332964949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 26156869222012444413008981 306525811195458332964949)
          ·
            refine ⟨3592099349946777339433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 306525811195458332964949 3592099349946777339433)
            ·
              rfl

theorem cell20_212491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 8].length) (baseStart_212491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212491 prefixEnd_212491 := by exact prefixLift 212491
  have htrace : WordTrace (prefixWord ++ tailWord_212491) baseStart_212491 baseEnd_212491 := by
    simpa [prefixWord, tailWord_212491, baseEnd_212491] using wordTrace_append hprefix tailTrace_212491
  have hstable : (prefixWord ++ tailWord_212491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212491).length < 2 ^ (prefixWord ++ tailWord_212491).sum := by decide
  have hdescent : baseEnd_212491 < baseStart_212491 := by decide
  rcases family_descends (prefixWord ++ tailWord_212491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212560 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_212560 : Nat := 118140960795 + 212560 * 2 ^ 59
def prefixEnd_212560 : Nat := 4983230072969 + 3 ^ 40 * 212560 * 2
def baseEnd_212560 : Nat := 97018175928705414864409

theorem tailTrace_212560 : CollatzResearch.WordTrace tailWord_212560 prefixEnd_212560 97018175928705414864409 := by
  unfold tailWord_212560
  simp only [CollatzResearch.WordTrace]
  refine ⟨3876350054969448601465567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5168466739959264801954089 3876350054969448601465567)
  ·
    refine ⟨5814525082454172902198351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3876350054969448601465567 5814525082454172902198351)
    ·
      refine ⟨8721787623681259353297527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814525082454172902198351 8721787623681259353297527)
      ·
        refine ⟨13082681435521889029946291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8721787623681259353297527 13082681435521889029946291)
        ·
          refine ⟨19624022153282833544919437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082681435521889029946291 19624022153282833544919437)
          ·
            refine ⟨7359008307481062579344789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19624022153282833544919437 7359008307481062579344789)
            ·
              refine ⟨344953514413174808406787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7359008307481062579344789 344953514413174808406787)
              ·
                refine ⟨517430271619762212610181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344953514413174808406787 517430271619762212610181)
                ·
                  refine ⟨97018175928705414864409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517430271619762212610181 97018175928705414864409)
                  ·
                    rfl

theorem cell20_212560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_212560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212560 prefixEnd_212560 := by exact prefixLift 212560
  have htrace : WordTrace (prefixWord ++ tailWord_212560) baseStart_212560 baseEnd_212560 := by
    simpa [prefixWord, tailWord_212560, baseEnd_212560] using wordTrace_append hprefix tailTrace_212560
  have hstable : (prefixWord ++ tailWord_212560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212560).length < 2 ^ (prefixWord ++ tailWord_212560).sum := by decide
  have hdescent : baseEnd_212560 < baseStart_212560 := by decide
  rcases family_descends (prefixWord ++ tailWord_212560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212584 : List Nat := [2, 1, 4, 3, 1, 2, 1, 6]
def baseStart_212584 : Nat := 118140960795 + 212584 * 2 ^ 59
def prefixEnd_212584 : Nat := 4983230072969 + 3 ^ 40 * 212584 * 2
def baseEnd_212584 : Nat := 32343043394222666021437

theorem tailTrace_212584 : CollatzResearch.WordTrace tailWord_212584 prefixEnd_212584 32343043394222666021437 := by
  unfold tailWord_212584
  simp only [CollatzResearch.WordTrace]
  refine ⟨3876787730925974650902403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5169050307901299534536537 3876787730925974650902403)
  ·
    refine ⟨5815181596388961976353605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3876787730925974650902403 5815181596388961976353605)
    ·
      refine ⟨1090346549322930370566301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5815181596388961976353605 1090346549322930370566301)
      ·
        refine ⟨408879955996098888962363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1090346549322930370566301 408879955996098888962363)
        ·
          refine ⟨613319933994148333443545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408879955996098888962363 613319933994148333443545)
          ·
            refine ⟨459989950495611250082659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613319933994148333443545 459989950495611250082659)
            ·
              refine ⟨689984925743416875123989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459989950495611250082659 689984925743416875123989)
              ·
                refine ⟨32343043394222666021437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 689984925743416875123989 32343043394222666021437)
                ·
                  rfl

theorem cell20_212584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_212584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212584 prefixEnd_212584 := by exact prefixLift 212584
  have htrace : WordTrace (prefixWord ++ tailWord_212584) baseStart_212584 baseEnd_212584 := by
    simpa [prefixWord, tailWord_212584, baseEnd_212584] using wordTrace_append hprefix tailTrace_212584
  have hstable : (prefixWord ++ tailWord_212584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212584).length < 2 ^ (prefixWord ++ tailWord_212584).sum := by decide
  have hdescent : baseEnd_212584 < baseStart_212584 := by decide
  rcases family_descends (prefixWord ++ tailWord_212584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212590 : List Nat := [4, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_212590 : Nat := 118140960795 + 212590 * 2 ^ 59
def prefixEnd_212590 : Nat := 4983230072969 + 3 ^ 40 * 212590 * 2
def baseEnd_212590 : Nat := 97031868746158643864287

theorem tailTrace_212590 : CollatzResearch.WordTrace tailWord_212590 prefixEnd_212590 97031868746158643864287 := by
  unfold tailWord_212590
  simp only [CollatzResearch.WordTrace]
  refine ⟨969224287478776540815403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5169196199886808217682149 969224287478776540815403)
  ·
    refine ⟨1453836431218164811223105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969224287478776540815403 1453836431218164811223105)
    ·
      refine ⟨1090377323413623608417329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1453836431218164811223105 1090377323413623608417329)
      ·
        refine ⟨817782992560217706312997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1090377323413623608417329 817782992560217706312997)
        ·
          refine ⟨153334311105040819933687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 817782992560217706312997 153334311105040819933687)
          ·
            refine ⟨230001466657561229900531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153334311105040819933687 230001466657561229900531)
            ·
              refine ⟨345002199986341844850797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230001466657561229900531 345002199986341844850797)
              ·
                refine ⟨129375824994878191819049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345002199986341844850797 129375824994878191819049)
                ·
                  refine ⟨97031868746158643864287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129375824994878191819049 97031868746158643864287)
                  ·
                    rfl

theorem cell20_212590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_212590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212590 prefixEnd_212590 := by exact prefixLift 212590
  have htrace : WordTrace (prefixWord ++ tailWord_212590) baseStart_212590 baseEnd_212590 := by
    simpa [prefixWord, tailWord_212590, baseEnd_212590] using wordTrace_append hprefix tailTrace_212590
  have hstable : (prefixWord ++ tailWord_212590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212590).length < 2 ^ (prefixWord ++ tailWord_212590).sum := by decide
  have hdescent : baseEnd_212590 < baseStart_212590 := by decide
  rcases family_descends (prefixWord ++ tailWord_212590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212594 : List Nat := [3, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_212594 : Nat := 118140960795 + 212594 * 2 ^ 59
def prefixEnd_212594 : Nat := 4983230072969 + 3 ^ 40 * 212594 * 2
def baseEnd_212594 : Nat := 97033694455152407730937

theorem tailTrace_212594 : CollatzResearch.WordTrace tailWord_212594 prefixEnd_212594 97033694455152407730937 := by
  unfold tailWord_212594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938485047953930252417209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5169293461210480673112557 1938485047953930252417209)
  ·
    refine ⟨1453863785965447689312907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1938485047953930252417209 1453863785965447689312907)
    ·
      refine ⟨2180795678948171533969361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1453863785965447689312907 2180795678948171533969361)
      ·
        refine ⟨1635596759211128650477021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2180795678948171533969361 1635596759211128650477021)
        ·
          refine ⟨613348784704173243928883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1635596759211128650477021 613348784704173243928883)
          ·
            refine ⟨920023177056259865893325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613348784704173243928883 920023177056259865893325)
            ·
              refine ⟨345008691396097449709997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 920023177056259865893325 345008691396097449709997)
              ·
                refine ⟨129378259273536543641249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345008691396097449709997 129378259273536543641249)
                ·
                  refine ⟨97033694455152407730937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129378259273536543641249 97033694455152407730937)
                  ·
                    rfl

theorem cell20_212594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_212594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212594 prefixEnd_212594 := by exact prefixLift 212594
  have htrace : WordTrace (prefixWord ++ tailWord_212594) baseStart_212594 baseEnd_212594 := by
    simpa [prefixWord, tailWord_212594, baseEnd_212594] using wordTrace_append hprefix tailTrace_212594
  have hstable : (prefixWord ++ tailWord_212594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212594).length < 2 ^ (prefixWord ++ tailWord_212594).sum := by decide
  have hdescent : baseEnd_212594 < baseStart_212594 := by decide
  rcases family_descends (prefixWord ++ tailWord_212594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212605 : List Nat := [1, 4, 1, 1, 4, 1, 8]
def baseStart_212605 : Nat := 118140960795 + 212605 * 2 ^ 59
def prefixEnd_212605 : Nat := 4983230072969 + 3 ^ 40 * 212605 * 2
def baseEnd_212605 : Nat := 10782079461653917596025

theorem tailTrace_212605 : CollatzResearch.WordTrace tailWord_212605 prefixEnd_212605 10782079461653917596025 := by
  unfold tailWord_212605
  simp only [CollatzResearch.WordTrace]
  refine ⟨7754341394775869888319269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5169560929850579925546179 7754341394775869888319269)
  ·
    refine ⟨1453939011520475604059863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7754341394775869888319269 1453939011520475604059863)
    ·
      refine ⟨2180908517280713406089795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1453939011520475604059863 2180908517280713406089795)
      ·
        refine ⟨3271362775921070109134693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180908517280713406089795 3271362775921070109134693)
        ·
          refine ⟨613380520485200645462755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3271362775921070109134693 613380520485200645462755)
          ·
            refine ⟨920070780727800968194133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613380520485200645462755 920070780727800968194133)
            ·
              refine ⟨10782079461653917596025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 920070780727800968194133 10782079461653917596025)
              ·
                rfl

theorem cell20_212605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_212605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212605 prefixEnd_212605 := by exact prefixLift 212605
  have htrace : WordTrace (prefixWord ++ tailWord_212605) baseStart_212605 baseEnd_212605 := by
    simpa [prefixWord, tailWord_212605, baseEnd_212605] using wordTrace_append hprefix tailTrace_212605
  have hstable : (prefixWord ++ tailWord_212605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212605).length < 2 ^ (prefixWord ++ tailWord_212605).sum := by decide
  have hdescent : baseEnd_212605 < baseStart_212605 := by decide
  rcases family_descends (prefixWord ++ tailWord_212605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212615 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 4]
def baseStart_212615 : Nat := 118140960795 + 212615 * 2 ^ 59
def prefixEnd_212615 : Nat := 4983230072969 + 3 ^ 40 * 212615 * 2
def baseEnd_212615 : Nat := 97043279427369668030851

theorem tailTrace_212615 : CollatzResearch.WordTrace tailWord_212615 prefixEnd_212615 97043279427369668030851 := by
  unfold tailWord_212615
  simp only [CollatzResearch.WordTrace]
  refine ⟨7754706124739641596183299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5169804083159761064122199 7754706124739641596183299)
  ·
    refine ⟨11632059187109462394274949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7754706124739641596183299 11632059187109462394274949)
    ·
      refine ⟨2181011097583024198926553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11632059187109462394274949 2181011097583024198926553)
      ·
        refine ⟨1635758323187268149194915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2181011097583024198926553 1635758323187268149194915)
        ·
          refine ⟨2453637484780902223792373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635758323187268149194915 2453637484780902223792373)
          ·
            refine ⟨230028514198209583480535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2453637484780902223792373 230028514198209583480535)
            ·
              refine ⟨345042771297314375220803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230028514198209583480535 345042771297314375220803)
              ·
                refine ⟨517564156945971562831205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345042771297314375220803 517564156945971562831205)
                ·
                  refine ⟨97043279427369668030851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517564156945971562831205 97043279427369668030851)
                  ·
                    rfl

theorem cell20_212615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_212615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212615 prefixEnd_212615 := by exact prefixLift 212615
  have htrace : WordTrace (prefixWord ++ tailWord_212615) baseStart_212615 baseEnd_212615 := by
    simpa [prefixWord, tailWord_212615, baseEnd_212615] using wordTrace_append hprefix tailTrace_212615
  have hstable : (prefixWord ++ tailWord_212615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212615).length < 2 ^ (prefixWord ++ tailWord_212615).sum := by decide
  have hdescent : baseEnd_212615 < baseStart_212615 := by decide
  rcases family_descends (prefixWord ++ tailWord_212615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212622 : List Nat := [4, 1, 1, 3, 1, 3, 2, 5]
def baseStart_212622 : Nat := 118140960795 + 212622 * 2 ^ 59
def prefixEnd_212622 : Nat := 4983230072969 + 3 ^ 40 * 212622 * 2
def baseEnd_212622 : Nat := 32348824806036251599163

theorem tailTrace_212622 : CollatzResearch.WordTrace tailWord_212622 prefixEnd_212622 32348824806036251599163 := by
  unfold tailWord_212622
  simp only [CollatzResearch.WordTrace]
  refine ⟨969370179464285223961015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5169974290476187861125413 969370179464285223961015)
  ·
    refine ⟨1454055269196427835941523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969370179464285223961015 1454055269196427835941523)
    ·
      refine ⟨2181082903794641753912285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454055269196427835941523 2181082903794641753912285)
      ·
        refine ⟨817906088922990657717107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2181082903794641753912285 817906088922990657717107)
        ·
          refine ⟨1226859133384485986575661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817906088922990657717107 1226859133384485986575661)
          ·
            refine ⟨460072175019182244965873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1226859133384485986575661 460072175019182244965873)
            ·
              refine ⟨345054131264386683724405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460072175019182244965873 345054131264386683724405)
              ·
                refine ⟨32348824806036251599163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345054131264386683724405 32348824806036251599163)
                ·
                  rfl

theorem cell20_212622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_212622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212622 prefixEnd_212622 := by exact prefixLift 212622
  have htrace : WordTrace (prefixWord ++ tailWord_212622) baseStart_212622 baseEnd_212622 := by
    simpa [prefixWord, tailWord_212622, baseEnd_212622] using wordTrace_append hprefix tailTrace_212622
  have hstable : (prefixWord ++ tailWord_212622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212622).length < 2 ^ (prefixWord ++ tailWord_212622).sum := by decide
  have hdescent : baseEnd_212622 < baseStart_212622 := by decide
  rcases family_descends (prefixWord ++ tailWord_212622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212670 : List Nat := [4, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_212670 : Nat := 118140960795 + 212670 * 2 ^ 59
def prefixEnd_212670 : Nat := 4983230072969 + 3 ^ 40 * 212670 * 2
def baseEnd_212670 : Nat := 97068382926033921197293

theorem tailTrace_212670 : CollatzResearch.WordTrace tailWord_212670 prefixEnd_212670 97068382926033921197293 := by
  unfold tailWord_212670
  simp only [CollatzResearch.WordTrace]
  refine ⟨969589017442548248679433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5171141426360257326290309 969589017442548248679433)
  ·
    refine ⟨727191763081911186509575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 969589017442548248679433 727191763081911186509575)
    ·
      refine ⟨1090787644622866779764363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727191763081911186509575 1090787644622866779764363)
      ·
        refine ⟨1636181466934300169646545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090787644622866779764363 1636181466934300169646545)
        ·
          refine ⟨1227136100200725127234909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1636181466934300169646545 1227136100200725127234909)
          ·
            refine ⟨460176037575271922713091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1227136100200725127234909 460176037575271922713091)
            ·
              refine ⟨690264056362907884069637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460176037575271922713091 690264056362907884069637)
              ·
                refine ⟨129424510568045228263057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690264056362907884069637 129424510568045228263057)
                ·
                  refine ⟨97068382926033921197293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129424510568045228263057 97068382926033921197293)
                  ·
                    rfl

theorem cell20_212670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_212670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212670 prefixEnd_212670 := by exact prefixLift 212670
  have htrace : WordTrace (prefixWord ++ tailWord_212670) baseStart_212670 baseEnd_212670 := by
    simpa [prefixWord, tailWord_212670, baseEnd_212670] using wordTrace_append hprefix tailTrace_212670
  have hstable : (prefixWord ++ tailWord_212670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212670).length < 2 ^ (prefixWord ++ tailWord_212670).sum := by decide
  have hdescent : baseEnd_212670 < baseStart_212670 := by decide
  rcases family_descends (prefixWord ++ tailWord_212670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212698 : List Nat := [3, 1, 1, 2, 2, 4, 3, 4]
def baseStart_212698 : Nat := 118140960795 + 212698 * 2 ^ 59
def prefixEnd_212698 : Nat := 4983230072969 + 3 ^ 40 * 212698 * 2
def baseEnd_212698 : Nat := 32360387629663422754615

theorem tailTrace_212698 : CollatzResearch.WordTrace tailWord_212698 prefixEnd_212698 32360387629663422754615 := by
  unfold tailWord_212698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939433345859736692863687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5171822255625964514303165 1939433345859736692863687)
  ·
    refine ⟨2909150018789605039295531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1939433345859736692863687 2909150018789605039295531)
    ·
      refine ⟨4363725028184407558943297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2909150018789605039295531 4363725028184407558943297)
      ·
        refine ⟨3272793771138305669207473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4363725028184407558943297 3272793771138305669207473)
        ·
          refine ⟨2454595328353729251905605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3272793771138305669207473 2454595328353729251905605)
          ·
            refine ⟨460236624066324234732301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2454595328353729251905605 460236624066324234732301)
            ·
              refine ⟨172588734024871588024613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460236624066324234732301 172588734024871588024613)
              ·
                refine ⟨32360387629663422754615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172588734024871588024613 32360387629663422754615)
                ·
                  rfl

theorem cell20_212698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_212698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212698 prefixEnd_212698 := by exact prefixLift 212698
  have htrace : WordTrace (prefixWord ++ tailWord_212698) baseStart_212698 baseEnd_212698 := by
    simpa [prefixWord, tailWord_212698, baseEnd_212698] using wordTrace_append hprefix tailTrace_212698
  have hstable : (prefixWord ++ tailWord_212698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212698).length < 2 ^ (prefixWord ++ tailWord_212698).sum := by decide
  have hdescent : baseEnd_212698 < baseStart_212698 := by decide
  rcases family_descends (prefixWord ++ tailWord_212698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212749 : List Nat := [1, 7, 2, 1, 1, 1, 1, 6]
def baseStart_212749 : Nat := 118140960795 + 212749 * 2 ^ 59
def prefixEnd_212749 : Nat := 4983230072969 + 3 ^ 40 * 212749 * 2
def baseEnd_212749 : Nat := 32368146892886919187879

theorem tailTrace_212749 : CollatzResearch.WordTrace tailWord_212749 prefixEnd_212749 32368146892886919187879 := by
  unfold tailWord_212749
  simp only [CollatzResearch.WordTrace]
  refine ⟨7759593506254182481561301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5173062337502788321040867 7759593506254182481561301)
  ·
    refine ⟨181865472802832401911593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7759593506254182481561301 181865472802832401911593)
    ·
      refine ⟨136399104602124301433695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181865472802832401911593 136399104602124301433695)
      ·
        refine ⟨204598656903186452150543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136399104602124301433695 204598656903186452150543)
        ·
          refine ⟨306897985354779678225815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204598656903186452150543 306897985354779678225815)
          ·
            refine ⟨460346978032169517338723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306897985354779678225815 460346978032169517338723)
            ·
              refine ⟨690520467048254276008085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460346978032169517338723 690520467048254276008085)
              ·
                refine ⟨32368146892886919187879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 690520467048254276008085 32368146892886919187879)
                ·
                  rfl

theorem cell20_212749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6].length) (baseStart_212749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212749 prefixEnd_212749 := by exact prefixLift 212749
  have htrace : WordTrace (prefixWord ++ tailWord_212749) baseStart_212749 baseEnd_212749 := by
    simpa [prefixWord, tailWord_212749, baseEnd_212749] using wordTrace_append hprefix tailTrace_212749
  have hstable : (prefixWord ++ tailWord_212749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212749).length < 2 ^ (prefixWord ++ tailWord_212749).sum := by decide
  have hdescent : baseEnd_212749 < baseStart_212749 := by decide
  rcases family_descends (prefixWord ++ tailWord_212749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212750 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_212750 : Nat := 118140960795 + 212750 * 2 ^ 59
def prefixEnd_212750 : Nat := 4983230072969 + 3 ^ 40 * 212750 * 2
def baseEnd_212750 : Nat := 97104897105909198530299

theorem tailTrace_212750 : CollatzResearch.WordTrace tailWord_212750 prefixEnd_212750 97104897105909198530299 := by
  unfold tailWord_212750
  simp only [CollatzResearch.WordTrace]
  refine ⟨969953747406319956543463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5173086652833706434898469 969953747406319956543463)
  ·
    refine ⟨1454930621109479934815195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969953747406319956543463 1454930621109479934815195)
    ·
      refine ⟨2182395931664219902222793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454930621109479934815195 2182395931664219902222793)
      ·
        refine ⟨1636796948748164926667095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2182395931664219902222793 1636796948748164926667095)
        ·
          refine ⟨2455195423122247390000643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636796948748164926667095 2455195423122247390000643)
          ·
            refine ⟨3682793134683371085000965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455195423122247390000643 3682793134683371085000965)
            ·
              refine ⟨690523712753132078437681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3682793134683371085000965 690523712753132078437681)
              ·
                refine ⟨517892784564849058828261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690523712753132078437681 517892784564849058828261)
                ·
                  refine ⟨97104897105909198530299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517892784564849058828261 97104897105909198530299)
                  ·
                    rfl

theorem cell20_212750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_212750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212750 prefixEnd_212750 := by exact prefixLift 212750
  have htrace : WordTrace (prefixWord ++ tailWord_212750) baseStart_212750 baseEnd_212750 := by
    simpa [prefixWord, tailWord_212750, baseEnd_212750] using wordTrace_append hprefix tailTrace_212750
  have hstable : (prefixWord ++ tailWord_212750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212750).length < 2 ^ (prefixWord ++ tailWord_212750).sum := by decide
  have hdescent : baseEnd_212750 < baseStart_212750 := by decide
  rcases family_descends (prefixWord ++ tailWord_212750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212757 : List Nat := [1, 3, 2, 1, 2, 4, 1, 6]
def baseStart_212757 : Nat := 118140960795 + 212757 * 2 ^ 59
def prefixEnd_212757 : Nat := 4983230072969 + 3 ^ 40 * 212757 * 2
def baseEnd_212757 : Nat := 32369364032216095098979

theorem tailTrace_212757 : CollatzResearch.WordTrace tailWord_212757 prefixEnd_212757 32369364032216095098979 := by
  unfold tailWord_212757
  simp only [CollatzResearch.WordTrace]
  refine ⟨7759885290225199847852525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5173256860150133231901683 7759885290225199847852525)
  ·
    refine ⟨2909956983834449942944697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7759885290225199847852525 2909956983834449942944697)
    ·
      refine ⟨2182467737875837457208523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2909956983834449942944697 2182467737875837457208523)
      ·
        refine ⟨3273701606813756185812785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182467737875837457208523 3273701606813756185812785)
        ·
          refine ⟨2455276205110317139359589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3273701606813756185812785 2455276205110317139359589)
          ·
            refine ⟨460364288458184463629923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2455276205110317139359589 460364288458184463629923)
            ·
              refine ⟨690546432687276695444885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460364288458184463629923 690546432687276695444885)
              ·
                refine ⟨32369364032216095098979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 690546432687276695444885 32369364032216095098979)
                ·
                  rfl

theorem cell20_212757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_212757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212757 prefixEnd_212757 := by exact prefixLift 212757
  have htrace : WordTrace (prefixWord ++ tailWord_212757) baseStart_212757 baseEnd_212757 := by
    simpa [prefixWord, tailWord_212757, baseEnd_212757] using wordTrace_append hprefix tailTrace_212757
  have hstable : (prefixWord ++ tailWord_212757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212757).length < 2 ^ (prefixWord ++ tailWord_212757).sum := by decide
  have hdescent : baseEnd_212757 < baseStart_212757 := by decide
  rcases family_descends (prefixWord ++ tailWord_212757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212764 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_212764 : Nat := 118140960795 + 212764 * 2 ^ 59
def prefixEnd_212764 : Nat := 4983230072969 + 3 ^ 40 * 212764 * 2
def baseEnd_212764 : Nat := 97111287087387372063575

theorem tailTrace_212764 : CollatzResearch.WordTrace tailWord_212764 prefixEnd_212764 97111287087387372063575 := by
  unfold tailWord_212764
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880070300599920021678673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5173427067466560028904897 3880070300599920021678673)
  ·
    refine ⟨2910052725449940016259005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3880070300599920021678673 2910052725449940016259005)
    ·
      refine ⟨1091269772043727506097127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2910052725449940016259005 1091269772043727506097127)
      ·
        refine ⟨1636904658065591259145691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091269772043727506097127 1636904658065591259145691)
        ·
          refine ⟨2455356987098386888718537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636904658065591259145691 2455356987098386888718537)
          ·
            refine ⟨1841517740323790166538903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2455356987098386888718537 1841517740323790166538903)
            ·
              refine ⟨2762276610485685249808355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841517740323790166538903 2762276610485685249808355)
              ·
                refine ⟨4143414915728527874712533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762276610485685249808355 4143414915728527874712533)
                ·
                  refine ⟨97111287087387372063575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4143414915728527874712533 97111287087387372063575)
                  ·
                    rfl

theorem cell20_212764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_212764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212764 prefixEnd_212764 := by exact prefixLift 212764
  have htrace : WordTrace (prefixWord ++ tailWord_212764) baseStart_212764 baseEnd_212764 := by
    simpa [prefixWord, tailWord_212764, baseEnd_212764] using wordTrace_append hprefix tailTrace_212764
  have hstable : (prefixWord ++ tailWord_212764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212764).length < 2 ^ (prefixWord ++ tailWord_212764).sum := by decide
  have hdescent : baseEnd_212764 < baseStart_212764 := by decide
  rcases family_descends (prefixWord ++ tailWord_212764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212771 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_212771 : Nat := 118140960795 + 212771 * 2 ^ 59
def prefixEnd_212771 : Nat := 4983230072969 + 3 ^ 40 * 212771 * 2
def baseEnd_212771 : Nat := 97114482078126458830213

theorem tailTrace_212771 : CollatzResearch.WordTrace tailWord_212771 prefixEnd_212771 97114482078126458830213 := by
  unfold tailWord_212771
  simp only [CollatzResearch.WordTrace]
  refine ⟨7760395912174480238862167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5173597274782986825908111 7760395912174480238862167)
  ·
    refine ⟨11640593868261720358293251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7760395912174480238862167 11640593868261720358293251)
    ·
      refine ⟨17460890802392580537439877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11640593868261720358293251 17460890802392580537439877)
      ·
        refine ⟨3273917025448608850769977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17460890802392580537439877 3273917025448608850769977)
        ·
          refine ⟨2455437769086456638077483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3273917025448608850769977 2455437769086456638077483)
          ·
            refine ⟨3683156653629684957116225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455437769086456638077483 3683156653629684957116225)
            ·
              refine ⟨2762367490222263717837169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3683156653629684957116225 2762367490222263717837169)
              ·
                refine ⟨2071775617666697788377877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2762367490222263717837169 2071775617666697788377877)
                ·
                  refine ⟨97114482078126458830213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2071775617666697788377877 97114482078126458830213)
                  ·
                    rfl

theorem cell20_212771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_212771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212771 prefixEnd_212771 := by exact prefixLift 212771
  have htrace : WordTrace (prefixWord ++ tailWord_212771) baseStart_212771 baseEnd_212771 := by
    simpa [prefixWord, tailWord_212771, baseEnd_212771] using wordTrace_append hprefix tailTrace_212771
  have hstable : (prefixWord ++ tailWord_212771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212771).length < 2 ^ (prefixWord ++ tailWord_212771).sum := by decide
  have hdescent : baseEnd_212771 < baseStart_212771 := by decide
  rcases family_descends (prefixWord ++ tailWord_212771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212798 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_212798 : Nat := 118140960795 + 212798 * 2 ^ 59
def prefixEnd_212798 : Nat := 4983230072969 + 3 ^ 40 * 212798 * 2
def baseEnd_212798 : Nat := 97126805613834364930103

theorem tailTrace_212798 : CollatzResearch.WordTrace tailWord_212798 prefixEnd_212798 97126805613834364930103 := by
  unfold tailWord_212798
  simp only [CollatzResearch.WordTrace]
  refine ⟨970172585384582981261881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5174253788717775900063365 970172585384582981261881)
  ·
    refine ⟨727629439038437235946411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970172585384582981261881 727629439038437235946411)
    ·
      refine ⟨1091444158557655853919617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727629439038437235946411 1091444158557655853919617)
      ·
        refine ⟨818583118918241890439713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1091444158557655853919617 818583118918241890439713)
        ·
          refine ⟨613937339188681417829785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818583118918241890439713 613937339188681417829785)
          ·
            refine ⟨460453004391511063372339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613937339188681417829785 460453004391511063372339)
            ·
              refine ⟨690679506587266595058509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460453004391511063372339 690679506587266595058509)
              ·
                refine ⟨259004814970224973146941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 690679506587266595058509 259004814970224973146941)
                ·
                  refine ⟨97126805613834364930103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259004814970224973146941 97126805613834364930103)
                  ·
                    rfl

theorem cell20_212798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_212798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212798 prefixEnd_212798 := by exact prefixLift 212798
  have htrace : WordTrace (prefixWord ++ tailWord_212798) baseStart_212798 baseEnd_212798 := by
    simpa [prefixWord, tailWord_212798, baseEnd_212798] using wordTrace_append hprefix tailTrace_212798
  have hstable : (prefixWord ++ tailWord_212798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212798).length < 2 ^ (prefixWord ++ tailWord_212798).sum := by decide
  have hdescent : baseEnd_212798 < baseStart_212798 := by decide
  rcases family_descends (prefixWord ++ tailWord_212798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212809 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_212809 : Nat := 118140960795 + 212809 * 2 ^ 59
def prefixEnd_212809 : Nat := 4983230072969 + 3 ^ 40 * 212809 * 2
def baseEnd_212809 : Nat := 97131826313567215563391

theorem tailTrace_212809 : CollatzResearch.WordTrace tailWord_212809 prefixEnd_212809 97131826313567215563391 := by
  unfold tailWord_212809
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761781886036812728745481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5174521257357875152496987 7761781886036812728745481)
  ·
    refine ⟨5821336414527609546559111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7761781886036812728745481 5821336414527609546559111)
    ·
      refine ⟨8732004621791414319838667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821336414527609546559111 8732004621791414319838667)
      ·
        refine ⟨13098006932687121479758001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8732004621791414319838667 13098006932687121479758001)
        ·
          refine ⟨9823505199515341109818501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13098006932687121479758001 9823505199515341109818501)
          ·
            refine ⟨1841907224909126458090969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9823505199515341109818501 1841907224909126458090969)
            ·
              refine ⟨1381430418681844843568227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841907224909126458090969 1381430418681844843568227)
              ·
                refine ⟨2072145628022767265352341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381430418681844843568227 2072145628022767265352341)
                ·
                  refine ⟨97131826313567215563391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2072145628022767265352341 97131826313567215563391)
                  ·
                    rfl

theorem cell20_212809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_212809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212809 prefixEnd_212809 := by exact prefixLift 212809
  have htrace : WordTrace (prefixWord ++ tailWord_212809) baseStart_212809 baseEnd_212809 := by
    simpa [prefixWord, tailWord_212809, baseEnd_212809] using wordTrace_append hprefix tailTrace_212809
  have hstable : (prefixWord ++ tailWord_212809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212809).length < 2 ^ (prefixWord ++ tailWord_212809).sum := by decide
  have hdescent : baseEnd_212809 < baseStart_212809 := by decide
  rcases family_descends (prefixWord ++ tailWord_212809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212836 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_212836 : Nat := 118140960795 + 212836 * 2 ^ 59
def prefixEnd_212836 : Nat := 4983230072969 + 3 ^ 40 * 212836 * 2
def baseEnd_212836 : Nat := 97144149849275121663281

theorem tailTrace_212836 : CollatzResearch.WordTrace tailWord_212836 prefixEnd_212836 97144149849275121663281 := by
  unfold tailWord_212836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881383328469498169989181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5175177771292664226652241 3881383328469498169989181)
  ·
    refine ⟨1455518748176061813745943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3881383328469498169989181 1455518748176061813745943)
    ·
      refine ⟨2183278122264092720618915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455518748176061813745943 2183278122264092720618915)
      ·
        refine ⟨3274917183396139080928373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183278122264092720618915 3274917183396139080928373)
        ·
          refine ⟨307023485943388038837035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3274917183396139080928373 307023485943388038837035)
          ·
            refine ⟨460535228915082058255553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307023485943388038837035 460535228915082058255553)
            ·
              refine ⟨345401421686311543691665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460535228915082058255553 345401421686311543691665)
              ·
                refine ⟨259051066264733657768749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345401421686311543691665 259051066264733657768749)
                ·
                  refine ⟨97144149849275121663281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259051066264733657768749 97144149849275121663281)
                  ·
                    rfl

theorem cell20_212836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_212836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212836 prefixEnd_212836 := by exact prefixLift 212836
  have htrace : WordTrace (prefixWord ++ tailWord_212836) baseStart_212836 baseEnd_212836 := by
    simpa [prefixWord, tailWord_212836, baseEnd_212836] using wordTrace_append hprefix tailTrace_212836
  have hstable : (prefixWord ++ tailWord_212836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212836).length < 2 ^ (prefixWord ++ tailWord_212836).sum := by decide
  have hdescent : baseEnd_212836 < baseStart_212836 := by decide
  rcases family_descends (prefixWord ++ tailWord_212836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212885 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_212885 : Nat := 118140960795 + 212885 * 2 ^ 59
def prefixEnd_212885 : Nat := 4983230072969 + 3 ^ 40 * 212885 * 2
def baseEnd_212885 : Nat := 97166514784448729029747

theorem tailTrace_212885 : CollatzResearch.WordTrace tailWord_212885 prefixEnd_212885 97166514784448729029747 := by
  unfold tailWord_212885
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764553833761477708512109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5176369222507651805674739 7764553833761477708512109)
  ·
    refine ⟨2911707687660554140692041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7764553833761477708512109 2911707687660554140692041)
    ·
      refine ⟨2183780765745415605519031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2911707687660554140692041 2183780765745415605519031)
      ·
        refine ⟨3275671148618123408278547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183780765745415605519031 3275671148618123408278547)
        ·
          refine ⟨4913506722927185112417821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275671148618123408278547 4913506722927185112417821)
          ·
            refine ⟨1842565021097694417156683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4913506722927185112417821 1842565021097694417156683)
            ·
              refine ⟨2763847531646541625735025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842565021097694417156683 2763847531646541625735025)
              ·
                refine ⟨2072885648734906219301269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763847531646541625735025 2072885648734906219301269)
                ·
                  refine ⟨97166514784448729029747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2072885648734906219301269 97166514784448729029747)
                  ·
                    rfl

theorem cell20_212885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_212885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212885 prefixEnd_212885 := by exact prefixLift 212885
  have htrace : WordTrace (prefixWord ++ tailWord_212885) baseStart_212885 baseEnd_212885 := by
    simpa [prefixWord, tailWord_212885, baseEnd_212885] using wordTrace_append hprefix tailTrace_212885
  have hstable : (prefixWord ++ tailWord_212885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212885).length < 2 ^ (prefixWord ++ tailWord_212885).sum := by decide
  have hdescent : baseEnd_212885 < baseStart_212885 := by decide
  rcases family_descends (prefixWord ++ tailWord_212885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212888 : List Nat := [2, 1, 2, 6, 1, 1, 7]
def baseStart_212888 : Nat := 118140960795 + 212888 * 2 ^ 59
def prefixEnd_212888 : Nat := 4983230072969 + 3 ^ 40 * 212888 * 2
def baseEnd_212888 : Nat := 10796431562910450214415

theorem tailTrace_212888 : CollatzResearch.WordTrace tailWord_212888 prefixEnd_212888 10796431562910450214415 := by
  unfold tailWord_212888
  simp only [CollatzResearch.WordTrace]
  refine ⟨3882331626375304610435659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5176442168500406147247545 3882331626375304610435659)
  ·
    refine ⟨5823497439562956915653489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3882331626375304610435659 5823497439562956915653489)
    ·
      refine ⟨4367623079672217686740117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5823497439562956915653489 4367623079672217686740117)
      ·
        refine ⟨204732331859635204065943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4367623079672217686740117 204732331859635204065943)
        ·
          refine ⟨307098497789452806098915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204732331859635204065943 307098497789452806098915)
          ·
            refine ⟨460647746684179209148373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307098497789452806098915 460647746684179209148373)
            ·
              refine ⟨10796431562910450214415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 460647746684179209148373 10796431562910450214415)
              ·
                rfl

theorem cell20_212888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 7].length) (baseStart_212888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212888 prefixEnd_212888 := by exact prefixLift 212888
  have htrace : WordTrace (prefixWord ++ tailWord_212888) baseStart_212888 baseEnd_212888 := by
    simpa [prefixWord, tailWord_212888, baseEnd_212888] using wordTrace_append hprefix tailTrace_212888
  have hstable : (prefixWord ++ tailWord_212888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212888).length < 2 ^ (prefixWord ++ tailWord_212888).sum := by decide
  have hdescent : baseEnd_212888 < baseStart_212888 := by decide
  rcases family_descends (prefixWord ++ tailWord_212888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212895 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 5]
def baseStart_212895 : Nat := 118140960795 + 212895 * 2 ^ 59
def prefixEnd_212895 : Nat := 4983230072969 + 3 ^ 40 * 212895 * 2
def baseEnd_212895 : Nat := 97171079056933138696373

theorem tailTrace_212895 : CollatzResearch.WordTrace tailWord_212895 prefixEnd_212895 97171079056933138696373 := by
  unfold tailWord_212895
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764918563725249416376139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5176612375816832944250759 7764918563725249416376139)
  ·
    refine ⟨11647377845587874124564209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7764918563725249416376139 11647377845587874124564209)
    ·
      refine ⟨8735533384190905593423157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11647377845587874124564209 8735533384190905593423157)
      ·
        refine ⟨818956254767897399383421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8735533384190905593423157 818956254767897399383421)
        ·
          refine ⟨307108595537961524768783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 818956254767897399383421 307108595537961524768783)
          ·
            refine ⟨460662893306942287153175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307108595537961524768783 460662893306942287153175)
            ·
              refine ⟨690994339960413430729763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460662893306942287153175 690994339960413430729763)
              ·
                refine ⟨1036491509940620146094645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690994339960413430729763 1036491509940620146094645)
                ·
                  refine ⟨97171079056933138696373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1036491509940620146094645 97171079056933138696373)
                  ·
                    rfl

theorem cell20_212895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_212895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212895 prefixEnd_212895 := by exact prefixLift 212895
  have htrace : WordTrace (prefixWord ++ tailWord_212895) baseStart_212895 baseEnd_212895 := by
    simpa [prefixWord, tailWord_212895, baseEnd_212895] using wordTrace_append hprefix tailTrace_212895
  have hstable : (prefixWord ++ tailWord_212895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212895).length < 2 ^ (prefixWord ++ tailWord_212895).sum := by decide
  have hdescent : baseEnd_212895 < baseStart_212895 := by decide
  rcases family_descends (prefixWord ++ tailWord_212895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212926 : List Nat := [4, 2, 1, 1, 1, 3, 4, 4]
def baseStart_212926 : Nat := 118140960795 + 212926 * 2 ^ 59
def prefixEnd_212926 : Nat := 4983230072969 + 3 ^ 40 * 212926 * 2
def baseEnd_212926 : Nat := 32395076100544936220971

theorem tailTrace_212926 : CollatzResearch.WordTrace tailWord_212926 prefixEnd_212926 32395076100544936220971 := by
  unfold tailWord_212926
  simp only [CollatzResearch.WordTrace]
  refine ⟨970756153326617713844329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5177366151075294473836421 970756153326617713844329)
  ·
    refine ⟨728067114994963285383247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970756153326617713844329 728067114994963285383247)
    ·
      refine ⟨1092100672492444928074871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728067114994963285383247 1092100672492444928074871)
      ·
        refine ⟨1638151008738667392112307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092100672492444928074871 1638151008738667392112307)
        ·
          refine ⟨2457226513108001088168461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638151008738667392112307 2457226513108001088168461)
          ·
            refine ⟨921459942415500408063173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2457226513108001088168461 921459942415500408063173)
            ·
              refine ⟨172773739202906326511845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 921459942415500408063173 172773739202906326511845)
              ·
                refine ⟨32395076100544936220971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172773739202906326511845 32395076100544936220971)
                ·
                  rfl

theorem cell20_212926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_212926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212926 prefixEnd_212926 := by exact prefixLift 212926
  have htrace : WordTrace (prefixWord ++ tailWord_212926) baseStart_212926 baseEnd_212926 := by
    simpa [prefixWord, tailWord_212926, baseEnd_212926] using wordTrace_append hprefix tailTrace_212926
  have hstable : (prefixWord ++ tailWord_212926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212926).length < 2 ^ (prefixWord ++ tailWord_212926).sum := by decide
  have hdescent : baseEnd_212926 < baseStart_212926 := by decide
  rcases family_descends (prefixWord ++ tailWord_212926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212936 : List Nat := [2, 1, 3, 1, 4, 3, 1, 3, 2]
def baseStart_212936 : Nat := 118140960795 + 212936 * 2 ^ 59
def prefixEnd_212936 : Nat := 4983230072969 + 3 ^ 40 * 212936 * 2
def baseEnd_212936 : Nat := 97189792574119218329539

theorem tailTrace_212936 : CollatzResearch.WordTrace tailWord_212936 prefixEnd_212936 97189792574119218329539 := by
  unfold tailWord_212936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3883206978288356709309331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5177609304384475612412441 3883206978288356709309331)
  ·
    refine ⟨5824810467432535063963997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3883206978288356709309331 5824810467432535063963997)
    ·
      refine ⟨2184303925287200648986499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5824810467432535063963997 2184303925287200648986499)
      ·
        refine ⟨3276455887930800973479749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184303925287200648986499 3276455887930800973479749)
        ·
          refine ⟨614335478987025182527453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3276455887930800973479749 614335478987025182527453)
          ·
            refine ⟨230375804620134443447795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614335478987025182527453 230375804620134443447795)
            ·
              refine ⟨345563706930201665171693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230375804620134443447795 345563706930201665171693)
              ·
                refine ⟨129586390098825624439385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345563706930201665171693 129586390098825624439385)
                ·
                  refine ⟨97189792574119218329539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129586390098825624439385 97189792574119218329539)
                  ·
                    rfl

theorem cell20_212936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_212936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212936 prefixEnd_212936 := by exact prefixLift 212936
  have htrace : WordTrace (prefixWord ++ tailWord_212936) baseStart_212936 baseEnd_212936 := by
    simpa [prefixWord, tailWord_212936, baseEnd_212936] using wordTrace_append hprefix tailTrace_212936
  have hstable : (prefixWord ++ tailWord_212936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212936).length < 2 ^ (prefixWord ++ tailWord_212936).sum := by decide
  have hdescent : baseEnd_212936 < baseStart_212936 := by decide
  rcases family_descends (prefixWord ++ tailWord_212936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212967 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 3]
def baseStart_212967 : Nat := 118140960795 + 212967 * 2 ^ 59
def prefixEnd_212967 : Nat := 4983230072969 + 3 ^ 40 * 212967 * 2
def baseEnd_212967 : Nat := 97203941818820888296079

theorem tailTrace_212967 : CollatzResearch.WordTrace tailWord_212967 prefixEnd_212967 97203941818820888296079 := by
  unfold tailWord_212967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767544619464405712997155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5178363079642937141998103 7767544619464405712997155)
  ·
    refine ⟨11651316929196608569495733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7767544619464405712997155 11651316929196608569495733)
    ·
      refine ⟨1092310962112182053390225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11651316929196608569495733 1092310962112182053390225)
      ·
        refine ⟨819233221584136540042669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1092310962112182053390225 819233221584136540042669)
        ·
          refine ⟨307212458094051202516001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 819233221584136540042669 307212458094051202516001)
          ·
            refine ⟨230409343570538401887001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307212458094051202516001 230409343570538401887001)
            ·
              refine ⟨172807007677903801415251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230409343570538401887001 172807007677903801415251)
              ·
                refine ⟨259210511516855702122877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172807007677903801415251 259210511516855702122877)
                ·
                  refine ⟨97203941818820888296079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259210511516855702122877 97203941818820888296079)
                  ·
                    rfl

theorem cell20_212967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 3].length) (baseStart_212967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212967 prefixEnd_212967 := by exact prefixLift 212967
  have htrace : WordTrace (prefixWord ++ tailWord_212967) baseStart_212967 baseEnd_212967 := by
    simpa [prefixWord, tailWord_212967, baseEnd_212967] using wordTrace_append hprefix tailTrace_212967
  have hstable : (prefixWord ++ tailWord_212967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212967).length < 2 ^ (prefixWord ++ tailWord_212967).sum := by decide
  have hdescent : baseEnd_212967 < baseStart_212967 := by decide
  rcases family_descends (prefixWord ++ tailWord_212967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212998 : List Nat := [6, 2, 1, 2, 1, 8]
def baseStart_212998 : Nat := 118140960795 + 212998 * 2 ^ 59
def prefixEnd_212998 : Nat := 4983230072969 + 3 ^ 40 * 212998 * 2
def baseEnd_212998 : Nat := 3600670039389724380097

theorem tailTrace_212998 : CollatzResearch.WordTrace tailWord_212998 prefixEnd_212998 3600670039389724380097 := by
  unfold tailWord_212998
  simp only [CollatzResearch.WordTrace]
  refine ⟨242771102573503062730489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5179116854901398671583765 242771102573503062730489)
  ·
    refine ⟨182078326930127297047867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242771102573503062730489 182078326930127297047867)
    ·
      refine ⟨273117490395190945571801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182078326930127297047867 273117490395190945571801)
      ·
        refine ⟨204838117796393209178851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273117490395190945571801 204838117796393209178851)
        ·
          refine ⟨307257176694589813768277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204838117796393209178851 307257176694589813768277)
          ·
            refine ⟨3600670039389724380097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 307257176694589813768277 3600670039389724380097)
            ·
              rfl

theorem cell20_212998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 8].length) (baseStart_212998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_212998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_212998 prefixEnd_212998 := by exact prefixLift 212998
  have htrace : WordTrace (prefixWord ++ tailWord_212998) baseStart_212998 baseEnd_212998 := by
    simpa [prefixWord, tailWord_212998, baseEnd_212998] using wordTrace_append hprefix tailTrace_212998
  have hstable : (prefixWord ++ tailWord_212998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212998).length < 2 ^ (prefixWord ++ tailWord_212998).sum := by decide
  have hdescent : baseEnd_212998 < baseStart_212998 := by decide
  rcases family_descends (prefixWord ++ tailWord_212998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213051 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_213051 : Nat := 118140960795 + 213051 * 2 ^ 59
def prefixEnd_213051 : Nat := 4983230072969 + 3 ^ 40 * 213051 * 2
def baseEnd_213051 : Nat := 97242281707689929495735

theorem tailTrace_213051 : CollatzResearch.WordTrace tailWord_213051 prefixEnd_213051 97242281707689929495735 := by
  unfold tailWord_213051
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770608351160088059055007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5180405567440058706036671 7770608351160088059055007)
  ·
    refine ⟨11655912526740132088582511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7770608351160088059055007 11655912526740132088582511)
    ·
      refine ⟨17483868790110198132873767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11655912526740132088582511 17483868790110198132873767)
      ·
        refine ⟨26225803185165297199310651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17483868790110198132873767 26225803185165297199310651)
        ·
          refine ⟨39338704777747945798965977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26225803185165297199310651 39338704777747945798965977)
          ·
            refine ⟨29504028583310959349224483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39338704777747945798965977 29504028583310959349224483)
            ·
              refine ⟨44256042874966439023836725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29504028583310959349224483 44256042874966439023836725)
              ·
                refine ⟨4149004019528103658484693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44256042874966439023836725 4149004019528103658484693)
                ·
                  refine ⟨97242281707689929495735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4149004019528103658484693 97242281707689929495735)
                  ·
                    rfl

theorem cell20_213051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_213051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213051 prefixEnd_213051 := by exact prefixLift 213051
  have htrace : WordTrace (prefixWord ++ tailWord_213051) baseStart_213051 baseEnd_213051 := by
    simpa [prefixWord, tailWord_213051, baseEnd_213051] using wordTrace_append hprefix tailTrace_213051
  have hstable : (prefixWord ++ tailWord_213051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213051).length < 2 ^ (prefixWord ++ tailWord_213051).sum := by decide
  have hdescent : baseEnd_213051 < baseStart_213051 := by decide
  rcases family_descends (prefixWord ++ tailWord_213051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213082 : List Nat := [3, 1, 1, 2, 1, 1, 4, 7]
def baseStart_213082 : Nat := 118140960795 + 213082 * 2 ^ 59
def prefixEnd_213082 : Nat := 4983230072969 + 3 ^ 40 * 213082 * 2
def baseEnd_213082 : Nat := 32418810317463866487425

theorem tailTrace_213082 : CollatzResearch.WordTrace tailWord_213082 prefixEnd_213082 32418810317463866487425 := by
  unfold tailWord_213082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942934753511945088358375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5181159342698520235622333 1942934753511945088358375)
  ·
    refine ⟨2914402130267917632537563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1942934753511945088358375 2914402130267917632537563)
    ·
      refine ⟨4371603195401876448806345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914402130267917632537563 4371603195401876448806345)
      ·
        refine ⟨3278702396551407336604759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4371603195401876448806345 3278702396551407336604759)
        ·
          refine ⟨4918053594827111004907139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3278702396551407336604759 4918053594827111004907139)
          ·
            refine ⟨7377080392240666507360709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918053594827111004907139 7377080392240666507360709)
            ·
              refine ⟨1383202573545124970130133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7377080392240666507360709 1383202573545124970130133)
              ·
                refine ⟨32418810317463866487425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1383202573545124970130133 32418810317463866487425)
                ·
                  rfl

theorem cell20_213082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_213082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213082 prefixEnd_213082 := by exact prefixLift 213082
  have htrace : WordTrace (prefixWord ++ tailWord_213082) baseStart_213082 baseEnd_213082 := by
    simpa [prefixWord, tailWord_213082, baseEnd_213082] using wordTrace_append hprefix tailTrace_213082
  have hstable : (prefixWord ++ tailWord_213082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213082).length < 2 ^ (prefixWord ++ tailWord_213082).sum := by decide
  have hdescent : baseEnd_213082 < baseStart_213082 := by decide
  rcases family_descends (prefixWord ++ tailWord_213082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213106 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_213106 : Nat := 118140960795 + 213106 * 2 ^ 59
def prefixEnd_213106 : Nat := 4983230072969 + 3 ^ 40 * 213106 * 2
def baseEnd_213106 : Nat := 97267385206354182662177

theorem tailTrace_213106 : CollatzResearch.WordTrace tailWord_213106 prefixEnd_213106 97267385206354182662177 := by
  unfold tailWord_213106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943153591490208113076793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5181742910640554968204781 1943153591490208113076793)
  ·
    refine ⟨1457365193617656084807595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1943153591490208113076793 1457365193617656084807595)
    ·
      refine ⟨2186047790426484127211393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1457365193617656084807595 2186047790426484127211393)
      ·
        refine ⟨1639535842819863095408545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2186047790426484127211393 1639535842819863095408545)
        ·
          refine ⟨1229651882114897321556409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1639535842819863095408545 1229651882114897321556409)
          ·
            refine ⟨922238911586172991167307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229651882114897321556409 922238911586172991167307)
            ·
              refine ⟨1383358367379259486750961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922238911586172991167307 1383358367379259486750961)
              ·
                refine ⟨1037518775534444615063221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383358367379259486750961 1037518775534444615063221)
                ·
                  refine ⟨97267385206354182662177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037518775534444615063221 97267385206354182662177)
                  ·
                    rfl

theorem cell20_213106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_213106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213106 prefixEnd_213106 := by exact prefixLift 213106
  have htrace : WordTrace (prefixWord ++ tailWord_213106) baseStart_213106 baseEnd_213106 := by
    simpa [prefixWord, tailWord_213106, baseEnd_213106] using wordTrace_append hprefix tailTrace_213106
  have hstable : (prefixWord ++ tailWord_213106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213106).length < 2 ^ (prefixWord ++ tailWord_213106).sum := by decide
  have hdescent : baseEnd_213106 < baseStart_213106 := by decide
  rcases family_descends (prefixWord ++ tailWord_213106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213130 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_213130 : Nat := 118140960795 + 213130 * 2 ^ 59
def prefixEnd_213130 : Nat := 4983230072969 + 3 ^ 40 * 213130 * 2
def baseEnd_213130 : Nat := 97278339460316765862079

theorem tailTrace_213130 : CollatzResearch.WordTrace tailWord_213130 prefixEnd_213130 97278339460316765862079 := by
  unfold tailWord_213130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943372429468471137795211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5182326478582589700787229 1943372429468471137795211)
  ·
    refine ⟨2915058644202706706692817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1943372429468471137795211 2915058644202706706692817)
    ·
      refine ⟨2186293983152030030019613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2915058644202706706692817 2186293983152030030019613)
      ·
        refine ⟨819860243682011261257355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2186293983152030030019613 819860243682011261257355)
        ·
          refine ⟨1229790365523016891886033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819860243682011261257355 1229790365523016891886033)
          ·
            refine ⟨922342774142262668914525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229790365523016891886033 922342774142262668914525)
            ·
              refine ⟨345878540303348500842947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 922342774142262668914525 345878540303348500842947)
              ·
                refine ⟨518817810455022751264421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345878540303348500842947 518817810455022751264421)
                ·
                  refine ⟨97278339460316765862079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518817810455022751264421 97278339460316765862079)
                  ·
                    rfl

theorem cell20_213130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_213130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213130 prefixEnd_213130 := by exact prefixLift 213130
  have htrace : WordTrace (prefixWord ++ tailWord_213130) baseStart_213130 baseEnd_213130 := by
    simpa [prefixWord, tailWord_213130, baseEnd_213130] using wordTrace_append hprefix tailTrace_213130
  have hstable : (prefixWord ++ tailWord_213130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213130).length < 2 ^ (prefixWord ++ tailWord_213130).sum := by decide
  have hdescent : baseEnd_213130 < baseStart_213130 := by decide
  rcases family_descends (prefixWord ++ tailWord_213130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213223 : List Nat := [1, 1, 5, 3, 1, 1, 1, 5, 2]
def baseStart_213223 : Nat := 118140960795 + 213223 * 2 ^ 59
def prefixEnd_213223 : Nat := 4983230072969 + 3 ^ 40 * 213223 * 2
def baseEnd_213223 : Nat := 97320787194421775761699

theorem tailTrace_213223 : CollatzResearch.WordTrace tailWord_213223 prefixEnd_213223 97320787194421775761699 := by
  unfold tailWord_213223
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776881706536961434316323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5184587804357974289544215 7776881706536961434316323)
  ·
    refine ⟨11665322559805442151474485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7776881706536961434316323 11665322559805442151474485)
    ·
      refine ⟨1093623989981760201700733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11665322559805442151474485 1093623989981760201700733)
      ·
        refine ⟨410108996243160075637775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1093623989981760201700733 410108996243160075637775)
        ·
          refine ⟨615163494364740113456663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410108996243160075637775 615163494364740113456663)
          ·
            refine ⟨922745241547110170184995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615163494364740113456663 922745241547110170184995)
            ·
              refine ⟨1384117862320665255277493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922745241547110170184995 1384117862320665255277493)
              ·
                refine ⟨129761049592562367682265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1384117862320665255277493 129761049592562367682265)
                ·
                  refine ⟨97320787194421775761699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129761049592562367682265 97320787194421775761699)
                  ·
                    rfl

theorem cell20_213223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 2].length) (baseStart_213223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213223 prefixEnd_213223 := by exact prefixLift 213223
  have htrace : WordTrace (prefixWord ++ tailWord_213223) baseStart_213223 baseEnd_213223 := by
    simpa [prefixWord, tailWord_213223, baseEnd_213223] using wordTrace_append hprefix tailTrace_213223
  have hstable : (prefixWord ++ tailWord_213223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213223).length < 2 ^ (prefixWord ++ tailWord_213223).sum := by decide
  have hdescent : baseEnd_213223 < baseStart_213223 := by decide
  rcases family_descends (prefixWord ++ tailWord_213223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213244 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_213244 : Nat := 118140960795 + 213244 * 2 ^ 59
def prefixEnd_213244 : Nat := 4983230072969 + 3 ^ 40 * 213244 * 2
def baseEnd_213244 : Nat := 97330372166639036061613

theorem tailTrace_213244 : CollatzResearch.WordTrace tailWord_213244 prefixEnd_213244 97330372166639036061613 := by
  unfold tailWord_213244
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888823819730441010415393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5185098426307254680553857 3888823819730441010415393)
  ·
    refine ⟨2916617864797830757811545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3888823819730441010415393 2916617864797830757811545)
    ·
      refine ⟨2187463398598373068358659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2916617864797830757811545 2187463398598373068358659)
      ·
        refine ⟨3281195097897559602537989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187463398598373068358659 3281195097897559602537989)
        ·
          refine ⟨615224080855792425475873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3281195097897559602537989 615224080855792425475873)
          ·
            refine ⟨461418060641844319106905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615224080855792425475873 461418060641844319106905)
            ·
              refine ⟨346063545481383239330179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461418060641844319106905 346063545481383239330179)
              ·
                refine ⟨519095318222074858995269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346063545481383239330179 519095318222074858995269)
                ·
                  refine ⟨97330372166639036061613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519095318222074858995269 97330372166639036061613)
                  ·
                    rfl

theorem cell20_213244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_213244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213244 prefixEnd_213244 := by exact prefixLift 213244
  have htrace : WordTrace (prefixWord ++ tailWord_213244) baseStart_213244 baseEnd_213244 := by
    simpa [prefixWord, tailWord_213244, baseEnd_213244] using wordTrace_append hprefix tailTrace_213244
  have hstable : (prefixWord ++ tailWord_213244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213244).length < 2 ^ (prefixWord ++ tailWord_213244).sum := by decide
  have hdescent : baseEnd_213244 < baseStart_213244 := by decide
  rcases family_descends (prefixWord ++ tailWord_213244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213258 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_213258 : Nat := 118140960795 + 213258 * 2 ^ 59
def prefixEnd_213258 : Nat := 4983230072969 + 3 ^ 40 * 213258 * 2
def baseEnd_213258 : Nat := 97336762148117209594889

theorem tailTrace_213258 : CollatzResearch.WordTrace tailWord_213258 prefixEnd_213258 97336762148117209594889 := by
  unfold tailWord_213258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944539565352540602960107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5185438840940108274560285 1944539565352540602960107)
  ·
    refine ⟨2916809348028810904440161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1944539565352540602960107 2916809348028810904440161)
    ·
      refine ⟨2187607011021608178330121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2916809348028810904440161 2187607011021608178330121)
      ·
        refine ⟨1640705258266206133747591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2187607011021608178330121 1640705258266206133747591)
        ·
          refine ⟨2461057887399309200621387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640705258266206133747591 2461057887399309200621387)
          ·
            refine ⟨3691586831098963800932081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461057887399309200621387 3691586831098963800932081)
            ·
              refine ⟨2768690123324222850699061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691586831098963800932081 2768690123324222850699061)
              ·
                refine ⟨259564699061645892253037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2768690123324222850699061 259564699061645892253037)
                ·
                  refine ⟨97336762148117209594889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259564699061645892253037 97336762148117209594889)
                  ·
                    rfl

theorem cell20_213258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_213258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213258 prefixEnd_213258 := by exact prefixLift 213258
  have htrace : WordTrace (prefixWord ++ tailWord_213258) baseStart_213258 baseEnd_213258 := by
    simpa [prefixWord, tailWord_213258, baseEnd_213258] using wordTrace_append hprefix tailTrace_213258
  have hstable : (prefixWord ++ tailWord_213258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213258).length < 2 ^ (prefixWord ++ tailWord_213258).sum := by decide
  have hdescent : baseEnd_213258 < baseStart_213258 := by decide
  rcases family_descends (prefixWord ++ tailWord_213258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213265 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_213265 : Nat := 118140960795 + 213265 * 2 ^ 59
def prefixEnd_213265 : Nat := 4983230072969 + 3 ^ 40 * 213265 * 2
def baseEnd_213265 : Nat := 97339957138856296361527

theorem tailTrace_213265 : CollatzResearch.WordTrace tailWord_213265 prefixEnd_213265 97339957138856296361527 := by
  unfold tailWord_213265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778413572384802607345249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5185609048256535071563499 7778413572384802607345249)
  ·
    refine ⟨5833810179288601955508937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7778413572384802607345249 5833810179288601955508937)
    ·
      refine ⟨4375357634466451466631703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5833810179288601955508937 4375357634466451466631703)
      ·
        refine ⟨6563036451699677199947555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4375357634466451466631703 6563036451699677199947555)
        ·
          refine ⟨9844554677549515799921333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563036451699677199947555 9844554677549515799921333)
          ·
            refine ⟨922927001020267106242625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9844554677549515799921333 922927001020267106242625)
            ·
              refine ⟨692195250765200329681969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922927001020267106242625 692195250765200329681969)
              ·
                refine ⟨519146438073900247261477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692195250765200329681969 519146438073900247261477)
                ·
                  refine ⟨97339957138856296361527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519146438073900247261477 97339957138856296361527)
                  ·
                    rfl

theorem cell20_213265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_213265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213265 prefixEnd_213265 := by exact prefixLift 213265
  have htrace : WordTrace (prefixWord ++ tailWord_213265) baseStart_213265 baseEnd_213265 := by
    simpa [prefixWord, tailWord_213265, baseEnd_213265] using wordTrace_append hprefix tailTrace_213265
  have hstable : (prefixWord ++ tailWord_213265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213265).length < 2 ^ (prefixWord ++ tailWord_213265).sum := by decide
  have hdescent : baseEnd_213265 < baseStart_213265 := by decide
  rcases family_descends (prefixWord ++ tailWord_213265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213272 : List Nat := [2, 1, 2, 3, 1, 2, 3, 6]
def baseStart_213272 : Nat := 118140960795 + 213272 * 2 ^ 59
def prefixEnd_213272 : Nat := 4983230072969 + 3 ^ 40 * 213272 * 2
def baseEnd_213272 : Nat := 32447717376531794376055

theorem tailTrace_213272 : CollatzResearch.WordTrace tailWord_213272 prefixEnd_213272 32447717376531794376055 := by
  unfold tailWord_213272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889334441679721401425035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5185779255572961868566713 3889334441679721401425035)
  ·
    refine ⟨5834001662519582102137553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3889334441679721401425035 5834001662519582102137553)
    ·
      refine ⟨4375501246889686576603165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5834001662519582102137553 4375501246889686576603165)
      ·
        refine ⟨1640812967583632466226187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4375501246889686576603165 1640812967583632466226187)
        ·
          refine ⟨2461219451375448699339281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640812967583632466226187 2461219451375448699339281)
          ·
            refine ⟨1845914588531586524504461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2461219451375448699339281 1845914588531586524504461)
            ·
              refine ⟨692217970699344946689173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845914588531586524504461 692217970699344946689173)
              ·
                refine ⟨32447717376531794376055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 692217970699344946689173 32447717376531794376055)
                ·
                  rfl

theorem cell20_213272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_213272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213272 prefixEnd_213272 := by exact prefixLift 213272
  have htrace : WordTrace (prefixWord ++ tailWord_213272) baseStart_213272 baseEnd_213272 := by
    simpa [prefixWord, tailWord_213272, baseEnd_213272] using wordTrace_append hprefix tailTrace_213272
  have hstable : (prefixWord ++ tailWord_213272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213272).length < 2 ^ (prefixWord ++ tailWord_213272).sum := by decide
  have hdescent : baseEnd_213272 < baseStart_213272 := by decide
  rcases family_descends (prefixWord ++ tailWord_213272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213299 : List Nat := [1, 1, 1, 2, 5, 1, 5, 2, 2]
def baseStart_213299 : Nat := 118140960795 + 213299 * 2 ^ 59
def prefixEnd_213299 : Nat := 4983230072969 + 3 ^ 40 * 213299 * 2
def baseEnd_213299 : Nat := 97355475665303289228055

theorem tailTrace_213299 : CollatzResearch.WordTrace tailWord_213299 prefixEnd_213299 97355475665303289228055 := by
  unfold tailWord_213299
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779653654261626414082951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5186435769507750942721967 7779653654261626414082951)
  ·
    refine ⟨11669480481392439621124427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7779653654261626414082951 11669480481392439621124427)
    ·
      refine ⟨17504220722088659431686641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11669480481392439621124427 17504220722088659431686641)
      ·
        refine ⟨13128165541566494573764981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17504220722088659431686641 13128165541566494573764981)
        ·
          refine ⟨1230765519521858866290467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13128165541566494573764981 1230765519521858866290467)
          ·
            refine ⟨1846148279282788299435701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230765519521858866290467 1846148279282788299435701)
            ·
              refine ⟨173076401182761403072097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1846148279282788299435701 173076401182761403072097)
              ·
                refine ⟨129807300887071052304073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173076401182761403072097 129807300887071052304073)
                ·
                  refine ⟨97355475665303289228055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129807300887071052304073 97355475665303289228055)
                  ·
                    rfl

theorem cell20_213299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 2].length) (baseStart_213299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213299 prefixEnd_213299 := by exact prefixLift 213299
  have htrace : WordTrace (prefixWord ++ tailWord_213299) baseStart_213299 baseEnd_213299 := by
    simpa [prefixWord, tailWord_213299, baseEnd_213299] using wordTrace_append hprefix tailTrace_213299
  have hstable : (prefixWord ++ tailWord_213299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213299).length < 2 ^ (prefixWord ++ tailWord_213299).sum := by decide
  have hdescent : baseEnd_213299 < baseStart_213299 := by decide
  rcases family_descends (prefixWord ++ tailWord_213299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213351 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 3]
def baseStart_213351 : Nat := 118140960795 + 213351 * 2 ^ 59
def prefixEnd_213351 : Nat := 4983230072969 + 3 ^ 40 * 213351 * 2
def baseEnd_213351 : Nat := 97379209882222219494509

theorem tailTrace_213351 : CollatzResearch.WordTrace tailWord_213351 prefixEnd_213351 97379209882222219494509 := by
  unfold tailWord_213351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781550250073239294975907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5187700166715492863317271 7781550250073239294975907)
  ·
    refine ⟨11672325375109858942463861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7781550250073239294975907 11672325375109858942463861)
    ·
      refine ⟨1094280503916549275855987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11672325375109858942463861 1094280503916549275855987)
      ·
        refine ⟨1641420755874823913783981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094280503916549275855987 1641420755874823913783981)
        ·
          refine ⟨615532783453058967668993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1641420755874823913783981 615532783453058967668993)
          ·
            refine ⟨461649587589794225751745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615532783453058967668993 461649587589794225751745)
            ·
              refine ⟨346237190692345669313809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461649587589794225751745 346237190692345669313809)
              ·
                refine ⟨259677893019259251985357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346237190692345669313809 259677893019259251985357)
                ·
                  refine ⟨97379209882222219494509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259677893019259251985357 97379209882222219494509)
                  ·
                    rfl

theorem cell20_213351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_213351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213351 prefixEnd_213351 := by exact prefixLift 213351
  have htrace : WordTrace (prefixWord ++ tailWord_213351) baseStart_213351 baseEnd_213351 := by
    simpa [prefixWord, tailWord_213351, baseEnd_213351] using wordTrace_append hprefix tailTrace_213351
  have hstable : (prefixWord ++ tailWord_213351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213351).length < 2 ^ (prefixWord ++ tailWord_213351).sum := by decide
  have hdescent : baseEnd_213351 < baseStart_213351 := by decide
  rcases family_descends (prefixWord ++ tailWord_213351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213354 : List Nat := [3, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_213354 : Nat := 118140960795 + 213354 * 2 ^ 59
def prefixEnd_213354 : Nat := 4983230072969 + 3 ^ 40 * 213354 * 2
def baseEnd_213354 : Nat := 97380579163967542394497

theorem tailTrace_213354 : CollatzResearch.WordTrace tailWord_213354 prefixEnd_213354 97380579163967542394497 := by
  unfold tailWord_213354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945414917265592701833779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5187773112708247204890077 1945414917265592701833779)
  ·
    refine ⟨2918122375898389052750669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1945414917265592701833779 2918122375898389052750669)
    ·
      refine ⟨1094295890961895894781501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2918122375898389052750669 1094295890961895894781501)
      ·
        refine ⟨410360959110710960543063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1094295890961895894781501 410360959110710960543063)
        ·
          refine ⟨615541438666066440814595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410360959110710960543063 615541438666066440814595)
          ·
            refine ⟨923312157999099661221893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615541438666066440814595 923312157999099661221893)
            ·
              refine ⟨173121029624831186479105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 923312157999099661221893 173121029624831186479105)
              ·
                refine ⟨129840772218623389859329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173121029624831186479105 129840772218623389859329)
                ·
                  refine ⟨97380579163967542394497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129840772218623389859329 97380579163967542394497)
                  ·
                    rfl

theorem cell20_213354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_213354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213354 prefixEnd_213354 := by exact prefixLift 213354
  have htrace : WordTrace (prefixWord ++ tailWord_213354) baseStart_213354 baseEnd_213354 := by
    simpa [prefixWord, tailWord_213354, baseEnd_213354] using wordTrace_append hprefix tailTrace_213354
  have hstable : (prefixWord ++ tailWord_213354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213354).length < 2 ^ (prefixWord ++ tailWord_213354).sum := by decide
  have hdescent : baseEnd_213354 < baseStart_213354 := by decide
  rcases family_descends (prefixWord ++ tailWord_213354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213365 : List Nat := [1, 3, 4, 1, 2, 1, 3, 5]
def baseStart_213365 : Nat := 118140960795 + 213365 * 2 ^ 59
def prefixEnd_213365 : Nat := 4983230072969 + 3 ^ 40 * 213365 * 2
def baseEnd_213365 : Nat := 32461866621233464342595

theorem tailTrace_213365 : CollatzResearch.WordTrace tailWord_213365 prefixEnd_213365 32461866621233464342595 := by
  unfold tailWord_213365
  simp only [CollatzResearch.WordTrace]
  refine ⟨7782060872022519685985549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5188040581348346457323699 7782060872022519685985549)
  ·
    refine ⟨2918272827008444882244581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7782060872022519685985549 2918272827008444882244581)
    ·
      refine ⟨547176155064083415420859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2918272827008444882244581 547176155064083415420859)
      ·
        refine ⟨820764232596125123131289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547176155064083415420859 820764232596125123131289)
        ·
          refine ⟨615573174447093842348467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820764232596125123131289 615573174447093842348467)
          ·
            refine ⟨923359761670640763522701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615573174447093842348467 923359761670640763522701)
            ·
              refine ⟨346259910626490286321013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 923359761670640763522701 346259910626490286321013)
              ·
                refine ⟨32461866621233464342595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346259910626490286321013 32461866621233464342595)
                ·
                  rfl

theorem cell20_213365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_213365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213365 prefixEnd_213365 := by exact prefixLift 213365
  have htrace : WordTrace (prefixWord ++ tailWord_213365) baseStart_213365 baseEnd_213365 := by
    simpa [prefixWord, tailWord_213365, baseEnd_213365] using wordTrace_append hprefix tailTrace_213365
  have hstable : (prefixWord ++ tailWord_213365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213365).length < 2 ^ (prefixWord ++ tailWord_213365).sum := by decide
  have hdescent : baseEnd_213365 < baseStart_213365 := by decide
  rcases family_descends (prefixWord ++ tailWord_213365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213406 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_213406 : Nat := 118140960795 + 213406 * 2 ^ 59
def prefixEnd_213406 : Nat := 4983230072969 + 3 ^ 40 * 213406 * 2
def baseEnd_213406 : Nat := 97404313380886472660951

theorem tailTrace_213406 : CollatzResearch.WordTrace tailWord_213406 prefixEnd_213406 97404313380886472660951 := by
  unfold tailWord_213406
  simp only [CollatzResearch.WordTrace]
  refine ⟨972944533109247961028509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5189037509915989125485381 972944533109247961028509)
  ·
    refine ⟨364854199915967985385691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 972944533109247961028509 364854199915967985385691)
    ·
      refine ⟨547281299873951978078537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364854199915967985385691 547281299873951978078537)
      ·
        refine ⟨410460974905463983558903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547281299873951978078537 410460974905463983558903)
        ·
          refine ⟨615691462358195975338355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410460974905463983558903 615691462358195975338355)
          ·
            refine ⟨923537193537293963007533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615691462358195975338355 923537193537293963007533)
            ·
              refine ⟨346326447576485236127825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 923537193537293963007533 346326447576485236127825)
              ·
                refine ⟨259744835682363927095869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346326447576485236127825 259744835682363927095869)
                ·
                  refine ⟨97404313380886472660951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259744835682363927095869 97404313380886472660951)
                  ·
                    rfl

theorem cell20_213406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_213406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213406 prefixEnd_213406 := by exact prefixLift 213406
  have htrace : WordTrace (prefixWord ++ tailWord_213406) baseStart_213406 baseEnd_213406 := by
    simpa [prefixWord, tailWord_213406, baseEnd_213406] using wordTrace_append hprefix tailTrace_213406
  have hstable : (prefixWord ++ tailWord_213406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213406).length < 2 ^ (prefixWord ++ tailWord_213406).sum := by decide
  have hdescent : baseEnd_213406 < baseStart_213406 := by decide
  rcases family_descends (prefixWord ++ tailWord_213406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213410 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_213410 : Nat := 118140960795 + 213410 * 2 ^ 59
def prefixEnd_213410 : Nat := 4983230072969 + 3 ^ 40 * 213410 * 2
def baseEnd_213410 : Nat := 97406139089880236527601

theorem tailTrace_213410 : CollatzResearch.WordTrace tailWord_213410 prefixEnd_213410 97406139089880236527601 := by
  unfold tailWord_213410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945925539214873092843421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5189134771239661580915789 1945925539214873092843421)
  ·
    refine ⟨729722077205577409816283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1945925539214873092843421 729722077205577409816283)
    ·
      refine ⟨1094583115808366114724425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729722077205577409816283 1094583115808366114724425)
      ·
        refine ⟨820937336856274586043319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1094583115808366114724425 820937336856274586043319)
        ·
          refine ⟨1231406005284411879064979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820937336856274586043319 1231406005284411879064979)
          ·
            refine ⟨1847109007926617818597469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231406005284411879064979 1847109007926617818597469)
            ·
              refine ⟨692665877972481681974051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1847109007926617818597469 692665877972481681974051)
              ·
                refine ⟨1038998816958722522961077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692665877972481681974051 1038998816958722522961077)
                ·
                  refine ⟨97406139089880236527601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038998816958722522961077 97406139089880236527601)
                  ·
                    rfl

theorem cell20_213410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_213410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213410 prefixEnd_213410 := by exact prefixLift 213410
  have htrace : WordTrace (prefixWord ++ tailWord_213410) baseStart_213410 baseEnd_213410 := by
    simpa [prefixWord, tailWord_213410, baseEnd_213410] using wordTrace_append hprefix tailTrace_213410
  have hstable : (prefixWord ++ tailWord_213410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213410).length < 2 ^ (prefixWord ++ tailWord_213410).sum := by decide
  have hdescent : baseEnd_213410 < baseStart_213410 := by decide
  rcases family_descends (prefixWord ++ tailWord_213410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213458 : List Nat := [3, 2, 2, 4, 1, 2, 6]
def baseStart_213458 : Nat := 118140960795 + 213458 * 2 ^ 59
def prefixEnd_213458 : Nat := 4983230072969 + 3 ^ 40 * 213458 * 2
def baseEnd_213458 : Nat := 10825338621978378103045

theorem tailTrace_213458 : CollatzResearch.WordTrace tailWord_213458 prefixEnd_213458 10825338621978378103045 := by
  unfold tailWord_213458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946363215171399142280257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5190301907123731046080685 1946363215171399142280257)
  ·
    refine ⟨1459772411378549356710193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1946363215171399142280257 1459772411378549356710193)
    ·
      refine ⟨1094829308533912017532645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1459772411378549356710193 1094829308533912017532645)
      ·
        refine ⟨205280495350108503287371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1094829308533912017532645 205280495350108503287371)
        ·
          refine ⟨307920743025162754931057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205280495350108503287371 307920743025162754931057)
          ·
            refine ⟨230940557268872066198293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307920743025162754931057 230940557268872066198293)
            ·
              refine ⟨10825338621978378103045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 230940557268872066198293 10825338621978378103045)
              ·
                rfl

theorem cell20_213458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 6].length) (baseStart_213458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213458 prefixEnd_213458 := by exact prefixLift 213458
  have htrace : WordTrace (prefixWord ++ tailWord_213458) baseStart_213458 baseEnd_213458 := by
    simpa [prefixWord, tailWord_213458, baseEnd_213458] using wordTrace_append hprefix tailTrace_213458
  have hstable : (prefixWord ++ tailWord_213458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213458).length < 2 ^ (prefixWord ++ tailWord_213458).sum := by decide
  have hdescent : baseEnd_213458 < baseStart_213458 := by decide
  rcases family_descends (prefixWord ++ tailWord_213458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213482 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_213482 : Nat := 118140960795 + 213482 * 2 ^ 59
def prefixEnd_213482 : Nat := 4983230072969 + 3 ^ 40 * 213482 * 2
def baseEnd_213482 : Nat := 97439001851767986127307

theorem tailTrace_213482 : CollatzResearch.WordTrace tailWord_213482 prefixEnd_213482 97439001851767986127307 := by
  unfold tailWord_213482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946582053149662166998675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5190885475065765778663133 1946582053149662166998675)
  ·
    refine ⟨2919873079724493250498013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1946582053149662166998675 2919873079724493250498013)
    ·
      refine ⟨1094952404896684968936755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2919873079724493250498013 1094952404896684968936755)
      ·
        refine ⟨1642428607345027453405133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094952404896684968936755 1642428607345027453405133)
        ·
          refine ⟨615910727754385295026925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1642428607345027453405133 615910727754385295026925)
          ·
            refine ⟨230966522907894485635097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615910727754385295026925 230966522907894485635097)
            ·
              refine ⟨173224892180920864226323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230966522907894485635097 173224892180920864226323)
              ·
                refine ⟨259837338271381296339485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173224892180920864226323 259837338271381296339485)
                ·
                  refine ⟨97439001851767986127307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259837338271381296339485 97439001851767986127307)
                  ·
                    rfl

theorem cell20_213482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_213482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213482 prefixEnd_213482 := by exact prefixLift 213482
  have htrace : WordTrace (prefixWord ++ tailWord_213482) baseStart_213482 baseEnd_213482 := by
    simpa [prefixWord, tailWord_213482, baseEnd_213482] using wordTrace_append hprefix tailTrace_213482
  have hstable : (prefixWord ++ tailWord_213482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213482).length < 2 ^ (prefixWord ++ tailWord_213482).sum := by decide
  have hdescent : baseEnd_213482 < baseStart_213482 := by decide
  rcases family_descends (prefixWord ++ tailWord_213482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213552 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_213552 : Nat := 118140960795 + 213552 * 2 ^ 59
def prefixEnd_213552 : Nat := 4983230072969 + 3 ^ 40 * 213552 * 2
def baseEnd_213552 : Nat := 97470951759158853793687

theorem tailTrace_213552 : CollatzResearch.WordTrace tailWord_213552 prefixEnd_213552 97470951759158853793687 := by
  unfold tailWord_213552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894440661172525311521455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5192587548230033748695273 3894440661172525311521455)
  ·
    refine ⟨5841660991758787967282183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894440661172525311521455 5841660991758787967282183)
    ·
      refine ⟨8762491487638181950923275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841660991758787967282183 8762491487638181950923275)
      ·
        refine ⟨13143737231457272926384913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8762491487638181950923275 13143737231457272926384913)
        ·
          refine ⟨9857802923592954694788685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13143737231457272926384913 9857802923592954694788685)
          ·
            refine ⟨3696676096347358010545757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9857802923592954694788685 3696676096347358010545757)
            ·
              refine ⟨1386253536130259253954659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3696676096347358010545757 1386253536130259253954659)
              ·
                refine ⟨2079380304195388880931989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386253536130259253954659 2079380304195388880931989)
                ·
                  refine ⟨97470951759158853793687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2079380304195388880931989 97470951759158853793687)
                  ·
                    rfl

theorem cell20_213552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_213552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213552 prefixEnd_213552 := by exact prefixLift 213552
  have htrace : WordTrace (prefixWord ++ tailWord_213552) baseStart_213552 baseEnd_213552 := by
    simpa [prefixWord, tailWord_213552, baseEnd_213552] using wordTrace_append hprefix tailTrace_213552
  have hstable : (prefixWord ++ tailWord_213552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213552).length < 2 ^ (prefixWord ++ tailWord_213552).sum := by decide
  have hdescent : baseEnd_213552 < baseStart_213552 := by decide
  rcases family_descends (prefixWord ++ tailWord_213552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213565 : List Nat := [1, 4, 1, 3, 2, 2, 2, 3, 2]
def baseStart_213565 : Nat := 118140960795 + 213565 * 2 ^ 59
def prefixEnd_213565 : Nat := 4983230072969 + 3 ^ 40 * 213565 * 2
def baseEnd_213565 : Nat := 97476885313388586360301

theorem tailTrace_213565 : CollatzResearch.WordTrace tailWord_213565 prefixEnd_213565 97476885313388586360301 := by
  unfold tailWord_213565
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789355471297953843266149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5192903647531969228844099 7789355471297953843266149)
  ·
    refine ⟨1460504150868366345612403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7789355471297953843266149 1460504150868366345612403)
    ·
      refine ⟨2190756226302549518418605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460504150868366345612403 2190756226302549518418605)
      ·
        refine ⟨821533584863456069406977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2190756226302549518418605 821533584863456069406977)
        ·
          refine ⟨616150188647592052055233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821533584863456069406977 616150188647592052055233)
          ·
            refine ⟨462112641485694039041425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616150188647592052055233 462112641485694039041425)
            ·
              refine ⟨346584481114270529281069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462112641485694039041425 346584481114270529281069)
              ·
                refine ⟨129969180417851448480401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346584481114270529281069 129969180417851448480401)
                ·
                  refine ⟨97476885313388586360301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129969180417851448480401 97476885313388586360301)
                  ·
                    rfl

theorem cell20_213565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_213565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213565 prefixEnd_213565 := by exact prefixLift 213565
  have htrace : WordTrace (prefixWord ++ tailWord_213565) baseStart_213565 baseEnd_213565 := by
    simpa [prefixWord, tailWord_213565, baseEnd_213565] using wordTrace_append hprefix tailTrace_213565
  have hstable : (prefixWord ++ tailWord_213565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213565).length < 2 ^ (prefixWord ++ tailWord_213565).sum := by decide
  have hdescent : baseEnd_213565 < baseStart_213565 := by decide
  rcases family_descends (prefixWord ++ tailWord_213565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213586 : List Nat := [3, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_213586 : Nat := 118140960795 + 213586 * 2 ^ 59
def prefixEnd_213586 : Nat := 4983230072969 + 3 ^ 40 * 213586 * 2
def baseEnd_213586 : Nat := 97486470285605846660215

theorem tailTrace_213586 : CollatzResearch.WordTrace tailWord_213586 prefixEnd_213586 97486470285605846660215 := by
  unfold tailWord_213586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947530351055468607445153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5193414269481249619853741 1947530351055468607445153)
  ·
    refine ⟨1460647763291601455583865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1947530351055468607445153 1460647763291601455583865)
    ·
      refine ⟨1095485822468701091687899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1460647763291601455583865 1095485822468701091687899)
      ·
        refine ⟨1643228733703051637531849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095485822468701091687899 1643228733703051637531849)
        ·
          refine ⟨1232421550277288728148887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1643228733703051637531849 1232421550277288728148887)
          ·
            refine ⟨1848632325415933092223331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232421550277288728148887 1848632325415933092223331)
            ·
              refine ⟨2772948488123899638334997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848632325415933092223331 2772948488123899638334997)
              ·
                refine ⟨129981960380807795546953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2772948488123899638334997 129981960380807795546953)
                ·
                  refine ⟨97486470285605846660215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129981960380807795546953 97486470285605846660215)
                  ·
                    rfl

theorem cell20_213586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_213586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213586 prefixEnd_213586 := by exact prefixLift 213586
  have htrace : WordTrace (prefixWord ++ tailWord_213586) baseStart_213586 baseEnd_213586 := by
    simpa [prefixWord, tailWord_213586, baseEnd_213586] using wordTrace_append hprefix tailTrace_213586
  have hstable : (prefixWord ++ tailWord_213586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213586).length < 2 ^ (prefixWord ++ tailWord_213586).sum := by decide
  have hdescent : baseEnd_213586 < baseStart_213586 := by decide
  rcases family_descends (prefixWord ++ tailWord_213586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213596 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_213596 : Nat := 118140960795 + 213596 * 2 ^ 59
def prefixEnd_213596 : Nat := 4983230072969 + 3 ^ 40 * 213596 * 2
def baseEnd_213596 : Nat := 97491034558090256326841

theorem tailTrace_213596 : CollatzResearch.WordTrace tailWord_213596 prefixEnd_213596 97491034558090256326841 := by
  unfold tailWord_213596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895243067092823068822321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5193657422790430758429761 3895243067092823068822321)
  ·
    refine ⟨2921432300319617301616741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3895243067092823068822321 2921432300319617301616741)
    ·
      refine ⟨547768556309928244053139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2921432300319617301616741 547768556309928244053139)
      ·
        refine ⟨821652834464892366079709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547768556309928244053139 821652834464892366079709)
        ·
          refine ⟨308119812924334637279891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 821652834464892366079709 308119812924334637279891)
          ·
            refine ⟨462179719386501955919837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308119812924334637279891 462179719386501955919837)
            ·
              refine ⟨173317394769938233469939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462179719386501955919837 173317394769938233469939)
              ·
                refine ⟨259976092154907350204909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173317394769938233469939 259976092154907350204909)
                ·
                  refine ⟨97491034558090256326841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259976092154907350204909 97491034558090256326841)
                  ·
                    rfl

theorem cell20_213596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_213596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213596 prefixEnd_213596 := by exact prefixLift 213596
  have htrace : WordTrace (prefixWord ++ tailWord_213596) baseStart_213596 baseEnd_213596 := by
    simpa [prefixWord, tailWord_213596, baseEnd_213596] using wordTrace_append hprefix tailTrace_213596
  have hstable : (prefixWord ++ tailWord_213596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213596).length < 2 ^ (prefixWord ++ tailWord_213596).sum := by decide
  have hdescent : baseEnd_213596 < baseStart_213596 := by decide
  rcases family_descends (prefixWord ++ tailWord_213596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213628 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_213628 : Nat := 118140960795 + 213628 * 2 ^ 59
def prefixEnd_213628 : Nat := 4983230072969 + 3 ^ 40 * 213628 * 2
def baseEnd_213628 : Nat := 97505640230040367260043

theorem tailTrace_213628 : CollatzResearch.WordTrace tailWord_213628 prefixEnd_213628 97505640230040367260043 := by
  unfold tailWord_213628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895826635034857801404769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5194435513379810401873025 3895826635034857801404769)
  ·
    refine ⟨2921869976276143351053577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3895826635034857801404769 2921869976276143351053577)
    ·
      refine ⟨2191402482207107513290183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2921869976276143351053577 2191402482207107513290183)
      ·
        refine ⟨3287103723310661269935275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191402482207107513290183 3287103723310661269935275)
        ·
          refine ⟨4930655584965991904902913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287103723310661269935275 4930655584965991904902913)
          ·
            refine ⟨3697991688724493928677185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4930655584965991904902913 3697991688724493928677185)
            ·
              refine ⟨2773493766543370446507889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697991688724493928677185 2773493766543370446507889)
              ·
                refine ⟨2080120324907527834880917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773493766543370446507889 2080120324907527834880917)
                ·
                  refine ⟨97505640230040367260043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2080120324907527834880917 97505640230040367260043)
                  ·
                    rfl

theorem cell20_213628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_213628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213628 prefixEnd_213628 := by exact prefixLift 213628
  have htrace : WordTrace (prefixWord ++ tailWord_213628) baseStart_213628 baseEnd_213628 := by
    simpa [prefixWord, tailWord_213628, baseEnd_213628] using wordTrace_append hprefix tailTrace_213628
  have hstable : (prefixWord ++ tailWord_213628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213628).length < 2 ^ (prefixWord ++ tailWord_213628).sum := by decide
  have hdescent : baseEnd_213628 < baseStart_213628 := by decide
  rcases family_descends (prefixWord ++ tailWord_213628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213635 : List Nat := [1, 1, 1, 3, 3, 1, 10]
def baseStart_213635 : Nat := 118140960795 + 213635 * 2 ^ 59
def prefixEnd_213635 : Nat := 4983230072969 + 3 ^ 40 * 213635 * 2
def baseEnd_213635 : Nat := 10834315024531050447409

theorem tailTrace_213635 : CollatzResearch.WordTrace tailWord_213635 prefixEnd_213635 10834315024531050447409 := by
  unfold tailWord_213635
  simp only [CollatzResearch.WordTrace]
  refine ⟨7791908581044355798314359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5194605720696237198876239 7791908581044355798314359)
  ·
    refine ⟨11687862871566533697471539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7791908581044355798314359 11687862871566533697471539)
    ·
      refine ⟨17531794307349800546207309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11687862871566533697471539 17531794307349800546207309)
      ·
        refine ⟨6574422865256175204827741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17531794307349800546207309 6574422865256175204827741)
        ·
          refine ⟨2465408574471065701810403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6574422865256175204827741 2465408574471065701810403)
          ·
            refine ⟨3698112861706598552715605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465408574471065701810403 3698112861706598552715605)
            ·
              refine ⟨10834315024531050447409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3698112861706598552715605 10834315024531050447409)
              ·
                rfl

theorem cell20_213635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_213635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213635 prefixEnd_213635 := by exact prefixLift 213635
  have htrace : WordTrace (prefixWord ++ tailWord_213635) baseStart_213635 baseEnd_213635 := by
    simpa [prefixWord, tailWord_213635, baseEnd_213635] using wordTrace_append hprefix tailTrace_213635
  have hstable : (prefixWord ++ tailWord_213635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213635).length < 2 ^ (prefixWord ++ tailWord_213635).sum := by decide
  have hdescent : baseEnd_213635 < baseStart_213635 := by decide
  rcases family_descends (prefixWord ++ tailWord_213635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213686 : List Nat := [5, 1, 3, 1, 3, 7]
def baseStart_213686 : Nat := 118140960795 + 213686 * 2 ^ 59
def prefixEnd_213686 : Nat := 4983230072969 + 3 ^ 40 * 213686 * 2
def baseEnd_213686 : Nat := 3612300481868516419499

theorem tailTrace_213686 : CollatzResearch.WordTrace tailWord_213686 prefixEnd_213686 3612300481868516419499 := by
  unfold tailWord_213686
  simp only [CollatzResearch.WordTrace]
  refine ⟨487110543991224469276307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5195845802573061005613941 487110543991224469276307)
  ·
    refine ⟨730665815986836703914461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 487110543991224469276307 730665815986836703914461)
    ·
      refine ⟨273999680995063763967923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 730665815986836703914461 273999680995063763967923)
      ·
        refine ⟨410999521492595645951885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273999680995063763967923 410999521492595645951885)
        ·
          refine ⟨154124820559723367231957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410999521492595645951885 154124820559723367231957)
          ·
            refine ⟨3612300481868516419499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 154124820559723367231957 3612300481868516419499)
            ·
              rfl

theorem cell20_213686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 7].length) (baseStart_213686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213686 prefixEnd_213686 := by exact prefixLift 213686
  have htrace : WordTrace (prefixWord ++ tailWord_213686) baseStart_213686 baseEnd_213686 := by
    simpa [prefixWord, tailWord_213686, baseEnd_213686] using wordTrace_append hprefix tailTrace_213686
  have hstable : (prefixWord ++ tailWord_213686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213686).length < 2 ^ (prefixWord ++ tailWord_213686).sum := by decide
  have hdescent : baseEnd_213686 < baseStart_213686 := by decide
  rcases family_descends (prefixWord ++ tailWord_213686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213724 : List Nat := [2, 2, 5, 1, 1, 2, 3, 4]
def baseStart_213724 : Nat := 118140960795 + 213724 * 2 ^ 59
def prefixEnd_213724 : Nat := 4983230072969 + 3 ^ 40 * 213724 * 2
def baseEnd_213724 : Nat := 32516485748630233353217

theorem tailTrace_213724 : CollatzResearch.WordTrace tailWord_213724 prefixEnd_213724 32516485748630233353217 := by
  unfold tailWord_213724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3897577338860961999152113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5196769785147949332202817 3897577338860961999152113)
  ·
    refine ⟨2923183004145721499364085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3897577338860961999152113 2923183004145721499364085)
    ·
      refine ⟨274048406638661390565383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2923183004145721499364085 274048406638661390565383)
      ·
        refine ⟨411072609957992085848075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274048406638661390565383 411072609957992085848075)
        ·
          refine ⟨616608914936988128772113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411072609957992085848075 616608914936988128772113)
          ·
            refine ⟨462456686202741096579085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616608914936988128772113 462456686202741096579085)
            ·
              refine ⟨173421257326027911217157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462456686202741096579085 173421257326027911217157)
              ·
                refine ⟨32516485748630233353217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173421257326027911217157 32516485748630233353217)
                ·
                  rfl

theorem cell20_213724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_213724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213724 prefixEnd_213724 := by exact prefixLift 213724
  have htrace : WordTrace (prefixWord ++ tailWord_213724) baseStart_213724 baseEnd_213724 := by
    simpa [prefixWord, tailWord_213724, baseEnd_213724] using wordTrace_append hprefix tailTrace_213724
  have hstable : (prefixWord ++ tailWord_213724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213724).length < 2 ^ (prefixWord ++ tailWord_213724).sum := by decide
  have hdescent : baseEnd_213724 < baseStart_213724 := by decide
  rcases family_descends (prefixWord ++ tailWord_213724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
