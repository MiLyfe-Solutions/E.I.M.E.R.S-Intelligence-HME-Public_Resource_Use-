import V185TrunkScan22Chunk119

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1073716 : List Nat := [2, 5, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1073716 : Nat := 118140960795 + 1073716 * 2 ^ 59
def prefixEnd_1073716 : Nat := 4983230072969 + 3 ^ 40 * 1073716 * 2
def baseEnd_1073716 : Nat := 122518309871783625536017

theorem tailTrace_1073716 : CollatzResearch.WordTrace tailWord_1073716 prefixEnd_1073716 122518309871783625536017 := by
  unfold tailWord_1073716
  simp only [CollatzResearch.WordTrace]
  refine ⟨19580819889058891469296501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26107759852078521959062001 19580819889058891469296501)
  ·
    refine ⟨1835701864599271075246547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19580819889058891469296501 1835701864599271075246547)
    ·
      refine ⟨2753552796898906612869821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835701864599271075246547 2753552796898906612869821)
      ·
        refine ⟨1032582298837089979826183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2753552796898906612869821 1032582298837089979826183)
        ·
          refine ⟨1548873448255634969739275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032582298837089979826183 1548873448255634969739275)
          ·
            refine ⟨2323310172383452454608913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548873448255634969739275 2323310172383452454608913)
            ·
              refine ⟨1742482629287589340956685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323310172383452454608913 1742482629287589340956685)
              ·
                refine ⟨653430985982846002858757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742482629287589340956685 653430985982846002858757)
                ·
                  refine ⟨122518309871783625536017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653430985982846002858757 122518309871783625536017)
                  ·
                    rfl

theorem cell22_1073716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1073716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073716 prefixEnd_1073716 := by exact prefixLift 1073716
  have htrace : WordTrace (prefixWord ++ tailWord_1073716) baseStart_1073716 baseEnd_1073716 := by
    simpa [prefixWord, tailWord_1073716, baseEnd_1073716] using wordTrace_append hprefix tailTrace_1073716
  have hstable : (prefixWord ++ tailWord_1073716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073716).length < 2 ^ (prefixWord ++ tailWord_1073716).sum := by decide
  have hdescent : baseEnd_1073716 < baseStart_1073716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073776 : List Nat := [2, 1, 1, 1, 7, 2, 1, 3, 1, 3]
def baseStart_1073776 : Nat := 118140960795 + 1073776 * 2 ^ 59
def prefixEnd_1073776 : Nat := 4983230072969 + 3 ^ 40 * 1073776 * 2
def baseEnd_1073776 : Nat := 367575468841530720107867

theorem tailTrace_1073776 : CollatzResearch.WordTrace tailWord_1073776 prefixEnd_1073776 367575468841530720107867 := by
  unfold tailWord_1073776
  simp only [CollatzResearch.WordTrace]
  refine ⟨19581914078950206592888591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26109218771933608790518121 19581914078950206592888591)
  ·
    refine ⟨29372871118425309889332887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19581914078950206592888591 29372871118425309889332887)
    ·
      refine ⟨44059306677637964833999331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29372871118425309889332887 44059306677637964833999331)
      ·
        refine ⟨66088960016456947250998997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44059306677637964833999331 66088960016456947250998997)
        ·
          refine ⟨1548960000385709701195289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66088960016456947250998997 1548960000385709701195289)
          ·
            refine ⟨1161720000289282275896467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1548960000385709701195289 1161720000289282275896467)
            ·
              refine ⟨1742580000433923413844701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161720000289282275896467 1742580000433923413844701)
              ·
                refine ⟨653467500162721280191763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742580000433923413844701 653467500162721280191763)
                ·
                  refine ⟨980201250244081920287645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653467500162721280191763 980201250244081920287645)
                  ·
                    refine ⟨367575468841530720107867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980201250244081920287645 367575468841530720107867)
                    ·
                      rfl

theorem cell22_1073776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 3].length) (baseStart_1073776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073776 prefixEnd_1073776 := by exact prefixLift 1073776
  have htrace : WordTrace (prefixWord ++ tailWord_1073776) baseStart_1073776 baseEnd_1073776 := by
    simpa [prefixWord, tailWord_1073776, baseEnd_1073776] using wordTrace_append hprefix tailTrace_1073776
  have hstable : (prefixWord ++ tailWord_1073776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073776).length < 2 ^ (prefixWord ++ tailWord_1073776).sum := by decide
  have hdescent : baseEnd_1073776 < baseStart_1073776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073783 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 8]
def baseStart_1073783 : Nat := 118140960795 + 1073783 * 2 ^ 59
def prefixEnd_1073783 : Nat := 4983230072969 + 3 ^ 40 * 1073783 * 2
def baseEnd_1073783 : Nat := 122525955028195011727615

theorem tailTrace_1073783 : CollatzResearch.WordTrace tailWord_1073783 prefixEnd_1073783 122525955028195011727615 := by
  unfold tailWord_1073783
  simp only [CollatzResearch.WordTrace]
  refine ⟨39164083468875053381282003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26109388979250035587521335 39164083468875053381282003)
  ·
    refine ⟨58746125203312580071923005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39164083468875053381282003 58746125203312580071923005)
    ·
      refine ⟨22029796951242217526971127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58746125203312580071923005 22029796951242217526971127)
      ·
        refine ⟨33044695426863326290456691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22029796951242217526971127 33044695426863326290456691)
        ·
          refine ⟨49567043140294989435685037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33044695426863326290456691 49567043140294989435685037)
          ·
            refine ⟨18587641177610621038381889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49567043140294989435685037 18587641177610621038381889)
            ·
              refine ⟨13940730883207965778786417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18587641177610621038381889 13940730883207965778786417)
              ·
                refine ⟨10455548162405974334089813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13940730883207965778786417 10455548162405974334089813)
                ·
                  refine ⟨122525955028195011727615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10455548162405974334089813 122525955028195011727615)
                  ·
                    rfl

theorem cell22_1073783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 8].length) (baseStart_1073783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073783 prefixEnd_1073783 := by exact prefixLift 1073783
  have htrace : WordTrace (prefixWord ++ tailWord_1073783) baseStart_1073783 baseEnd_1073783 := by
    simpa [prefixWord, tailWord_1073783, baseEnd_1073783] using wordTrace_append hprefix tailTrace_1073783
  have hstable : (prefixWord ++ tailWord_1073783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073783).length < 2 ^ (prefixWord ++ tailWord_1073783).sum := by decide
  have hdescent : baseEnd_1073783 < baseStart_1073783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073815 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1073815 : Nat := 118140960795 + 1073815 * 2 ^ 59
def prefixEnd_1073815 : Nat := 4983230072969 + 3 ^ 40 * 1073815 * 2
def baseEnd_1073815 : Nat := 367588819338547618382747

theorem tailTrace_1073815 : CollatzResearch.WordTrace tailWord_1073815 prefixEnd_1073815 367588819338547618382747 := by
  unfold tailWord_1073815
  simp only [CollatzResearch.WordTrace]
  refine ⟨39165250604759122846446899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26110167069839415230964599 39165250604759122846446899)
  ·
    refine ⟨58747875907138684269670349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39165250604759122846446899 58747875907138684269670349)
    ·
      refine ⟨22030453465177006601126381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58747875907138684269670349 22030453465177006601126381)
      ·
        refine ⟨8261420049441377475422393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22030453465177006601126381 8261420049441377475422393)
        ·
          refine ⟨6196065037081033106566795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8261420049441377475422393 6196065037081033106566795)
          ·
            refine ⟨9294097555621549659850193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6196065037081033106566795 9294097555621549659850193)
            ·
              refine ⟨6970573166716162244887645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9294097555621549659850193 6970573166716162244887645)
              ·
                refine ⟨2613964937518560841832867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6970573166716162244887645 2613964937518560841832867)
                ·
                  refine ⟨3920947406277841262749301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613964937518560841832867 3920947406277841262749301)
                  ·
                    refine ⟨367588819338547618382747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3920947406277841262749301 367588819338547618382747)
                    ·
                      rfl

theorem cell22_1073815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1073815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073815 prefixEnd_1073815 := by exact prefixLift 1073815
  have htrace : WordTrace (prefixWord ++ tailWord_1073815) baseStart_1073815 baseEnd_1073815 := by
    simpa [prefixWord, tailWord_1073815, baseEnd_1073815] using wordTrace_append hprefix tailTrace_1073815
  have hstable : (prefixWord ++ tailWord_1073815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073815).length < 2 ^ (prefixWord ++ tailWord_1073815).sum := by decide
  have hdescent : baseEnd_1073815 < baseStart_1073815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073845 : List Nat := [1, 3, 3, 3, 1, 11]
def baseStart_1073845 : Nat := 118140960795 + 1073845 * 2 ^ 59
def prefixEnd_1073845 : Nat := 4983230072969 + 3 ^ 40 * 1073845 * 2
def baseEnd_1073845 : Nat := 4538260357427623952255

theorem tailTrace_1073845 : CollatzResearch.WordTrace tailWord_1073845 prefixEnd_1073845 4538260357427623952255 := by
  unfold tailWord_1073845
  simp only [CollatzResearch.WordTrace]
  refine ⟨39166344794650437970038989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26110896529766958646692659 39166344794650437970038989)
  ·
    refine ⟨14687379297993914238764621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39166344794650437970038989 14687379297993914238764621)
    ·
      refine ⟨5507767236747717839536733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14687379297993914238764621 5507767236747717839536733)
      ·
        refine ⟨2065412713780394189826275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5507767236747717839536733 2065412713780394189826275)
        ·
          refine ⟨3098119070670591284739413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065412713780394189826275 3098119070670591284739413)
          ·
            refine ⟨4538260357427623952255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3098119070670591284739413 4538260357427623952255)
            ·
              rfl

theorem cell22_1073845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 11].length) (baseStart_1073845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073845 prefixEnd_1073845 := by exact prefixLift 1073845
  have htrace : WordTrace (prefixWord ++ tailWord_1073845) baseStart_1073845 baseEnd_1073845 := by
    simpa [prefixWord, tailWord_1073845, baseEnd_1073845] using wordTrace_append hprefix tailTrace_1073845
  have hstable : (prefixWord ++ tailWord_1073845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073845).length < 2 ^ (prefixWord ++ tailWord_1073845).sum := by decide
  have hdescent : baseEnd_1073845 < baseStart_1073845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073905 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_1073905 : Nat := 118140960795 + 1073905 * 2 ^ 59
def prefixEnd_1073905 : Nat := 4983230072969 + 3 ^ 40 * 1073905 * 2
def baseEnd_1073905 : Nat := 367619628177817383632471

theorem tailTrace_1073905 : CollatzResearch.WordTrace tailWord_1073905 prefixEnd_1073905 367619628177817383632471 := by
  unfold tailWord_1073905
  simp only [CollatzResearch.WordTrace]
  refine ⟨39168533174433068217223169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26112355449622045478148779 39168533174433068217223169)
  ·
    refine ⟨29376399880824801162917377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39168533174433068217223169 29376399880824801162917377)
    ·
      refine ⟨22032299910618600872188033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29376399880824801162917377 22032299910618600872188033)
      ·
        refine ⟨16524224932963950654141025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22032299910618600872188033 16524224932963950654141025)
        ·
          refine ⟨12393168699722962990605769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16524224932963950654141025 12393168699722962990605769)
          ·
            refine ⟨9294876524792222242954327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12393168699722962990605769 9294876524792222242954327)
            ·
              refine ⟨13942314787188333364431491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9294876524792222242954327 13942314787188333364431491)
              ·
                refine ⟨20913472180782500046647237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13942314787188333364431491 20913472180782500046647237)
                ·
                  refine ⟨3921276033896718758746357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20913472180782500046647237 3921276033896718758746357)
                  ·
                    refine ⟨367619628177817383632471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3921276033896718758746357 367619628177817383632471)
                    ·
                      rfl

theorem cell22_1073905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_1073905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073905 prefixEnd_1073905 := by exact prefixLift 1073905
  have htrace : WordTrace (prefixWord ++ tailWord_1073905) baseStart_1073905 baseEnd_1073905 := by
    simpa [prefixWord, tailWord_1073905, baseEnd_1073905] using wordTrace_append hprefix tailTrace_1073905
  have hstable : (prefixWord ++ tailWord_1073905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073905).length < 2 ^ (prefixWord ++ tailWord_1073905).sum := by decide
  have hdescent : baseEnd_1073905 < baseStart_1073905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073924 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 5]
def baseStart_1073924 : Nat := 118140960795 + 1073924 * 2 ^ 59
def prefixEnd_1073924 : Nat := 4983230072969 + 3 ^ 40 * 1073924 * 2
def baseEnd_1073924 : Nat := 122542044088702555802471

theorem tailTrace_1073924 : CollatzResearch.WordTrace tailWord_1073924 prefixEnd_1073924 122542044088702555802471 := by
  unfold tailWord_1073924
  simp only [CollatzResearch.WordTrace]
  refine ⟨19584613080682117231082413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26112817440909489641443217 19584613080682117231082413)
  ·
    refine ⟨7344229905255793961655905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19584613080682117231082413 7344229905255793961655905)
    ·
      refine ⟨5508172428941845471241929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7344229905255793961655905 5508172428941845471241929)
      ·
        refine ⟨4131129321706384103431447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5508172428941845471241929 4131129321706384103431447)
        ·
          refine ⟨6196693982559576155147171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4131129321706384103431447 6196693982559576155147171)
          ·
            refine ⟨9295040973839364232720757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6196693982559576155147171 9295040973839364232720757)
            ·
              refine ⟨871410091297440396817571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9295040973839364232720757 871410091297440396817571)
              ·
                refine ⟨1307115136946160595226357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871410091297440396817571 1307115136946160595226357)
                ·
                  refine ⟨122542044088702555802471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1307115136946160595226357 122542044088702555802471)
                  ·
                    rfl

theorem cell22_1073924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_1073924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073924 prefixEnd_1073924 := by exact prefixLift 1073924
  have htrace : WordTrace (prefixWord ++ tailWord_1073924) baseStart_1073924 baseEnd_1073924 := by
    simpa [prefixWord, tailWord_1073924, baseEnd_1073924] using wordTrace_append hprefix tailTrace_1073924
  have hstable : (prefixWord ++ tailWord_1073924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073924).length < 2 ^ (prefixWord ++ tailWord_1073924).sum := by decide
  have hdescent : baseEnd_1073924 < baseStart_1073924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073935 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 6]
def baseStart_1073935 : Nat := 118140960795 + 1073935 * 2 ^ 59
def prefixEnd_1073935 : Nat := 4983230072969 + 3 ^ 40 * 1073935 * 2
def baseEnd_1073935 : Nat := 122543299263635768460793

theorem tailTrace_1073935 : CollatzResearch.WordTrace tailWord_1073935 prefixEnd_1073935 122543299263635768460793 := by
  unfold tailWord_1073935
  simp only [CollatzResearch.WordTrace]
  refine ⟨39169627364324383340815259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26113084909549588893876839 39169627364324383340815259)
  ·
    refine ⟨58754441046486575011222889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39169627364324383340815259 58754441046486575011222889)
    ·
      refine ⟨44065830784864931258417167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58754441046486575011222889 44065830784864931258417167)
      ·
        refine ⟨66098746177297396887625751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44065830784864931258417167 66098746177297396887625751)
        ·
          refine ⟨99148119265946095331438627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66098746177297396887625751 99148119265946095331438627)
          ·
            refine ⟨148722178898919142997157941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99148119265946095331438627 148722178898919142997157941)
            ·
              refine ⟨13942704271773669655983557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148722178898919142997157941 13942704271773669655983557)
              ·
                refine ⟨2614257050957563060496917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13942704271773669655983557 2614257050957563060496917)
                ·
                  refine ⟨122543299263635768460793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2614257050957563060496917 122543299263635768460793)
                  ·
                    rfl

theorem cell22_1073935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 6].length) (baseStart_1073935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073935 prefixEnd_1073935 := by exact prefixLift 1073935
  have htrace : WordTrace (prefixWord ++ tailWord_1073935) baseStart_1073935 baseEnd_1073935 := by
    simpa [prefixWord, tailWord_1073935, baseEnd_1073935] using wordTrace_append hprefix tailTrace_1073935
  have hstable : (prefixWord ++ tailWord_1073935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073935).length < 2 ^ (prefixWord ++ tailWord_1073935).sum := by decide
  have hdescent : baseEnd_1073935 < baseStart_1073935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073937 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_1073937 : Nat := 118140960795 + 1073937 * 2 ^ 59
def prefixEnd_1073937 : Nat := 4983230072969 + 3 ^ 40 * 1073937 * 2
def baseEnd_1073937 : Nat := 367630582431779966832373

theorem tailTrace_1073937 : CollatzResearch.WordTrace tailWord_1073937 prefixEnd_1073937 367630582431779966832373 := by
  unfold tailWord_1073937
  simp only [CollatzResearch.WordTrace]
  refine ⟨39169700310317137682388065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26113133540211425121592043 39169700310317137682388065)
  ·
    refine ⟨29377275232737853261791049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39169700310317137682388065 29377275232737853261791049)
    ·
      refine ⟨22032956424553389946343287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29377275232737853261791049 22032956424553389946343287)
      ·
        refine ⟨33049434636830084919514931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22032956424553389946343287 33049434636830084919514931)
        ·
          refine ⟨49574151955245127379272397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33049434636830084919514931 49574151955245127379272397)
          ·
            refine ⟨18590306983216922767227149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49574151955245127379272397 18590306983216922767227149)
            ·
              refine ⟨6971365118706346037710181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18590306983216922767227149 6971365118706346037710181)
              ·
                refine ⟨1307130959757439882070659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6971365118706346037710181 1307130959757439882070659)
                ·
                  refine ⟨1960696439636159823105989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307130959757439882070659 1960696439636159823105989)
                  ·
                    refine ⟨367630582431779966832373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1960696439636159823105989 367630582431779966832373)
                    ·
                      rfl

theorem cell22_1073937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_1073937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073937 prefixEnd_1073937 := by exact prefixLift 1073937
  have htrace : WordTrace (prefixWord ++ tailWord_1073937) baseStart_1073937 baseEnd_1073937 := by
    simpa [prefixWord, tailWord_1073937, baseEnd_1073937] using wordTrace_append hprefix tailTrace_1073937
  have hstable : (prefixWord ++ tailWord_1073937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073937).length < 2 ^ (prefixWord ++ tailWord_1073937).sum := by decide
  have hdescent : baseEnd_1073937 < baseStart_1073937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073954 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1073954 : Nat := 118140960795 + 1073954 * 2 ^ 59
def prefixEnd_1073954 : Nat := 4983230072969 + 3 ^ 40 * 1073954 * 2
def baseEnd_1073954 : Nat := 367636401879197589157321

theorem tailTrace_1073954 : CollatzResearch.WordTrace tailWord_1073954 prefixEnd_1073954 367636401879197589157321 := by
  unfold tailWord_1073954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9792580087813887396439229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26113546900837033057171277 9792580087813887396439229)
  ·
    refine ⟨3672217532930207773664711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9792580087813887396439229 3672217532930207773664711)
    ·
      refine ⟨5508326299395311660497067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672217532930207773664711 5508326299395311660497067)
      ·
        refine ⟨8262489449092967490745601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5508326299395311660497067 8262489449092967490745601)
        ·
          refine ⟨6196867086819725618059201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262489449092967490745601 6196867086819725618059201)
          ·
            refine ⟨4647650315114794213544401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6196867086819725618059201 4647650315114794213544401)
            ·
              refine ⟨3485737736336095660158301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4647650315114794213544401 3485737736336095660158301)
              ·
                refine ⟨1307151651126035872559363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3485737736336095660158301 1307151651126035872559363)
                ·
                  refine ⟨1960727476689053808839045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307151651126035872559363 1960727476689053808839045)
                  ·
                    refine ⟨367636401879197589157321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1960727476689053808839045 367636401879197589157321)
                    ·
                      rfl

theorem cell22_1073954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1073954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1073954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1073954 prefixEnd_1073954 := by exact prefixLift 1073954
  have htrace : WordTrace (prefixWord ++ tailWord_1073954) baseStart_1073954 baseEnd_1073954 := by
    simpa [prefixWord, tailWord_1073954, baseEnd_1073954] using wordTrace_append hprefix tailTrace_1073954
  have hstable : (prefixWord ++ tailWord_1073954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073954).length < 2 ^ (prefixWord ++ tailWord_1073954).sum := by decide
  have hdescent : baseEnd_1073954 < baseStart_1073954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074018 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1074018 : Nat := 118140960795 + 1074018 * 2 ^ 59
def prefixEnd_1074018 : Nat := 4983230072969 + 3 ^ 40 * 1074018 * 2
def baseEnd_1074018 : Nat := 367658310387122755557125

theorem tailTrace_1074018 : CollatzResearch.WordTrace tailWord_1074018 prefixEnd_1074018 367658310387122755557125 := by
  unfold tailWord_1074018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793163655755922129021677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26115103082015792344057805 9793163655755922129021677)
  ·
    refine ⟨3672436370908470798383129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9793163655755922129021677 3672436370908470798383129)
    ·
      refine ⟨2754327278181353098787347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3672436370908470798383129 2754327278181353098787347)
      ·
        refine ⟨4131490917272029648181021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754327278181353098787347 4131490917272029648181021)
        ·
          refine ⟨1549309093977011118067883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4131490917272029648181021 1549309093977011118067883)
          ·
            refine ⟨2323963640965516677101825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549309093977011118067883 2323963640965516677101825)
            ·
              refine ⟨1742972730724137507826369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323963640965516677101825 1742972730724137507826369)
              ·
                refine ⟨1307229548043103130869777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742972730724137507826369 1307229548043103130869777)
                ·
                  refine ⟨980422161032327348152333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1307229548043103130869777 980422161032327348152333)
                  ·
                    refine ⟨367658310387122755557125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980422161032327348152333 367658310387122755557125)
                    ·
                      rfl

theorem cell22_1074018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1074018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074018 prefixEnd_1074018 := by exact prefixLift 1074018
  have htrace : WordTrace (prefixWord ++ tailWord_1074018) baseStart_1074018 baseEnd_1074018 := by
    simpa [prefixWord, tailWord_1074018, baseEnd_1074018] using wordTrace_append hprefix tailTrace_1074018
  have hstable : (prefixWord ++ tailWord_1074018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074018).length < 2 ^ (prefixWord ++ tailWord_1074018).sum := by decide
  have hdescent : baseEnd_1074018 < baseStart_1074018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074029 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_1074029 : Nat := 118140960795 + 1074029 * 2 ^ 59
def prefixEnd_1074029 : Nat := 4983230072969 + 3 ^ 40 * 1074029 * 2
def baseEnd_1074029 : Nat := 367662075911922393532091

theorem tailTrace_1074029 : CollatzResearch.WordTrace tailWord_1074029 prefixEnd_1074029 367662075911922393532091 := by
  unfold tailWord_1074029
  simp only [CollatzResearch.WordTrace]
  refine ⟨39173055825983837394737141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26115370550655891596491427 39173055825983837394737141)
  ·
    refine ⟨3672473983685984755756607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39173055825983837394737141 3672473983685984755756607)
    ·
      refine ⟨5508710975528977133634911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672473983685984755756607 5508710975528977133634911)
      ·
        refine ⟨8263066463293465700452367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5508710975528977133634911 8263066463293465700452367)
        ·
          refine ⟨12394599694940198550678551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8263066463293465700452367 12394599694940198550678551)
          ·
            refine ⟨18591899542410297826017827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12394599694940198550678551 18591899542410297826017827)
            ·
              refine ⟨27887849313615446739026741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18591899542410297826017827 27887849313615446739026741)
              ·
                refine ⟨2614485873151448131783757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27887849313615446739026741 2614485873151448131783757)
                ·
                  refine ⟨980432202431793049418909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2614485873151448131783757 980432202431793049418909)
                  ·
                    refine ⟨367662075911922393532091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980432202431793049418909 367662075911922393532091)
                    ·
                      rfl

theorem cell22_1074029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_1074029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074029 prefixEnd_1074029 := by exact prefixLift 1074029
  have htrace : WordTrace (prefixWord ++ tailWord_1074029) baseStart_1074029 baseEnd_1074029 := by
    simpa [prefixWord, tailWord_1074029, baseEnd_1074029] using wordTrace_append hprefix tailTrace_1074029
  have hstable : (prefixWord ++ tailWord_1074029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074029).length < 2 ^ (prefixWord ++ tailWord_1074029).sum := by decide
  have hdescent : baseEnd_1074029 < baseStart_1074029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074050 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1074050 : Nat := 118140960795 + 1074050 * 2 ^ 59
def prefixEnd_1074050 : Nat := 4983230072969 + 3 ^ 40 * 1074050 * 2
def baseEnd_1074050 : Nat := 367669264641085338757027

theorem tailTrace_1074050 : CollatzResearch.WordTrace tailWord_1074050 prefixEnd_1074050 367669264641085338757027 := by
  unfold tailWord_1074050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793455439726939495312901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26115881172605171987501069 9793455439726939495312901)
  ·
    refine ⟨1836272894948801155371169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9793455439726939495312901 1836272894948801155371169)
    ·
      refine ⟨1377204671211600866528377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1836272894948801155371169 1377204671211600866528377)
      ·
        refine ⟨1032903503408700649896283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1377204671211600866528377 1032903503408700649896283)
        ·
          refine ⟨1549355255113050974844425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032903503408700649896283 1549355255113050974844425)
          ·
            refine ⟨1162016441334788231133319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549355255113050974844425 1162016441334788231133319)
            ·
              refine ⟨1743024662002182346699979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162016441334788231133319 1743024662002182346699979)
              ·
                refine ⟨2614536993003273520049969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743024662002182346699979 2614536993003273520049969)
                ·
                  refine ⟨1960902744752455140037477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2614536993003273520049969 1960902744752455140037477)
                  ·
                    refine ⟨367669264641085338757027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1960902744752455140037477 367669264641085338757027)
                    ·
                      rfl

theorem cell22_1074050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1074050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074050 prefixEnd_1074050 := by exact prefixLift 1074050
  have htrace : WordTrace (prefixWord ++ tailWord_1074050) baseStart_1074050 baseEnd_1074050 := by
    simpa [prefixWord, tailWord_1074050, baseEnd_1074050] using wordTrace_append hprefix tailTrace_1074050
  have hstable : (prefixWord ++ tailWord_1074050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074050).length < 2 ^ (prefixWord ++ tailWord_1074050).sum := by decide
  have hdescent : baseEnd_1074050 < baseStart_1074050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074119 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 4, 3]
def baseStart_1074119 : Nat := 118140960795 + 1074119 * 2 ^ 59
def prefixEnd_1074119 : Nat := 4983230072969 + 3 ^ 40 * 1074119 * 2
def baseEnd_1074119 : Nat := 367692884751192158781815

theorem tailTrace_1074119 : CollatzResearch.WordTrace tailWord_1074119 prefixEnd_1074119 367692884751192158781815 := by
  unfold tailWord_1074119
  simp only [CollatzResearch.WordTrace]
  refine ⟨39176338395657782765513411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26117558930438521843675607 39176338395657782765513411)
  ·
    refine ⟨58764507593486674148270117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39176338395657782765513411 58764507593486674148270117)
    ·
      refine ⟨11018345173778751402800647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58764507593486674148270117 11018345173778751402800647)
      ·
        refine ⟨16527517760668127104200971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11018345173778751402800647 16527517760668127104200971)
        ·
          refine ⟨24791276641002190656301457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16527517760668127104200971 24791276641002190656301457)
          ·
            refine ⟨18593457480751642992226093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24791276641002190656301457 18593457480751642992226093)
            ·
              refine ⟨6972546555281866122084785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18593457480751642992226093 6972546555281866122084785)
              ·
                refine ⟨5229409916461399591563589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6972546555281866122084785 5229409916461399591563589)
                ·
                  refine ⟨980514359336512423418173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5229409916461399591563589 980514359336512423418173)
                  ·
                    refine ⟨367692884751192158781815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980514359336512423418173 367692884751192158781815)
                    ·
                      rfl

theorem cell22_1074119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_1074119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074119 prefixEnd_1074119 := by exact prefixLift 1074119
  have htrace : WordTrace (prefixWord ++ tailWord_1074119) baseStart_1074119 baseEnd_1074119 := by
    simpa [prefixWord, tailWord_1074119, baseEnd_1074119] using wordTrace_append hprefix tailTrace_1074119
  have hstable : (prefixWord ++ tailWord_1074119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074119).length < 2 ^ (prefixWord ++ tailWord_1074119).sum := by decide
  have hdescent : baseEnd_1074119 < baseStart_1074119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074138 : List Nat := [3, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_1074138 : Nat := 118140960795 + 1074138 * 2 ^ 59
def prefixEnd_1074138 : Nat := 4983230072969 + 3 ^ 40 * 1074138 * 2
def baseEnd_1074138 : Nat := 122566462946494147518919

theorem tailTrace_1074138 : CollatzResearch.WordTrace tailWord_1074138 prefixEnd_1074138 122566462946494147518919 := by
  unfold tailWord_1074138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794257845647237252613767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26118020921725966006970045 9794257845647237252613767)
  ·
    refine ⟨14691386768470855878920651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9794257845647237252613767 14691386768470855878920651)
    ·
      refine ⟨22037080152706283818380977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14691386768470855878920651 22037080152706283818380977)
      ·
        refine ⟨16527810114529712863785733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22037080152706283818380977 16527810114529712863785733)
        ·
          refine ⟨3098964396474321161959825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16527810114529712863785733 3098964396474321161959825)
          ·
            refine ⟨2324223297355740871469869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3098964396474321161959825 2324223297355740871469869)
            ·
              refine ⟨871583736508402826801201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2324223297355740871469869 871583736508402826801201)
              ·
                refine ⟨653687802381302120100901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871583736508402826801201 653687802381302120100901)
                ·
                  refine ⟨122566462946494147518919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653687802381302120100901 122566462946494147518919)
                  ·
                    rfl

theorem cell22_1074138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_1074138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074138 prefixEnd_1074138 := by exact prefixLift 1074138
  have htrace : WordTrace (prefixWord ++ tailWord_1074138) baseStart_1074138 baseEnd_1074138 := by
    simpa [prefixWord, tailWord_1074138, baseEnd_1074138] using wordTrace_append hprefix tailTrace_1074138
  have hstable : (prefixWord ++ tailWord_1074138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074138).length < 2 ^ (prefixWord ++ tailWord_1074138).sum := by decide
  have hdescent : baseEnd_1074138 < baseStart_1074138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074209 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1074209 : Nat := 118140960795 + 1074209 * 2 ^ 59
def prefixEnd_1074209 : Nat := 4983230072969 + 3 ^ 40 * 1074209 * 2
def baseEnd_1074209 : Nat := 367723693590461924031539

theorem tailTrace_1074209 : CollatzResearch.WordTrace tailWord_1074209 prefixEnd_1074209 367723693590461924031539 := by
  unfold tailWord_1074209
  simp only [CollatzResearch.WordTrace]
  refine ⟨39179620965331728136289681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26119747310221152090859787 39179620965331728136289681)
  ·
    refine ⟨29384715723998796102217261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39179620965331728136289681 29384715723998796102217261)
    ·
      refine ⟨11019268396499548538331473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29384715723998796102217261 11019268396499548538331473)
      ·
        refine ⟨8264451297374661403748605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11019268396499548538331473 8264451297374661403748605)
        ·
          refine ⟨3099169236515498026405727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8264451297374661403748605 3099169236515498026405727)
          ·
            refine ⟨4648753854773247039608591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099169236515498026405727 4648753854773247039608591)
            ·
              refine ⟨6973130782159870559412887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648753854773247039608591 6973130782159870559412887)
              ·
                refine ⟨10459696173239805839119331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6973130782159870559412887 10459696173239805839119331)
                ·
                  refine ⟨15689544259859708758678997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10459696173239805839119331 15689544259859708758678997)
                  ·
                    refine ⟨367723693590461924031539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15689544259859708758678997 367723693590461924031539)
                    ·
                      rfl

theorem cell22_1074209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1074209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074209 prefixEnd_1074209 := by exact prefixLift 1074209
  have htrace : WordTrace (prefixWord ++ tailWord_1074209) baseStart_1074209 baseEnd_1074209 := by
    simpa [prefixWord, tailWord_1074209, baseEnd_1074209] using wordTrace_append hprefix tailTrace_1074209
  have hstable : (prefixWord ++ tailWord_1074209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074209).length < 2 ^ (prefixWord ++ tailWord_1074209).sum := by decide
  have hdescent : baseEnd_1074209 < baseStart_1074209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074224 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_1074224 : Nat := 118140960795 + 1074224 * 2 ^ 59
def prefixEnd_1074224 : Nat := 4983230072969 + 3 ^ 40 * 1074224 * 2
def baseEnd_1074224 : Nat := 367728828397006884906493

theorem tailTrace_1074224 : CollatzResearch.WordTrace tailWord_1074224 prefixEnd_1074224 367728828397006884906493 := by
  unfold tailWord_1074224
  simp only [CollatzResearch.WordTrace]
  refine ⟨19590084030138692849042863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26120112040184923798723817 19590084030138692849042863)
  ·
    refine ⟨29385126045208039273564295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19590084030138692849042863 29385126045208039273564295)
    ·
      refine ⟨44077689067812058910346443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29385126045208039273564295 44077689067812058910346443)
      ·
        refine ⟨66116533601718088365519665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44077689067812058910346443 66116533601718088365519665)
        ·
          refine ⟨49587400201288566274139749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66116533601718088365519665 49587400201288566274139749)
          ·
            refine ⟨9297637537741606176401203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49587400201288566274139749 9297637537741606176401203)
            ·
              refine ⟨13946456306612409264601805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9297637537741606176401203 13946456306612409264601805)
              ·
                refine ⟨5229921114979653474225677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13946456306612409264601805 5229921114979653474225677)
                ·
                  refine ⟨1961220418117370052834629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5229921114979653474225677 1961220418117370052834629)
                  ·
                    refine ⟨367728828397006884906493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961220418117370052834629 367728828397006884906493)
                    ·
                      rfl

theorem cell22_1074224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_1074224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074224 prefixEnd_1074224 := by exact prefixLift 1074224
  have htrace : WordTrace (prefixWord ++ tailWord_1074224) baseStart_1074224 baseEnd_1074224 := by
    simpa [prefixWord, tailWord_1074224, baseEnd_1074224] using wordTrace_append hprefix tailTrace_1074224
  have hstable : (prefixWord ++ tailWord_1074224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074224).length < 2 ^ (prefixWord ++ tailWord_1074224).sum := by decide
  have hdescent : baseEnd_1074224 < baseStart_1074224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074262 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1074262 : Nat := 118140960795 + 1074262 * 2 ^ 59
def prefixEnd_1074262 : Nat := 4983230072969 + 3 ^ 40 * 1074262 * 2
def baseEnd_1074262 : Nat := 122580612191195817485459

theorem tailTrace_1074262 : CollatzResearch.WordTrace tailWord_1074262 prefixEnd_1074262 122580612191195817485459 := by
  unfold tailWord_1074262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448847127133732386748065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26121036022759812125312693 2448847127133732386748065)
  ·
    refine ⟨1836635345350299290061049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2448847127133732386748065 1836635345350299290061049)
    ·
      refine ⟨1377476509012724467545787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1836635345350299290061049 1377476509012724467545787)
      ·
        refine ⟨2066214763519086701318681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377476509012724467545787 2066214763519086701318681)
        ·
          refine ⟨1549661072639315025989011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2066214763519086701318681 1549661072639315025989011)
          ·
            refine ⟨2324491608958972538983517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549661072639315025989011 2324491608958972538983517)
            ·
              refine ⟨871684353359614702118819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2324491608958972538983517 871684353359614702118819)
              ·
                refine ⟨1307526530039422053178229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871684353359614702118819 1307526530039422053178229)
                ·
                  refine ⟨122580612191195817485459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1307526530039422053178229 122580612191195817485459)
                  ·
                    rfl

theorem cell22_1074262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1074262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074262 prefixEnd_1074262 := by exact prefixLift 1074262
  have htrace : WordTrace (prefixWord ++ tailWord_1074262) baseStart_1074262 baseEnd_1074262 := by
    simpa [prefixWord, tailWord_1074262, baseEnd_1074262] using wordTrace_append hprefix tailTrace_1074262
  have hstable : (prefixWord ++ tailWord_1074262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074262).length < 2 ^ (prefixWord ++ tailWord_1074262).sum := by decide
  have hdescent : baseEnd_1074262 < baseStart_1074262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074284 : List Nat := [2, 2, 1, 1, 3, 2, 3, 8]
def baseStart_1074284 : Nat := 118140960795 + 1074284 * 2 ^ 59
def prefixEnd_1074284 : Nat := 4983230072969 + 3 ^ 40 * 1074284 * 2
def baseEnd_1074284 : Nat := 40861040847020747600701

theorem tailTrace_1074284 : CollatzResearch.WordTrace tailWord_1074284 prefixEnd_1074284 40861040847020747600701 := by
  unfold tailWord_1074284
  simp only [CollatzResearch.WordTrace]
  refine ⟨19591178220030007972634953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26121570960040010630179937 19591178220030007972634953)
  ·
    refine ⟨14693383665022505979476215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19591178220030007972634953 14693383665022505979476215)
    ·
      refine ⟨22040075497533758969214323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14693383665022505979476215 22040075497533758969214323)
      ·
        refine ⟨33060113246300638453821485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22040075497533758969214323 33060113246300638453821485)
        ·
          refine ⟨12397542467362739420183057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33060113246300638453821485 12397542467362739420183057)
          ·
            refine ⟨9298156850522054565137293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12397542467362739420183057 9298156850522054565137293)
            ·
              refine ⟨3486808818945770461926485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9298156850522054565137293 3486808818945770461926485)
              ·
                refine ⟨40861040847020747600701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3486808818945770461926485 40861040847020747600701)
                ·
                  rfl

theorem cell22_1074284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 8].length) (baseStart_1074284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074284 prefixEnd_1074284 := by exact prefixLift 1074284
  have htrace : WordTrace (prefixWord ++ tailWord_1074284) baseStart_1074284 baseEnd_1074284 := by
    simpa [prefixWord, tailWord_1074284, baseEnd_1074284] using wordTrace_append hprefix tailTrace_1074284
  have hstable : (prefixWord ++ tailWord_1074284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074284).length < 2 ^ (prefixWord ++ tailWord_1074284).sum := by decide
  have hdescent : baseEnd_1074284 < baseStart_1074284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074286 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1074286 : Nat := 118140960795 + 1074286 * 2 ^ 59
def prefixEnd_1074286 : Nat := 4983230072969 + 3 ^ 40 * 1074286 * 2
def baseEnd_1074286 : Nat := 367750052264059389856303

theorem tailTrace_1074286 : CollatzResearch.WordTrace tailWord_1074286 prefixEnd_1074286 367750052264059389856303 := by
  unfold tailWord_1074286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4897803673256596285855339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26121619590701846857895141 4897803673256596285855339)
  ·
    refine ⟨7346705509884894428783009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4897803673256596285855339 7346705509884894428783009)
    ·
      refine ⟨5510029132413670821587257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7346705509884894428783009 5510029132413670821587257)
      ·
        refine ⟨4132521849310253116190443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5510029132413670821587257 4132521849310253116190443)
        ·
          refine ⟨6198782773965379674285665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132521849310253116190443 6198782773965379674285665)
          ·
            refine ⟨4649087080474034755714249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6198782773965379674285665 4649087080474034755714249)
            ·
              refine ⟨3486815310355526066785687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649087080474034755714249 3486815310355526066785687)
              ·
                refine ⟨5230222965533289100178531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3486815310355526066785687 5230222965533289100178531)
                ·
                  refine ⟨7845334448299933650267797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5230222965533289100178531 7845334448299933650267797)
                  ·
                    refine ⟨367750052264059389856303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7845334448299933650267797 367750052264059389856303)
                    ·
                      rfl

theorem cell22_1074286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1074286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074286 prefixEnd_1074286 := by exact prefixLift 1074286
  have htrace : WordTrace (prefixWord ++ tailWord_1074286) baseStart_1074286 baseEnd_1074286 := by
    simpa [prefixWord, tailWord_1074286, baseEnd_1074286] using wordTrace_append hprefix tailTrace_1074286
  have hstable : (prefixWord ++ tailWord_1074286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074286).length < 2 ^ (prefixWord ++ tailWord_1074286).sum := by decide
  have hdescent : baseEnd_1074286 < baseStart_1074286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074322 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1074322 : Nat := 118140960795 + 1074322 * 2 ^ 59
def prefixEnd_1074322 : Nat := 4983230072969 + 3 ^ 40 * 1074322 * 2
def baseEnd_1074322 : Nat := 367762375799767295956193

theorem tailTrace_1074322 : CollatzResearch.WordTrace tailWord_1074322 prefixEnd_1074322 367762375799767295956193 := by
  unfold tailWord_1074322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9795935603480587108788305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26122494942614898956768813 9795935603480587108788305)
  ·
    refine ⟨7346951702610440331591229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9795935603480587108788305 7346951702610440331591229)
    ·
      refine ⟨2755106888478915124346711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7346951702610440331591229 2755106888478915124346711)
      ·
        refine ⟨4132660332718372686520067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2755106888478915124346711 4132660332718372686520067)
        ·
          refine ⟨6198990499077559029780101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132660332718372686520067 6198990499077559029780101)
          ·
            refine ⟨1162310718577042318083769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6198990499077559029780101 1162310718577042318083769)
            ·
              refine ⟨871733038932781738562827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162310718577042318083769 871733038932781738562827)
              ·
                refine ⟨1307599558399172607844241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871733038932781738562827 1307599558399172607844241)
                ·
                  refine ⟨980699668799379455883181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1307599558399172607844241 980699668799379455883181)
                  ·
                    refine ⟨367762375799767295956193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980699668799379455883181 367762375799767295956193)
                    ·
                      rfl

theorem cell22_1074322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1074322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074322 prefixEnd_1074322 := by exact prefixLift 1074322
  have htrace : WordTrace (prefixWord ++ tailWord_1074322) baseStart_1074322 baseEnd_1074322 := by
    simpa [prefixWord, tailWord_1074322, baseEnd_1074322] using wordTrace_append hprefix tailTrace_1074322
  have hstable : (prefixWord ++ tailWord_1074322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074322).length < 2 ^ (prefixWord ++ tailWord_1074322).sum := by decide
  have hdescent : baseEnd_1074322 < baseStart_1074322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074376 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1074376 : Nat := 118140960795 + 1074376 * 2 ^ 59
def prefixEnd_1074376 : Nat := 4983230072969 + 3 ^ 40 * 1074376 * 2
def baseEnd_1074376 : Nat := 367780861103329155106027

theorem tailTrace_1074376 : CollatzResearch.WordTrace tailWord_1074376 prefixEnd_1074376 367780861103329155106027 := by
  unfold tailWord_1074376
  simp only [CollatzResearch.WordTrace]
  refine ⟨19592855977863357828809491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26123807970484477105079321 19592855977863357828809491)
  ·
    refine ⟨29389283966795036743214237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19592855977863357828809491 29389283966795036743214237)
    ·
      refine ⟨11020981487548138778705339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29389283966795036743214237 11020981487548138778705339)
      ·
        refine ⟨16531472231322208168058009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11020981487548138778705339 16531472231322208168058009)
        ·
          refine ⟨12398604173491656126043507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16531472231322208168058009 12398604173491656126043507)
          ·
            refine ⟨18597906260237484189065261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12398604173491656126043507 18597906260237484189065261)
            ·
              refine ⟨6974214847589056570899473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18597906260237484189065261 6974214847589056570899473)
              ·
                refine ⟨5230661135691792428174605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6974214847589056570899473 5230661135691792428174605)
                ·
                  refine ⟨1961497925884422160565477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5230661135691792428174605 1961497925884422160565477)
                  ·
                    refine ⟨367780861103329155106027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961497925884422160565477 367780861103329155106027)
                    ·
                      rfl

theorem cell22_1074376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1074376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074376 prefixEnd_1074376 := by exact prefixLift 1074376
  have htrace : WordTrace (prefixWord ++ tailWord_1074376) baseStart_1074376 baseEnd_1074376 := by
    simpa [prefixWord, tailWord_1074376, baseEnd_1074376] using wordTrace_append hprefix tailTrace_1074376
  have hstable : (prefixWord ++ tailWord_1074376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074376).length < 2 ^ (prefixWord ++ tailWord_1074376).sum := by decide
  have hdescent : baseEnd_1074376 < baseStart_1074376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074410 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_1074410 : Nat := 118140960795 + 1074410 * 2 ^ 59
def prefixEnd_1074410 : Nat := 4983230072969 + 3 ^ 40 * 1074410 * 2
def baseEnd_1074410 : Nat := 367792499998164399755923

theorem tailTrace_1074410 : CollatzResearch.WordTrace tailWord_1074410 prefixEnd_1074410 367792499998164399755923 := by
  unfold tailWord_1074410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9796738009400884866089171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26124634691735692976237789 9796738009400884866089171)
  ·
    refine ⟨14695107014101327299133757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9796738009400884866089171 14695107014101327299133757)
    ·
      refine ⟨5510665130287997737175159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14695107014101327299133757 5510665130287997737175159)
      ·
        refine ⟨8265997695431996605762739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510665130287997737175159 8265997695431996605762739)
        ·
          refine ⟨12398996543147994908644109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8265997695431996605762739 12398996543147994908644109)
          ·
            refine ⟨4649623703680498090741541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12398996543147994908644109 4649623703680498090741541)
            ·
              refine ⟨871804444440093392014039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4649623703680498090741541 871804444440093392014039)
              ·
                refine ⟨1307706666660140088021059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871804444440093392014039 1307706666660140088021059)
                ·
                  refine ⟨1961559999990210132031589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307706666660140088021059 1961559999990210132031589)
                  ·
                    refine ⟨367792499998164399755923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961559999990210132031589 367792499998164399755923)
                    ·
                      rfl

theorem cell22_1074410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_1074410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074410 prefixEnd_1074410 := by exact prefixLift 1074410
  have htrace : WordTrace (prefixWord ++ tailWord_1074410) baseStart_1074410 baseEnd_1074410 := by
    simpa [prefixWord, tailWord_1074410, baseEnd_1074410] using wordTrace_append hprefix tailTrace_1074410
  have hstable : (prefixWord ++ tailWord_1074410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074410).length < 2 ^ (prefixWord ++ tailWord_1074410).sum := by decide
  have hdescent : baseEnd_1074410 < baseStart_1074410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074440 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1074440 : Nat := 118140960795 + 1074440 * 2 ^ 59
def prefixEnd_1074440 : Nat := 4983230072969 + 3 ^ 40 * 1074440 * 2
def baseEnd_1074440 : Nat := 367802769611254321505831

theorem tailTrace_1074440 : CollatzResearch.WordTrace tailWord_1074440 prefixEnd_1074440 367802769611254321505831 := by
  unfold tailWord_1074440
  simp only [CollatzResearch.WordTrace]
  refine ⟨19594023113747427293974387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26125364151663236391965849 19594023113747427293974387)
  ·
    refine ⟨29391034670621140940961581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19594023113747427293974387 29391034670621140940961581)
    ·
      refine ⟨11021638001482927852860593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29391034670621140940961581 11021638001482927852860593)
      ·
        refine ⟨8266228501112195889645445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11021638001482927852860593 8266228501112195889645445)
        ·
          refine ⟨1549917843958536729308521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8266228501112195889645445 1549917843958536729308521)
          ·
            refine ⟨1162438382968902546981391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549917843958536729308521 1162438382968902546981391)
            ·
              refine ⟨1743657574453353820472087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162438382968902546981391 1743657574453353820472087)
              ·
                refine ⟨2615486361680030730708131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743657574453353820472087 2615486361680030730708131)
                ·
                  refine ⟨3923229542520046096062197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615486361680030730708131 3923229542520046096062197)
                  ·
                    refine ⟨367802769611254321505831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3923229542520046096062197 367802769611254321505831)
                    ·
                      rfl

theorem cell22_1074440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1074440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074440 prefixEnd_1074440 := by exact prefixLift 1074440
  have htrace : WordTrace (prefixWord ++ tailWord_1074440) baseStart_1074440 baseEnd_1074440 := by
    simpa [prefixWord, tailWord_1074440, baseEnd_1074440] using wordTrace_append hprefix tailTrace_1074440
  have hstable : (prefixWord ++ tailWord_1074440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074440).length < 2 ^ (prefixWord ++ tailWord_1074440).sum := by decide
  have hdescent : baseEnd_1074440 < baseStart_1074440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074485 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1074485 : Nat := 118140960795 + 1074485 * 2 ^ 59
def prefixEnd_1074485 : Nat := 4983230072969 + 3 ^ 40 * 1074485 * 2
def baseEnd_1074485 : Nat := 367818174030889204130693

theorem tailTrace_1074485 : CollatzResearch.WordTrace tailWord_1074485 prefixEnd_1074485 367818174030889204130693 := by
  unfold tailWord_1074485
  simp only [CollatzResearch.WordTrace]
  refine ⟨39189687512331827273336909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26126458341554551515557939 39189687512331827273336909)
  ·
    refine ⟨14696132817124435227501341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39189687512331827273336909 14696132817124435227501341)
    ·
      refine ⟨5511049806421663210313003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14696132817124435227501341 5511049806421663210313003)
      ·
        refine ⟨8266574709632494815469505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5511049806421663210313003 8266574709632494815469505)
        ·
          refine ⟨6199931032224371111602129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8266574709632494815469505 6199931032224371111602129)
          ·
            refine ⟨4649948274168278333701597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6199931032224371111602129 4649948274168278333701597)
            ·
              refine ⟨1743730602813104375138099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4649948274168278333701597 1743730602813104375138099)
              ·
                refine ⟨2615595904219656562707149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743730602813104375138099 2615595904219656562707149)
                ·
                  refine ⟨980848464082371211015181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2615595904219656562707149 980848464082371211015181)
                  ·
                    refine ⟨367818174030889204130693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980848464082371211015181 367818174030889204130693)
                    ·
                      rfl

theorem cell22_1074485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1074485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074485 prefixEnd_1074485 := by exact prefixLift 1074485
  have htrace : WordTrace (prefixWord ++ tailWord_1074485) baseStart_1074485 baseEnd_1074485 := by
    simpa [prefixWord, tailWord_1074485, baseEnd_1074485] using wordTrace_append hprefix tailTrace_1074485
  have hstable : (prefixWord ++ tailWord_1074485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074485).length < 2 ^ (prefixWord ++ tailWord_1074485).sum := by decide
  have hdescent : baseEnd_1074485 < baseStart_1074485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074496 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_1074496 : Nat := 118140960795 + 1074496 * 2 ^ 59
def prefixEnd_1074496 : Nat := 4983230072969 + 3 ^ 40 * 1074496 * 2
def baseEnd_1074496 : Nat := 367821939555688842105659

theorem tailTrace_1074496 : CollatzResearch.WordTrace tailWord_1074496 prefixEnd_1074496 367821939555688842105659 := by
  unfold tailWord_1074496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19595044357645988075993671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26126725810194650767991561 19595044357645988075993671)
  ·
    refine ⟨29392566536468982113990507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19595044357645988075993671 29392566536468982113990507)
    ·
      refine ⟨44088849804703473170985761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29392566536468982113990507 44088849804703473170985761)
      ·
        refine ⟨33066637353527604878239321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44088849804703473170985761 33066637353527604878239321)
        ·
          refine ⟨24799978015145703658679491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33066637353527604878239321 24799978015145703658679491)
          ·
            refine ⟨37199967022718555488019237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24799978015145703658679491 37199967022718555488019237)
            ·
              refine ⟨6974993816759729154003607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37199967022718555488019237 6974993816759729154003607)
              ·
                refine ⟨10462490725139593731005411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6974993816759729154003607 10462490725139593731005411)
                ·
                  refine ⟨15693736087709390596508117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10462490725139593731005411 15693736087709390596508117)
                  ·
                    refine ⟨367821939555688842105659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15693736087709390596508117 367821939555688842105659)
                    ·
                      rfl

theorem cell22_1074496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_1074496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074496 prefixEnd_1074496 := by exact prefixLift 1074496
  have htrace : WordTrace (prefixWord ++ tailWord_1074496) baseStart_1074496 baseEnd_1074496 := by
    simpa [prefixWord, tailWord_1074496, baseEnd_1074496] using wordTrace_append hprefix tailTrace_1074496
  have hstable : (prefixWord ++ tailWord_1074496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074496).length < 2 ^ (prefixWord ++ tailWord_1074496).sum := by decide
  have hdescent : baseEnd_1074496 < baseStart_1074496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074536 : List Nat := [2, 1, 4, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1074536 : Nat := 118140960795 + 1074536 * 2 ^ 59
def prefixEnd_1074536 : Nat := 4983230072969 + 3 ^ 40 * 1074536 * 2
def baseEnd_1074536 : Nat := 367835632373142071105537

theorem tailTrace_1074536 : CollatzResearch.WordTrace tailWord_1074536 prefixEnd_1074536 367835632373142071105537 := by
  unfold tailWord_1074536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19595773817573531491721731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26127698423431375322295641 19595773817573531491721731)
  ·
    refine ⟨29393660726360297237582597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19595773817573531491721731 29393660726360297237582597)
    ·
      refine ⟨5511311386192555732046737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29393660726360297237582597 5511311386192555732046737)
      ·
        refine ⟨4133483539644416799035053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5511311386192555732046737 4133483539644416799035053)
        ·
          refine ⟨1550056327366656299638145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4133483539644416799035053 1550056327366656299638145)
          ·
            refine ⟨1162542245524992224728609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1550056327366656299638145 1162542245524992224728609)
            ·
              refine ⟨871906684143744168546457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162542245524992224728609 871906684143744168546457)
              ·
                refine ⟨653930013107808126409843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871906684143744168546457 653930013107808126409843)
                ·
                  refine ⟨980895019661712189614765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653930013107808126409843 980895019661712189614765)
                  ·
                    refine ⟨367835632373142071105537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980895019661712189614765 367835632373142071105537)
                    ·
                      rfl

theorem cell22_1074536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1074536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074536 prefixEnd_1074536 := by exact prefixLift 1074536
  have htrace : WordTrace (prefixWord ++ tailWord_1074536) baseStart_1074536 baseEnd_1074536 := by
    simpa [prefixWord, tailWord_1074536, baseEnd_1074536] using wordTrace_append hprefix tailTrace_1074536
  have hstable : (prefixWord ++ tailWord_1074536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074536).length < 2 ^ (prefixWord ++ tailWord_1074536).sum := by decide
  have hdescent : baseEnd_1074536 < baseStart_1074536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074562 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1074562 : Nat := 118140960795 + 1074562 * 2 ^ 59
def prefixEnd_1074562 : Nat := 4983230072969 + 3 ^ 40 * 1074562 * 2
def baseEnd_1074562 : Nat := 367844532704486669955457

theorem tailTrace_1074562 : CollatzResearch.WordTrace tailWord_1074562 prefixEnd_1074562 367844532704486669955457 := by
  unfold tailWord_1074562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9798123983263217355972485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26128330622035246282593293 9798123983263217355972485)
  ·
    refine ⟨1837148246861853254244841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9798123983263217355972485 1837148246861853254244841)
    ·
      refine ⟨1377861185146389940683631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1837148246861853254244841 1377861185146389940683631)
      ·
        refine ⟨2066791777719584911025447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377861185146389940683631 2066791777719584911025447)
        ·
          refine ⟨3100187666579377366538171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2066791777719584911025447 3100187666579377366538171)
          ·
            refine ⟨4650281499869066049807257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100187666579377366538171 4650281499869066049807257)
            ·
              refine ⟨3487711124901799537355443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650281499869066049807257 3487711124901799537355443)
              ·
                refine ⟨5231566687352699306033165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487711124901799537355443 5231566687352699306033165)
                ·
                  refine ⟨1961837507757262239762437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5231566687352699306033165 1961837507757262239762437)
                  ·
                    refine ⟨367844532704486669955457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961837507757262239762437 367844532704486669955457)
                    ·
                      rfl

theorem cell22_1074562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1074562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074562 prefixEnd_1074562 := by exact prefixLift 1074562
  have htrace : WordTrace (prefixWord ++ tailWord_1074562) baseStart_1074562 baseEnd_1074562 := by
    simpa [prefixWord, tailWord_1074562, baseEnd_1074562] using wordTrace_append hprefix tailTrace_1074562
  have hstable : (prefixWord ++ tailWord_1074562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074562).length < 2 ^ (prefixWord ++ tailWord_1074562).sum := by decide
  have hdescent : baseEnd_1074562 < baseStart_1074562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074648 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1074648 : Nat := 118140960795 + 1074648 * 2 ^ 59
def prefixEnd_1074648 : Nat := 4983230072969 + 3 ^ 40 * 1074648 * 2
def baseEnd_1074648 : Nat := 367873972262011112305193

theorem tailTrace_1074648 : CollatzResearch.WordTrace tailWord_1074648 prefixEnd_1074648 367873972262011112305193 := by
  unfold tailWord_1074648
  simp only [CollatzResearch.WordTrace]
  refine ⟨19597816305370653055760299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26130421740494204074347065 19597816305370653055760299)
  ·
    refine ⟨29396724458055979583640449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19597816305370653055760299 29396724458055979583640449)
    ·
      refine ⟨22047543343541984687730337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29396724458055979583640449 22047543343541984687730337)
      ·
        refine ⟨16535657507656488515797753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22047543343541984687730337 16535657507656488515797753)
        ·
          refine ⟨12401743130742366386848315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16535657507656488515797753 12401743130742366386848315)
          ·
            refine ⟨18602614696113549580272473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12401743130742366386848315 18602614696113549580272473)
            ·
              refine ⟨13951961022085162185204355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18602614696113549580272473 13951961022085162185204355)
              ·
                refine ⟨20927941533127743277806533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13951961022085162185204355 20927941533127743277806533)
                ·
                  refine ⟨3923989037461451864588725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20927941533127743277806533 3923989037461451864588725)
                  ·
                    refine ⟨367873972262011112305193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3923989037461451864588725 367873972262011112305193)
                    ·
                      rfl

theorem cell22_1074648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1074648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074648 prefixEnd_1074648 := by exact prefixLift 1074648
  have htrace : WordTrace (prefixWord ++ tailWord_1074648) baseStart_1074648 baseEnd_1074648 := by
    simpa [prefixWord, tailWord_1074648, baseEnd_1074648] using wordTrace_append hprefix tailTrace_1074648
  have hstable : (prefixWord ++ tailWord_1074648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074648).length < 2 ^ (prefixWord ++ tailWord_1074648).sum := by decide
  have hdescent : baseEnd_1074648 < baseStart_1074648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074680 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1074680 : Nat := 118140960795 + 1074680 * 2 ^ 59
def prefixEnd_1074680 : Nat := 4983230072969 + 3 ^ 40 * 1074680 * 2
def baseEnd_1074680 : Nat := 367884926515973695505095

theorem tailTrace_1074680 : CollatzResearch.WordTrace tailWord_1074680 prefixEnd_1074680 367884926515973695505095 := by
  unfold tailWord_1074680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19598399873312687788342747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26131199831083583717790329 19598399873312687788342747)
  ·
    refine ⟨29397599809969031682514121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19598399873312687788342747 29397599809969031682514121)
    ·
      refine ⟨22048199857476773761885591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29397599809969031682514121 22048199857476773761885591)
      ·
        refine ⟨33072299786215160642828387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22048199857476773761885591 33072299786215160642828387)
        ·
          refine ⟨49608449679322740964242581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33072299786215160642828387 49608449679322740964242581)
          ·
            refine ⟨2325396078718253482698871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49608449679322740964242581 2325396078718253482698871)
            ·
              refine ⟨3488094118077380224048307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325396078718253482698871 3488094118077380224048307)
              ·
                refine ⟨5232141177116070336072461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488094118077380224048307 5232141177116070336072461)
                ·
                  refine ⟨1962052941418526376027173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5232141177116070336072461 1962052941418526376027173)
                  ·
                    refine ⟨367884926515973695505095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962052941418526376027173 367884926515973695505095)
                    ·
                      rfl

theorem cell22_1074680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1074680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074680 prefixEnd_1074680 := by exact prefixLift 1074680
  have htrace : WordTrace (prefixWord ++ tailWord_1074680) baseStart_1074680 baseEnd_1074680 := by
    simpa [prefixWord, tailWord_1074680, baseEnd_1074680] using wordTrace_append hprefix tailTrace_1074680
  have hstable : (prefixWord ++ tailWord_1074680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074680).length < 2 ^ (prefixWord ++ tailWord_1074680).sum := by decide
  have hdescent : baseEnd_1074680 < baseStart_1074680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074697 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 1, 4]
def baseStart_1074697 : Nat := 118140960795 + 1074697 * 2 ^ 59
def prefixEnd_1074697 : Nat := 4983230072969 + 3 ^ 40 * 1074697 * 2
def baseEnd_1074697 : Nat := 367890745963391317830043

theorem tailTrace_1074697 : CollatzResearch.WordTrace tailWord_1074697 prefixEnd_1074697 367890745963391317830043 := by
  unfold tailWord_1074697
  simp only [CollatzResearch.WordTrace]
  refine ⟨39197419787563787480054345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26131613191709191653369563 39197419787563787480054345)
  ·
    refine ⟨29398064840672840610040759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39197419787563787480054345 29398064840672840610040759)
    ·
      refine ⟨44097097261009260915061139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29398064840672840610040759 44097097261009260915061139)
      ·
        refine ⟨66145645891513891372591709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44097097261009260915061139 66145645891513891372591709)
        ·
          refine ⟨24804617209317709264721891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66145645891513891372591709 24804617209317709264721891)
          ·
            refine ⟨37206925813976563897082837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24804617209317709264721891 37206925813976563897082837)
            ·
              refine ⟨872037323765075716337879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37206925813976563897082837 872037323765075716337879)
              ·
                refine ⟨1308055985647613574506819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872037323765075716337879 1308055985647613574506819)
                ·
                  refine ⟨1962083978471420361760229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308055985647613574506819 1962083978471420361760229)
                  ·
                    refine ⟨367890745963391317830043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962083978471420361760229 367890745963391317830043)
                    ·
                      rfl

theorem cell22_1074697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_1074697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074697 prefixEnd_1074697 := by exact prefixLift 1074697
  have htrace : WordTrace (prefixWord ++ tailWord_1074697) baseStart_1074697 baseEnd_1074697 := by
    simpa [prefixWord, tailWord_1074697, baseEnd_1074697] using wordTrace_append hprefix tailTrace_1074697
  have hstable : (prefixWord ++ tailWord_1074697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074697).length < 2 ^ (prefixWord ++ tailWord_1074697).sum := by decide
  have hdescent : baseEnd_1074697 < baseStart_1074697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074701 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1074701 : Nat := 118140960795 + 1074701 * 2 ^ 59
def prefixEnd_1074701 : Nat := 4983230072969 + 3 ^ 40 * 1074701 * 2
def baseEnd_1074701 : Nat := 122630705081712213576677

theorem tailTrace_1074701 : CollatzResearch.WordTrace tailWord_1074701 prefixEnd_1074701 122630705081712213576677 := by
  unfold tailWord_1074701
  simp only [CollatzResearch.WordTrace]
  refine ⟨39197565679549296163199957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26131710453032864108799971 39197565679549296163199957)
  ·
    refine ⟨918692945614436628824999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39197565679549296163199957 918692945614436628824999)
    ·
      refine ⟨1378039418421654943237499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918692945614436628824999 1378039418421654943237499)
      ·
        refine ⟨2067059127632482414856249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378039418421654943237499 2067059127632482414856249)
        ·
          refine ⟨1550294345724361811142187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067059127632482414856249 1550294345724361811142187)
          ·
            refine ⟨2325441518586542716713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550294345724361811142187 2325441518586542716713281)
            ·
              refine ⟨1744081138939907037534961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325441518586542716713281 1744081138939907037534961)
              ·
                refine ⟨1308060854204930278151221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744081138939907037534961 1308060854204930278151221)
                ·
                  refine ⟨122630705081712213576677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1308060854204930278151221 122630705081712213576677)
                  ·
                    rfl

theorem cell22_1074701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1074701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074701 prefixEnd_1074701 := by exact prefixLift 1074701
  have htrace : WordTrace (prefixWord ++ tailWord_1074701) baseStart_1074701 baseEnd_1074701 := by
    simpa [prefixWord, tailWord_1074701, baseEnd_1074701] using wordTrace_append hprefix tailTrace_1074701
  have hstable : (prefixWord ++ tailWord_1074701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074701).length < 2 ^ (prefixWord ++ tailWord_1074701).sum := by decide
  have hdescent : baseEnd_1074701 < baseStart_1074701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074849 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1074849 : Nat := 118140960795 + 1074849 * 2 ^ 59
def prefixEnd_1074849 : Nat := 4983230072969 + 3 ^ 40 * 1074849 * 2
def baseEnd_1074849 : Nat := 367942778669713588029577

theorem tailTrace_1074849 : CollatzResearch.WordTrace tailWord_1074849 prefixEnd_1074849 367942778669713588029577 := by
  unfold tailWord_1074849
  simp only [CollatzResearch.WordTrace]
  refine ⟨39202963683013117439587601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26135309122008744959725067 39202963683013117439587601)
  ·
    refine ⟨29402222762259838079690701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39202963683013117439587601 29402222762259838079690701)
    ·
      refine ⟨11025833535847439279884013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29402222762259838079690701 11025833535847439279884013)
      ·
        refine ⟨4134687575942789729956505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11025833535847439279884013 4134687575942789729956505)
        ·
          refine ⟨3101015681957092297467379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4134687575942789729956505 3101015681957092297467379)
          ·
            refine ⟨4651523522935638446201069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3101015681957092297467379 4651523522935638446201069)
            ·
              refine ⟨1744321321100864417325401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4651523522935638446201069 1744321321100864417325401)
              ·
                refine ⟨1308240990825648312994051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744321321100864417325401 1308240990825648312994051)
                ·
                  refine ⟨1962361486238472469491077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308240990825648312994051 1962361486238472469491077)
                  ·
                    refine ⟨367942778669713588029577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962361486238472469491077 367942778669713588029577)
                    ·
                      rfl

theorem cell22_1074849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1074849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074849 prefixEnd_1074849 := by exact prefixLift 1074849
  have htrace : WordTrace (prefixWord ++ tailWord_1074849) baseStart_1074849 baseEnd_1074849 := by
    simpa [prefixWord, tailWord_1074849, baseEnd_1074849] using wordTrace_append hprefix tailTrace_1074849
  have hstable : (prefixWord ++ tailWord_1074849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074849).length < 2 ^ (prefixWord ++ tailWord_1074849).sum := by decide
  have hdescent : baseEnd_1074849 < baseStart_1074849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074877 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1074877 : Nat := 118140960795 + 1074877 * 2 ^ 59
def prefixEnd_1074877 : Nat := 4983230072969 + 3 ^ 40 * 1074877 * 2
def baseEnd_1074877 : Nat := 367952363641930848329491

theorem tailTrace_1074877 : CollatzResearch.WordTrace tailWord_1074877 prefixEnd_1074877 367952363641930848329491 := by
  unfold tailWord_1074877
  simp only [CollatzResearch.WordTrace]
  refine ⟨39203984926911678221606885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26135989951274452147737923 39203984926911678221606885)
  ·
    refine ⟨7350747173795939666551291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39203984926911678221606885 7350747173795939666551291)
    ·
      refine ⟨11026120760693909499826937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7350747173795939666551291 11026120760693909499826937)
      ·
        refine ⟨8269590570520432124870203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11026120760693909499826937 8269590570520432124870203)
        ·
          refine ⟨12404385855780648187305305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8269590570520432124870203 12404385855780648187305305)
          ·
            refine ⟨9303289391835486140478979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12404385855780648187305305 9303289391835486140478979)
            ·
              refine ⟨13954934087753229210718469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9303289391835486140478979 13954934087753229210718469)
              ·
                refine ⟨2616550141453730477009713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13954934087753229210718469 2616550141453730477009713)
                ·
                  refine ⟨1962412606090297857757285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616550141453730477009713 1962412606090297857757285)
                  ·
                    refine ⟨367952363641930848329491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962412606090297857757285 367952363641930848329491)
                    ·
                      rfl

theorem cell22_1074877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1074877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074877 prefixEnd_1074877 := by exact prefixLift 1074877
  have htrace : WordTrace (prefixWord ++ tailWord_1074877) baseStart_1074877 baseEnd_1074877 := by
    simpa [prefixWord, tailWord_1074877, baseEnd_1074877] using wordTrace_append hprefix tailTrace_1074877
  have hstable : (prefixWord ++ tailWord_1074877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074877).length < 2 ^ (prefixWord ++ tailWord_1074877).sum := by decide
  have hdescent : baseEnd_1074877 < baseStart_1074877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074879 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 2, 3]
def baseStart_1074879 : Nat := 118140960795 + 1074879 * 2 ^ 59
def prefixEnd_1074879 : Nat := 4983230072969 + 3 ^ 40 * 1074879 * 2
def baseEnd_1074879 : Nat := 367953048282803509779485

theorem tailTrace_1074879 : CollatzResearch.WordTrace tailWord_1074879 prefixEnd_1074879 367953048282803509779485 := by
  unfold tailWord_1074879
  simp only [CollatzResearch.WordTrace]
  refine ⟨39204057872904432563179691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26136038581936288375453127 39204057872904432563179691)
  ·
    refine ⟨58806086809356648844769537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39204057872904432563179691 58806086809356648844769537)
    ·
      refine ⟨44104565107017486633577153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58806086809356648844769537 44104565107017486633577153)
      ·
        refine ⟨33078423830263114975182865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44104565107017486633577153 33078423830263114975182865)
        ·
          refine ⟨24808817872697336231387149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33078423830263114975182865 24808817872697336231387149)
          ·
            refine ⟨9303306702261501086770181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24808817872697336231387149 9303306702261501086770181)
            ·
              refine ⟨1744370006674031453769409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9303306702261501086770181 1744370006674031453769409)
              ·
                refine ⟨1308277505005523590327057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744370006674031453769409 1308277505005523590327057)
                ·
                  refine ⟨981208128754142692745293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1308277505005523590327057 981208128754142692745293)
                  ·
                    refine ⟨367953048282803509779485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981208128754142692745293 367953048282803509779485)
                    ·
                      rfl

theorem cell22_1074879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_1074879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074879 prefixEnd_1074879 := by exact prefixLift 1074879
  have htrace : WordTrace (prefixWord ++ tailWord_1074879) baseStart_1074879 baseEnd_1074879 := by
    simpa [prefixWord, tailWord_1074879, baseEnd_1074879] using wordTrace_append hprefix tailTrace_1074879
  have hstable : (prefixWord ++ tailWord_1074879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074879).length < 2 ^ (prefixWord ++ tailWord_1074879).sum := by decide
  have hdescent : baseEnd_1074879 < baseStart_1074879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074952 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1074952 : Nat := 118140960795 + 1074952 * 2 ^ 59
def prefixEnd_1074952 : Nat := 4983230072969 + 3 ^ 40 * 1074952 * 2
def baseEnd_1074952 : Nat := 367978037674655652704261

theorem tailTrace_1074952 : CollatzResearch.WordTrace tailWord_1074952 prefixEnd_1074952 367978037674655652704261 := by
  unfold tailWord_1074952
  simp only [CollatzResearch.WordTrace]
  refine ⟨19603360200819983015293555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26137813601093310687058073 19603360200819983015293555)
  ·
    refine ⟨29405040301229974522940333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19603360200819983015293555 29405040301229974522940333)
    ·
      refine ⟨11026890112961240446102625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29405040301229974522940333 11026890112961240446102625)
      ·
        refine ⟨8270167584720930334576969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11026890112961240446102625 8270167584720930334576969)
        ·
          refine ⟨6202625688540697750932727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8270167584720930334576969 6202625688540697750932727)
          ·
            refine ⟨9303938532811046626399091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6202625688540697750932727 9303938532811046626399091)
            ·
              refine ⟨13955907799216569939598637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9303938532811046626399091 13955907799216569939598637)
              ·
                refine ⟨5233465424706213727349489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13955907799216569939598637 5233465424706213727349489)
                ·
                  refine ⟨3925099068529660295512117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5233465424706213727349489 3925099068529660295512117)
                  ·
                    refine ⟨367978037674655652704261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3925099068529660295512117 367978037674655652704261)
                    ·
                      rfl

theorem cell22_1074952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1074952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1074952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1074952 prefixEnd_1074952 := by exact prefixLift 1074952
  have htrace : WordTrace (prefixWord ++ tailWord_1074952) baseStart_1074952 baseEnd_1074952 := by
    simpa [prefixWord, tailWord_1074952, baseEnd_1074952] using wordTrace_append hprefix tailTrace_1074952
  have hstable : (prefixWord ++ tailWord_1074952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074952).length < 2 ^ (prefixWord ++ tailWord_1074952).sum := by decide
  have hdescent : baseEnd_1074952 < baseStart_1074952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075029 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1075029 : Nat := 118140960795 + 1075029 * 2 ^ 59
def prefixEnd_1075029 : Nat := 4983230072969 + 3 ^ 40 * 1075029 * 2
def baseEnd_1075029 : Nat := 368004396348253118529025

theorem tailTrace_1075029 : CollatzResearch.WordTrace tailWord_1075029 prefixEnd_1075029 368004396348253118529025 := by
  unfold tailWord_1075029
  simp only [CollatzResearch.WordTrace]
  refine ⟨39209528822361008181140141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26139685881574005454093427 39209528822361008181140141)
  ·
    refine ⟨14703573308385378067927553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39209528822361008181140141 14703573308385378067927553)
    ·
      refine ⟨11027679981289033550945665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14703573308385378067927553 11027679981289033550945665)
      ·
        refine ⟨8270759985966775163209249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11027679981289033550945665 8270759985966775163209249)
        ·
          refine ⟨6203069989475081372406937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8270759985966775163209249 6203069989475081372406937)
          ·
            refine ⟨4652302492106311029305203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6203069989475081372406937 4652302492106311029305203)
            ·
              refine ⟨6978453738159466543957805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652302492106311029305203 6978453738159466543957805)
              ·
                refine ⟨2616920151809799953984177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6978453738159466543957805 2616920151809799953984177)
                ·
                  refine ⟨1962690113857349965488133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616920151809799953984177 1962690113857349965488133)
                  ·
                    refine ⟨368004396348253118529025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962690113857349965488133 368004396348253118529025)
                    ·
                      rfl

theorem cell22_1075029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1075029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075029 prefixEnd_1075029 := by exact prefixLift 1075029
  have htrace : WordTrace (prefixWord ++ tailWord_1075029) baseStart_1075029 baseEnd_1075029 := by
    simpa [prefixWord, tailWord_1075029, baseEnd_1075029] using wordTrace_append hprefix tailTrace_1075029
  have hstable : (prefixWord ++ tailWord_1075029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075029).length < 2 ^ (prefixWord ++ tailWord_1075029).sum := by decide
  have hdescent : baseEnd_1075029 < baseStart_1075029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075044 : List Nat := [2, 3, 1, 1, 6, 9]
def baseStart_1075044 : Nat := 118140960795 + 1075044 * 2 ^ 59
def prefixEnd_1075044 : Nat := 4983230072969 + 3 ^ 40 * 1075044 * 2
def baseEnd_1075044 : Nat := 4543327545120963943259

theorem tailTrace_1075044 : CollatzResearch.WordTrace tailWord_1075044 prefixEnd_1075044 4543327545120963943259 := by
  unfold tailWord_1075044
  simp only [CollatzResearch.WordTrace]
  refine ⟨19605037958653332871468093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26140050611537777161957457 19605037958653332871468093)
  ·
    refine ⟨7351889234494999826800535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19605037958653332871468093 7351889234494999826800535)
    ·
      refine ⟨11027833851742499740200803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7351889234494999826800535 11027833851742499740200803)
      ·
        refine ⟨16541750777613749610301205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11027833851742499740200803 16541750777613749610301205)
        ·
          refine ⟨775394567700644512982869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16541750777613749610301205 775394567700644512982869)
          ·
            refine ⟨4543327545120963943259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 775394567700644512982869 4543327545120963943259)
            ·
              rfl

theorem cell22_1075044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 9].length) (baseStart_1075044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075044 prefixEnd_1075044 := by exact prefixLift 1075044
  have htrace : WordTrace (prefixWord ++ tailWord_1075044) baseStart_1075044 baseEnd_1075044 := by
    simpa [prefixWord, tailWord_1075044, baseEnd_1075044] using wordTrace_append hprefix tailTrace_1075044
  have hstable : (prefixWord ++ tailWord_1075044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075044).length < 2 ^ (prefixWord ++ tailWord_1075044).sum := by decide
  have hdescent : baseEnd_1075044 < baseStart_1075044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075057 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_1075057 : Nat := 118140960795 + 1075057 * 2 ^ 59
def prefixEnd_1075057 : Nat := 4983230072969 + 3 ^ 40 * 1075057 * 2
def baseEnd_1075057 : Nat := 368013981320470378828939

theorem tailTrace_1075057 : CollatzResearch.WordTrace tailWord_1075057 prefixEnd_1075057 368013981320470378828939 := by
  unfold tailWord_1075057
  simp only [CollatzResearch.WordTrace]
  refine ⟨39210550066259568963159425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26140366710839712642106283 39210550066259568963159425)
  ·
    refine ⟨29407912549694676722369569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39210550066259568963159425 29407912549694676722369569)
    ·
      refine ⟨22055934412271007541777177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29407912549694676722369569 22055934412271007541777177)
      ·
        refine ⟨16541950809203255656332883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22055934412271007541777177 16541950809203255656332883)
        ·
          refine ⟨24812926213804883484499325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16541950809203255656332883 24812926213804883484499325)
          ·
            refine ⟨9304847330176831306687247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24812926213804883484499325 9304847330176831306687247)
            ·
              refine ⟨13957270995265246960030871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9304847330176831306687247 13957270995265246960030871)
              ·
                refine ⟨20935906492897870440046307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13957270995265246960030871 20935906492897870440046307)
                ·
                  refine ⟨31403859739346805660069461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20935906492897870440046307 31403859739346805660069461)
                  ·
                    refine ⟨368013981320470378828939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31403859739346805660069461 368013981320470378828939)
                    ·
                      rfl

theorem cell22_1075057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_1075057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075057 prefixEnd_1075057 := by exact prefixLift 1075057
  have htrace : WordTrace (prefixWord ++ tailWord_1075057) baseStart_1075057 baseEnd_1075057 := by
    simpa [prefixWord, tailWord_1075057, baseEnd_1075057] using wordTrace_append hprefix tailTrace_1075057
  have hstable : (prefixWord ++ tailWord_1075057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075057).length < 2 ^ (prefixWord ++ tailWord_1075057).sum := by decide
  have hdescent : baseEnd_1075057 < baseStart_1075057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075059 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 3, 3]
def baseStart_1075059 : Nat := 118140960795 + 1075059 * 2 ^ 59
def prefixEnd_1075059 : Nat := 4983230072969 + 3 ^ 40 * 1075059 * 2
def baseEnd_1075059 : Nat := 368014665961343040278933

theorem tailTrace_1075059 : CollatzResearch.WordTrace tailWord_1075059 prefixEnd_1075059 368014665961343040278933 := by
  unfold tailWord_1075059
  simp only [CollatzResearch.WordTrace]
  refine ⟨39210623012252323304732231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26140415341501548869821487 39210623012252323304732231)
  ·
    refine ⟨58815934518378484957098347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39210623012252323304732231 58815934518378484957098347)
    ·
      refine ⟨88223901777567727435647521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58815934518378484957098347 88223901777567727435647521)
      ·
        refine ⟨66167926333175795576735641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88223901777567727435647521 66167926333175795576735641)
        ·
          refine ⟨49625944749881846682551731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66167926333175795576735641 49625944749881846682551731)
          ·
            refine ⟨74438917124822770023827597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49625944749881846682551731 74438917124822770023827597)
            ·
              refine ⟨27914593921808538758935349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74438917124822770023827597 27914593921808538758935349)
              ·
                refine ⟨2616993180169550508650189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27914593921808538758935349 2616993180169550508650189)
                ·
                  refine ⟨981372442563581440743821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2616993180169550508650189 981372442563581440743821)
                  ·
                    refine ⟨368014665961343040278933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981372442563581440743821 368014665961343040278933)
                    ·
                      rfl

theorem cell22_1075059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 3].length) (baseStart_1075059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075059 prefixEnd_1075059 := by exact prefixLift 1075059
  have htrace : WordTrace (prefixWord ++ tailWord_1075059) baseStart_1075059 baseEnd_1075059 := by
    simpa [prefixWord, tailWord_1075059, baseEnd_1075059] using wordTrace_append hprefix tailTrace_1075059
  have hstable : (prefixWord ++ tailWord_1075059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075059).length < 2 ^ (prefixWord ++ tailWord_1075059).sum := by decide
  have hdescent : baseEnd_1075059 < baseStart_1075059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075093 : List Nat := [1, 3, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_1075093 : Nat := 118140960795 + 1075093 * 2 ^ 59
def prefixEnd_1075093 : Nat := 4983230072969 + 3 ^ 40 * 1075093 * 2
def baseEnd_1075093 : Nat := 368026304856178284928829

theorem tailTrace_1075093 : CollatzResearch.WordTrace tailWord_1075093 prefixEnd_1075093 368026304856178284928829 := by
  unfold tailWord_1075093
  simp only [CollatzResearch.WordTrace]
  refine ⟨39211863094129147111469933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26141242062752764740979955 39211863094129147111469933)
  ·
    refine ⟨14704448660298430166801225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39211863094129147111469933 14704448660298430166801225)
    ·
      refine ⟨11028336495223822625100919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14704448660298430166801225 11028336495223822625100919)
      ·
        refine ⟨16542504742835733937651379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11028336495223822625100919 16542504742835733937651379)
        ·
          refine ⟨24813757114253600906477069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16542504742835733937651379 24813757114253600906477069)
          ·
            refine ⟨9305158917845100339928901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24813757114253600906477069 9305158917845100339928901)
            ·
              refine ⟨1744717297095956313736669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9305158917845100339928901 1744717297095956313736669)
              ·
                refine ⟨654268986410983617651251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1744717297095956313736669 654268986410983617651251)
                ·
                  refine ⟨981403479616475426476877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654268986410983617651251 981403479616475426476877)
                  ·
                    refine ⟨368026304856178284928829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981403479616475426476877 368026304856178284928829)
                    ·
                      rfl

theorem cell22_1075093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_1075093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075093 prefixEnd_1075093 := by exact prefixLift 1075093
  have htrace : WordTrace (prefixWord ++ tailWord_1075093) baseStart_1075093 baseEnd_1075093 := by
    simpa [prefixWord, tailWord_1075093, baseEnd_1075093] using wordTrace_append hprefix tailTrace_1075093
  have hstable : (prefixWord ++ tailWord_1075093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075093).length < 2 ^ (prefixWord ++ tailWord_1075093).sum := by decide
  have hdescent : baseEnd_1075093 < baseStart_1075093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075106 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1075106 : Nat := 118140960795 + 1075106 * 2 ^ 59
def prefixEnd_1075106 : Nat := 4983230072969 + 3 ^ 40 * 1075106 * 2
def baseEnd_1075106 : Nat := 122676918340616861451263

theorem tailTrace_1075106 : CollatzResearch.WordTrace tailWord_1075106 prefixEnd_1075106 122676918340616861451263 := by
  unfold tailWord_1075106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9803084310770512582923293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26141558162054700221128781 9803084310770512582923293)
  ·
    refine ⟨3676156616538942218596235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9803084310770512582923293 3676156616538942218596235)
    ·
      refine ⟨5514234924808413327894353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3676156616538942218596235 5514234924808413327894353)
      ·
        refine ⟨4135676193606309995920765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5514234924808413327894353 4135676193606309995920765)
        ·
          refine ⟨1550878572602366248470287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4135676193606309995920765 1550878572602366248470287)
          ·
            refine ⟨2326317858903549372705431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550878572602366248470287 2326317858903549372705431)
            ·
              refine ⟨3489476788355324059058147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326317858903549372705431 3489476788355324059058147)
              ·
                refine ⟨5234215182532986088587221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489476788355324059058147 5234215182532986088587221)
                ·
                  refine ⟨122676918340616861451263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5234215182532986088587221 122676918340616861451263)
                  ·
                    rfl

theorem cell22_1075106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1075106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075106 prefixEnd_1075106 := by exact prefixLift 1075106
  have htrace : WordTrace (prefixWord ++ tailWord_1075106) baseStart_1075106 baseEnd_1075106 := by
    simpa [prefixWord, tailWord_1075106, baseEnd_1075106] using wordTrace_append hprefix tailTrace_1075106
  have hstable : (prefixWord ++ tailWord_1075106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075106).length < 2 ^ (prefixWord ++ tailWord_1075106).sum := by decide
  have hdescent : baseEnd_1075106 < baseStart_1075106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075136 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_1075136 : Nat := 118140960795 + 1075136 * 2 ^ 59
def prefixEnd_1075136 : Nat := 4983230072969 + 3 ^ 40 * 1075136 * 2
def baseEnd_1075136 : Nat := 368041024634940506103697

theorem tailTrace_1075136 : CollatzResearch.WordTrace tailWord_1075136 prefixEnd_1075136 368041024634940506103697 := by
  unfold tailWord_1075136
  simp only [CollatzResearch.WordTrace]
  refine ⟨19606715716486682727642631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26142287621982243636856841 19606715716486682727642631)
  ·
    refine ⟨29410073574730024091463947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19606715716486682727642631 29410073574730024091463947)
    ·
      refine ⟨44115110362095036137195921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29410073574730024091463947 44115110362095036137195921)
      ·
        refine ⟨33086332771571277102896941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44115110362095036137195921 33086332771571277102896941)
        ·
          refine ⟨12407374789339228913586353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33086332771571277102896941 12407374789339228913586353)
          ·
            refine ⟨9305531092004421685189765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12407374789339228913586353 9305531092004421685189765)
            ·
              refine ⟨1744787079750829065973081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9305531092004421685189765 1744787079750829065973081)
              ·
                refine ⟨1308590309813121799479811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744787079750829065973081 1308590309813121799479811)
                ·
                  refine ⟨1962885464719682699219717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308590309813121799479811 1962885464719682699219717)
                  ·
                    refine ⟨368041024634940506103697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962885464719682699219717 368041024634940506103697)
                    ·
                      rfl

theorem cell22_1075136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_1075136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075136 prefixEnd_1075136 := by exact prefixLift 1075136
  have htrace : WordTrace (prefixWord ++ tailWord_1075136) baseStart_1075136 baseEnd_1075136 := by
    simpa [prefixWord, tailWord_1075136, baseEnd_1075136] using wordTrace_append hprefix tailTrace_1075136
  have hstable : (prefixWord ++ tailWord_1075136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075136).length < 2 ^ (prefixWord ++ tailWord_1075136).sum := by decide
  have hdescent : baseEnd_1075136 < baseStart_1075136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075198 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1075198 : Nat := 118140960795 + 1075198 * 2 ^ 59
def prefixEnd_1075198 : Nat := 4983230072969 + 3 ^ 40 * 1075198 * 2
def baseEnd_1075198 : Nat := 368062248501993011053507

theorem tailTrace_1075198 : CollatzResearch.WordTrace tailWord_1075198 prefixEnd_1075198 368062248501993011053507 := by
  unfold tailWord_1075198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901961594843593755505281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26143795172499166696028165 4901961594843593755505281)
  ·
    refine ⟨3676471196132695316628961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4901961594843593755505281 3676471196132695316628961)
    ·
      refine ⟨2757353397099521487471721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3676471196132695316628961 2757353397099521487471721)
      ·
        refine ⟨2068015047824641115603791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2757353397099521487471721 2068015047824641115603791)
        ·
          refine ⟨3102022571736961673405687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068015047824641115603791 3102022571736961673405687)
          ·
            refine ⟨4653033857605442510108531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102022571736961673405687 4653033857605442510108531)
            ·
              refine ⟨6979550786408163765162797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4653033857605442510108531 6979550786408163765162797)
              ·
                refine ⟨2617331544903061411936049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6979550786408163765162797 2617331544903061411936049)
                ·
                  refine ⟨1962998658677296058952037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2617331544903061411936049 1962998658677296058952037)
                  ·
                    refine ⟨368062248501993011053507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962998658677296058952037 368062248501993011053507)
                    ·
                      rfl

theorem cell22_1075198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1075198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075198 prefixEnd_1075198 := by exact prefixLift 1075198
  have htrace : WordTrace (prefixWord ++ tailWord_1075198) baseStart_1075198 baseEnd_1075198 := by
    simpa [prefixWord, tailWord_1075198, baseEnd_1075198] using wordTrace_append hprefix tailTrace_1075198
  have hstable : (prefixWord ++ tailWord_1075198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075198).length < 2 ^ (prefixWord ++ tailWord_1075198).sum := by decide
  have hdescent : baseEnd_1075198 < baseStart_1075198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075213 : List Nat := [1, 7, 1, 2, 11]
def baseStart_1075213 : Nat := 118140960795 + 1075213 * 2 ^ 59
def prefixEnd_1075213 : Nat := 4983230072969 + 3 ^ 40 * 1075213 * 2
def baseEnd_1075213 : Nat := 1514680589747069843327

theorem tailTrace_1075213 : CollatzResearch.WordTrace tailWord_1075213 prefixEnd_1075213 1514680589747069843327 := by
  unfold tailWord_1075213
  simp only [CollatzResearch.WordTrace]
  refine ⟨39216239853694407605838293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26144159902462938403892195 39216239853694407605838293)
  ·
    refine ⟨919130621570962678261835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39216239853694407605838293 919130621570962678261835)
    ·
      refine ⟨1378695932356444017392753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919130621570962678261835 1378695932356444017392753)
      ·
        refine ⟨1034021949267333013044565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1378695932356444017392753 1034021949267333013044565)
        ·
          refine ⟨1514680589747069843327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1034021949267333013044565 1514680589747069843327)
          ·
            rfl

theorem cell22_1075213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 11].length) (baseStart_1075213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075213 prefixEnd_1075213 := by exact prefixLift 1075213
  have htrace : WordTrace (prefixWord ++ tailWord_1075213) baseStart_1075213 baseEnd_1075213 := by
    simpa [prefixWord, tailWord_1075213, baseEnd_1075213] using wordTrace_append hprefix tailTrace_1075213
  have hstable : (prefixWord ++ tailWord_1075213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075213).length < 2 ^ (prefixWord ++ tailWord_1075213).sum := by decide
  have hdescent : baseEnd_1075213 < baseStart_1075213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075269 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 10]
def baseStart_1075269 : Nat := 118140960795 + 1075269 * 2 ^ 59
def prefixEnd_1075269 : Nat := 4983230072969 + 3 ^ 40 * 1075269 * 2
def baseEnd_1075269 : Nat := 122695517750990830842763

theorem tailTrace_1075269 : CollatzResearch.WordTrace tailWord_1075269 prefixEnd_1075269 122695517750990830842763 := by
  unfold tailWord_1075269
  simp only [CollatzResearch.WordTrace]
  refine ⟨39218282341491529169876861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26145521560994352779917907 39218282341491529169876861)
  ·
    refine ⟨14706855878059323438703823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39218282341491529169876861 14706855878059323438703823)
    ·
      refine ⟨22060283817088985158055735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14706855878059323438703823 22060283817088985158055735)
      ·
        refine ⟨33090425725633477737083603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22060283817088985158055735 33090425725633477737083603)
        ·
          refine ⟨49635638588450216605625405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33090425725633477737083603 49635638588450216605625405)
          ·
            refine ⟨18613364470668831227109527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49635638588450216605625405 18613364470668831227109527)
            ·
              refine ⟨27920046706003246840664291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18613364470668831227109527 27920046706003246840664291)
              ·
                refine ⟨41880070059004870260996437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27920046706003246840664291 41880070059004870260996437)
                ·
                  refine ⟨122695517750990830842763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41880070059004870260996437 122695517750990830842763)
                  ·
                    rfl

theorem cell22_1075269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_1075269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075269 prefixEnd_1075269 := by exact prefixLift 1075269
  have htrace : WordTrace (prefixWord ++ tailWord_1075269) baseStart_1075269 baseEnd_1075269 := by
    simpa [prefixWord, tailWord_1075269, baseEnd_1075269] using wordTrace_append hprefix tailTrace_1075269
  have hstable : (prefixWord ++ tailWord_1075269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075269).length < 2 ^ (prefixWord ++ tailWord_1075269).sum := by decide
  have hdescent : baseEnd_1075269 < baseStart_1075269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075331 : List Nat := [1, 1, 1, 3, 3, 5, 8]
def baseStart_1075331 : Nat := 118140960795 + 1075331 * 2 ^ 59
def prefixEnd_1075331 : Nat := 4983230072969 + 3 ^ 40 * 1075331 * 2
def baseEnd_1075331 : Nat := 13633621374815740647337

theorem tailTrace_1075331 : CollatzResearch.WordTrace tailWord_1075331 prefixEnd_1075331 13633621374815740647337 := by
  unfold tailWord_1075331
  simp only [CollatzResearch.WordTrace]
  refine ⟨39220543667266913758633847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26147029111511275839089231 39220543667266913758633847)
  ·
    refine ⟨58830815500900370637950771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39220543667266913758633847 58830815500900370637950771)
    ·
      refine ⟨88246223251350555956926157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58830815500900370637950771 88246223251350555956926157)
      ·
        refine ⟨33092333719256458483847309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88246223251350555956926157 33092333719256458483847309)
        ·
          refine ⟨12409625144721171931442741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33092333719256458483847309 12409625144721171931442741)
          ·
            refine ⟨1163402357317609868572757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12409625144721171931442741 1163402357317609868572757)
            ·
              refine ⟨13633621374815740647337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1163402357317609868572757 13633621374815740647337)
              ·
                rfl

theorem cell22_1075331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 8].length) (baseStart_1075331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075331 prefixEnd_1075331 := by exact prefixLift 1075331
  have htrace : WordTrace (prefixWord ++ tailWord_1075331) baseStart_1075331 baseEnd_1075331 := by
    simpa [prefixWord, tailWord_1075331, baseEnd_1075331] using wordTrace_append hprefix tailTrace_1075331
  have hstable : (prefixWord ++ tailWord_1075331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075331).length < 2 ^ (prefixWord ++ tailWord_1075331).sum := by decide
  have hdescent : baseEnd_1075331 < baseStart_1075331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075333 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1075333 : Nat := 118140960795 + 1075333 * 2 ^ 59
def prefixEnd_1075333 : Nat := 4983230072969 + 3 ^ 40 * 1075333 * 2
def baseEnd_1075333 : Nat := 368108461760897658928093

theorem tailTrace_1075333 : CollatzResearch.WordTrace tailWord_1075333 prefixEnd_1075333 368108461760897658928093 := by
  unfold tailWord_1075333
  simp only [CollatzResearch.WordTrace]
  refine ⟨39220616613259668100206653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26147077742173112066804435 39220616613259668100206653)
  ·
    refine ⟨14707731229972375537577495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39220616613259668100206653 14707731229972375537577495)
    ·
      refine ⟨22061596844958563306366243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14707731229972375537577495 22061596844958563306366243)
      ·
        refine ⟨33092395267437844959549365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22061596844958563306366243 33092395267437844959549365)
        ·
          refine ⟨3102412056322297964957753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33092395267437844959549365 3102412056322297964957753)
          ·
            refine ⟨2326809042241723473718315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3102412056322297964957753 2326809042241723473718315)
            ·
              refine ⟨3490213563362585210577473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326809042241723473718315 3490213563362585210577473)
              ·
                refine ⟨2617660172521938907933105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490213563362585210577473 2617660172521938907933105)
                ·
                  refine ⟨1963245129391454180949829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2617660172521938907933105 1963245129391454180949829)
                  ·
                    refine ⟨368108461760897658928093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1963245129391454180949829 368108461760897658928093)
                    ·
                      rfl

theorem cell22_1075333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1075333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075333 prefixEnd_1075333 := by exact prefixLift 1075333
  have htrace : WordTrace (prefixWord ++ tailWord_1075333) baseStart_1075333 baseEnd_1075333 := by
    simpa [prefixWord, tailWord_1075333, baseEnd_1075333] using wordTrace_append hprefix tailTrace_1075333
  have hstable : (prefixWord ++ tailWord_1075333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075333).length < 2 ^ (prefixWord ++ tailWord_1075333).sum := by decide
  have hdescent : baseEnd_1075333 < baseStart_1075333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075391 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 2, 5]
def baseStart_1075391 : Nat := 118140960795 + 1075391 * 2 ^ 59
def prefixEnd_1075391 : Nat := 4983230072969 + 3 ^ 40 * 1075391 * 2
def baseEnd_1075391 : Nat := 368128316346204840977915

theorem tailTrace_1075391 : CollatzResearch.WordTrace tailWord_1075391 prefixEnd_1075391 368128316346204840977915 := by
  unfold tailWord_1075391
  simp only [CollatzResearch.WordTrace]
  refine ⟨39222732047049544005818027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26148488031366362670545351 39222732047049544005818027)
  ·
    refine ⟨58834098070574316008727041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39222732047049544005818027 58834098070574316008727041)
    ·
      refine ⟨44125573552930737006545281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58834098070574316008727041 44125573552930737006545281)
      ·
        refine ⟨33094180164698052754908961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44125573552930737006545281 33094180164698052754908961)
        ·
          refine ⟨24820635123523539566181721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33094180164698052754908961 24820635123523539566181721)
          ·
            refine ⟨18615476342642654674636291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24820635123523539566181721 18615476342642654674636291)
            ·
              refine ⟨27923214513963982011954437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18615476342642654674636291 27923214513963982011954437)
              ·
                refine ⟨5235602721368246627241457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27923214513963982011954437 5235602721368246627241457)
                ·
                  refine ⟨3926702041026184970431093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5235602721368246627241457 3926702041026184970431093)
                  ·
                    refine ⟨368128316346204840977915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3926702041026184970431093 368128316346204840977915)
                    ·
                      rfl

theorem cell22_1075391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_1075391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075391 prefixEnd_1075391 := by exact prefixLift 1075391
  have htrace : WordTrace (prefixWord ++ tailWord_1075391) baseStart_1075391 baseEnd_1075391 := by
    simpa [prefixWord, tailWord_1075391, baseEnd_1075391] using wordTrace_append hprefix tailTrace_1075391
  have hstable : (prefixWord ++ tailWord_1075391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075391).length < 2 ^ (prefixWord ++ tailWord_1075391).sum := by decide
  have hdescent : baseEnd_1075391 < baseStart_1075391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075397 : List Nat := [1, 3, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_1075397 : Nat := 118140960795 + 1075397 * 2 ^ 59
def prefixEnd_1075397 : Nat := 4983230072969 + 3 ^ 40 * 1075397 * 2
def baseEnd_1075397 : Nat := 368130370268822825327897

theorem tailTrace_1075397 : CollatzResearch.WordTrace tailWord_1075397 prefixEnd_1075397 368130370268822825327897 := by
  unfold tailWord_1075397
  simp only [CollatzResearch.WordTrace]
  refine ⟨39222950885027807030536445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26148633923351871353690963 39222950885027807030536445)
  ·
    refine ⟨14708606581885427636451167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39222950885027807030536445 14708606581885427636451167)
    ·
      refine ⟨22062909872828141454676751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14708606581885427636451167 22062909872828141454676751)
      ·
        refine ⟨33094364809242212182015127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22062909872828141454676751 33094364809242212182015127)
        ·
          refine ⟨49641547213863318273022691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33094364809242212182015127 49641547213863318273022691)
          ·
            refine ⟨74462320820794977409534037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49641547213863318273022691 74462320820794977409534037)
            ·
              refine ⟨872605322118691141517977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 74462320820794977409534037 872605322118691141517977)
              ·
                refine ⟨654453991589018356138483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872605322118691141517977 654453991589018356138483)
                ·
                  refine ⟨981680987383527534207725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654453991589018356138483 981680987383527534207725)
                  ·
                    refine ⟨368130370268822825327897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981680987383527534207725 368130370268822825327897)
                    ·
                      rfl

theorem cell22_1075397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_1075397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075397 prefixEnd_1075397 := by exact prefixLift 1075397
  have htrace : WordTrace (prefixWord ++ tailWord_1075397) baseStart_1075397 baseEnd_1075397 := by
    simpa [prefixWord, tailWord_1075397, baseEnd_1075397] using wordTrace_append hprefix tailTrace_1075397
  have hstable : (prefixWord ++ tailWord_1075397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075397).length < 2 ^ (prefixWord ++ tailWord_1075397).sum := by decide
  have hdescent : baseEnd_1075397 < baseStart_1075397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075423 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 1, 4]
def baseStart_1075423 : Nat := 118140960795 + 1075423 * 2 ^ 59
def prefixEnd_1075423 : Nat := 4983230072969 + 3 ^ 40 * 1075423 * 2
def baseEnd_1075423 : Nat := 368139270600167424177817

theorem tailTrace_1075423 : CollatzResearch.WordTrace tailWord_1075423 prefixEnd_1075423 368139270600167424177817 := by
  unfold tailWord_1075423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39223899182933613470982923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26149266121955742313988615 39223899182933613470982923)
  ·
    refine ⟨58835848774400420206474385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39223899182933613470982923 58835848774400420206474385)
    ·
      refine ⟨44126886580800315154855789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58835848774400420206474385 44126886580800315154855789)
      ·
        refine ⟨16547582467800118183070921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44126886580800315154855789 16547582467800118183070921)
        ·
          refine ⟨12410686850850088637303191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16547582467800118183070921 12410686850850088637303191)
          ·
            refine ⟨18616030276275132955954787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12410686850850088637303191 18616030276275132955954787)
            ·
              refine ⟨27924045414412699433932181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18616030276275132955954787 27924045414412699433932181)
              ·
                refine ⟨1308939628800595285965571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27924045414412699433932181 1308939628800595285965571)
                ·
                  refine ⟨1963409443200892928948357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308939628800595285965571 1963409443200892928948357)
                  ·
                    refine ⟨368139270600167424177817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1963409443200892928948357 368139270600167424177817)
                    ·
                      rfl

theorem cell22_1075423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_1075423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075423 prefixEnd_1075423 := by exact prefixLift 1075423
  have htrace : WordTrace (prefixWord ++ tailWord_1075423) baseStart_1075423 baseEnd_1075423 := by
    simpa [prefixWord, tailWord_1075423, baseEnd_1075423] using wordTrace_append hprefix tailTrace_1075423
  have hstable : (prefixWord ++ tailWord_1075423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075423).length < 2 ^ (prefixWord ++ tailWord_1075423).sum := by decide
  have hdescent : baseEnd_1075423 < baseStart_1075423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075483 : List Nat := [1, 1, 1, 1, 1, 1, 10, 6]
def baseStart_1075483 : Nat := 118140960795 + 1075483 * 2 ^ 59
def prefixEnd_1075483 : Nat := 4983230072969 + 3 ^ 40 * 1075483 * 2
def baseEnd_1075483 : Nat := 40906645536260807519737

theorem tailTrace_1075483 : CollatzResearch.WordTrace tailWord_1075483 prefixEnd_1075483 40906645536260807519737 := by
  unfold tailWord_1075483
  simp only [CollatzResearch.WordTrace]
  refine ⟨39226087562716243718167103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26150725041810829145444735 39226087562716243718167103)
  ·
    refine ⟨58839131344074365577250655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39226087562716243718167103 58839131344074365577250655)
    ·
      refine ⟨88258697016111548365875983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58839131344074365577250655 88258697016111548365875983)
      ·
        refine ⟨132388045524167322548813975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88258697016111548365875983 132388045524167322548813975)
        ·
          refine ⟨198582068286250983823220963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132388045524167322548813975 198582068286250983823220963)
          ·
            refine ⟨297873102429376475734831445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198582068286250983823220963 297873102429376475734831445)
            ·
              refine ⟨872675104773563893754389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 297873102429376475734831445 872675104773563893754389)
              ·
                refine ⟨40906645536260807519737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 872675104773563893754389 40906645536260807519737)
                ·
                  rfl

theorem cell22_1075483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 6].length) (baseStart_1075483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075483 prefixEnd_1075483 := by exact prefixLift 1075483
  have htrace : WordTrace (prefixWord ++ tailWord_1075483) baseStart_1075483 baseEnd_1075483 := by
    simpa [prefixWord, tailWord_1075483, baseEnd_1075483] using wordTrace_append hprefix tailTrace_1075483
  have hstable : (prefixWord ++ tailWord_1075483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075483).length < 2 ^ (prefixWord ++ tailWord_1075483).sum := by decide
  have hdescent : baseEnd_1075483 < baseStart_1075483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075521 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1075521 : Nat := 118140960795 + 1075521 * 2 ^ 59
def prefixEnd_1075521 : Nat := 4983230072969 + 3 ^ 40 * 1075521 * 2
def baseEnd_1075521 : Nat := 368172818002927835227517

theorem tailTrace_1075521 : CollatzResearch.WordTrace tailWord_1075521 prefixEnd_1075521 368172818002927835227517 := by
  unfold tailWord_1075521
  simp only [CollatzResearch.WordTrace]
  refine ⟨39227473536578576208050417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26151649024385717472033611 39227473536578576208050417)
  ·
    refine ⟨29420605152433932156037813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39227473536578576208050417 29420605152433932156037813)
    ·
      refine ⟨2758181733040681139628545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29420605152433932156037813 2758181733040681139628545)
      ·
        refine ⟨2068636299780510854721409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2758181733040681139628545 2068636299780510854721409)
        ·
          refine ⟨1551477224835383141041057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068636299780510854721409 1551477224835383141041057)
          ·
            refine ⟨1163607918626537355780793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551477224835383141041057 1163607918626537355780793)
            ·
              refine ⟨872705938969903016835595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163607918626537355780793 872705938969903016835595)
              ·
                refine ⟨1309058908454854525253393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872705938969903016835595 1309058908454854525253393)
                ·
                  refine ⟨981794181341140893940045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1309058908454854525253393 981794181341140893940045)
                  ·
                    refine ⟨368172818002927835227517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981794181341140893940045 368172818002927835227517)
                    ·
                      rfl

theorem cell22_1075521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1075521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075521 prefixEnd_1075521 := by exact prefixLift 1075521
  have htrace : WordTrace (prefixWord ++ tailWord_1075521) baseStart_1075521 baseEnd_1075521 := by
    simpa [prefixWord, tailWord_1075521, baseEnd_1075521] using wordTrace_append hprefix tailTrace_1075521
  have hstable : (prefixWord ++ tailWord_1075521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075521).length < 2 ^ (prefixWord ++ tailWord_1075521).sum := by decide
  have hdescent : baseEnd_1075521 < baseStart_1075521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075562 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_1075562 : Nat := 118140960795 + 1075562 * 2 ^ 59
def prefixEnd_1075562 : Nat := 4983230072969 + 3 ^ 40 * 1075562 * 2
def baseEnd_1075562 : Nat := 122728951046939131650797

theorem tailTrace_1075562 : CollatzResearch.WordTrace tailWord_1075562 prefixEnd_1075562 122728951046939131650797 := by
  unfold tailWord_1075562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9807242232357510052573235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26152645952953360140195293 9807242232357510052573235)
  ·
    refine ⟨14710863348536265078859853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9807242232357510052573235 14710863348536265078859853)
    ·
      refine ⟨5516573755701099404572445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14710863348536265078859853 5516573755701099404572445)
      ·
        refine ⟨2068715158387912276714667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5516573755701099404572445 2068715158387912276714667)
        ·
          refine ⟨3103072737581868415072001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068715158387912276714667 3103072737581868415072001)
          ·
            refine ⟨2327304553186401311304001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3103072737581868415072001 2327304553186401311304001)
            ·
              refine ⟨1745478414889800983478001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2327304553186401311304001 1745478414889800983478001)
              ·
                refine ⟨1309108811167350737608501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745478414889800983478001 1309108811167350737608501)
                ·
                  refine ⟨122728951046939131650797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1309108811167350737608501 122728951046939131650797)
                  ·
                    rfl

theorem cell22_1075562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_1075562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075562 prefixEnd_1075562 := by exact prefixLift 1075562
  have htrace : WordTrace (prefixWord ++ tailWord_1075562) baseStart_1075562 baseEnd_1075562 := by
    simpa [prefixWord, tailWord_1075562, baseEnd_1075562] using wordTrace_append hprefix tailTrace_1075562
  have hstable : (prefixWord ++ tailWord_1075562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075562).length < 2 ^ (prefixWord ++ tailWord_1075562).sum := by decide
  have hdescent : baseEnd_1075562 < baseStart_1075562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075605 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_1075605 : Nat := 118140960795 + 1075605 * 2 ^ 59
def prefixEnd_1075605 : Nat := 4983230072969 + 3 ^ 40 * 1075605 * 2
def baseEnd_1075605 : Nat := 368201572919579616127259

theorem tailTrace_1075605 : CollatzResearch.WordTrace tailWord_1075605 prefixEnd_1075605 368201572919579616127259 := by
  unfold tailWord_1075605
  simp only [CollatzResearch.WordTrace]
  refine ⟨39230537268274258554108269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26153691512182839036072179 39230537268274258554108269)
  ·
    refine ⟨14711451475602846957790601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39230537268274258554108269 14711451475602846957790601)
    ·
      refine ⟨11033588606702135218342951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14711451475602846957790601 11033588606702135218342951)
      ·
        refine ⟨16550382910053202827514427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11033588606702135218342951 16550382910053202827514427)
        ·
          refine ⟨24825574365079804241271641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16550382910053202827514427 24825574365079804241271641)
          ·
            refine ⟨18619180773809853180953731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24825574365079804241271641 18619180773809853180953731)
            ·
              refine ⟨27928771160714779771430597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18619180773809853180953731 27928771160714779771430597)
              ·
                refine ⟨5236644592634021207143237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27928771160714779771430597 5236644592634021207143237)
                ·
                  refine ⟨981870861118878976339357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5236644592634021207143237 981870861118878976339357)
                  ·
                    refine ⟨368201572919579616127259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981870861118878976339357 368201572919579616127259)
                    ·
                      rfl

theorem cell22_1075605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_1075605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075605 prefixEnd_1075605 := by exact prefixLift 1075605
  have htrace : WordTrace (prefixWord ++ tailWord_1075605) baseStart_1075605 baseEnd_1075605 := by
    simpa [prefixWord, tailWord_1075605, baseEnd_1075605] using wordTrace_append hprefix tailTrace_1075605
  have hstable : (prefixWord ++ tailWord_1075605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075605).length < 2 ^ (prefixWord ++ tailWord_1075605).sum := by decide
  have hdescent : baseEnd_1075605 < baseStart_1075605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075620 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1075620 : Nat := 118140960795 + 1075620 * 2 ^ 59
def prefixEnd_1075620 : Nat := 4983230072969 + 3 ^ 40 * 1075620 * 2
def baseEnd_1075620 : Nat := 368206707726124577002213

theorem tailTrace_1075620 : CollatzResearch.WordTrace tailWord_1075620 prefixEnd_1075620 368206707726124577002213 := by
  unfold tailWord_1075620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19615542181609958057952157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26154056242146610743936209 19615542181609958057952157)
  ·
    refine ⟨7355828318103734271732059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19615542181609958057952157 7355828318103734271732059)
    ·
      refine ⟨11033742477155601407598089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7355828318103734271732059 11033742477155601407598089)
      ·
        refine ⟨8275306857866701055698567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11033742477155601407598089 8275306857866701055698567)
        ·
          refine ⟨12412960286800051583547851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8275306857866701055698567 12412960286800051583547851)
          ·
            refine ⟨18619440430200077375321777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12412960286800051583547851 18619440430200077375321777)
            ·
              refine ⟨13964580322650058031491333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18619440430200077375321777 13964580322650058031491333)
              ·
                refine ⟨2618358810496885880904625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13964580322650058031491333 2618358810496885880904625)
                ·
                  refine ⟨1963769107872664410678469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2618358810496885880904625 1963769107872664410678469)
                  ·
                    refine ⟨368206707726124577002213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1963769107872664410678469 368206707726124577002213)
                    ·
                      rfl

theorem cell22_1075620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1075620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075620 prefixEnd_1075620 := by exact prefixLift 1075620
  have htrace : WordTrace (prefixWord ++ tailWord_1075620) baseStart_1075620 baseEnd_1075620 := by
    simpa [prefixWord, tailWord_1075620, baseEnd_1075620] using wordTrace_append hprefix tailTrace_1075620
  have hstable : (prefixWord ++ tailWord_1075620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075620).length < 2 ^ (prefixWord ++ tailWord_1075620).sum := by decide
  have hdescent : baseEnd_1075620 < baseStart_1075620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075624 : List Nat := [2, 1, 6, 1, 1, 1, 2, 4, 4]
def baseStart_1075624 : Nat := 118140960795 + 1075624 * 2 ^ 59
def prefixEnd_1075624 : Nat := 4983230072969 + 3 ^ 40 * 1075624 * 2
def baseEnd_1075624 : Nat := 122736025669289966634067

theorem tailTrace_1075624 : CollatzResearch.WordTrace tailWord_1075624 prefixEnd_1075624 122736025669289966634067 := by
  unfold tailWord_1075624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19615615127602712399524963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26154153503470283199366617 19615615127602712399524963)
  ·
    refine ⟨29423422691404068599287445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19615615127602712399524963 29423422691404068599287445)
    ·
      refine ⟨1379222938659565715591599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29423422691404068599287445 1379222938659565715591599)
      ·
        refine ⟨2068834407989348573387399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379222938659565715591599 2068834407989348573387399)
        ·
          refine ⟨3103251611984022860081099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068834407989348573387399 3103251611984022860081099)
          ·
            refine ⟨4654877417976034290121649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103251611984022860081099 4654877417976034290121649)
            ·
              refine ⟨3491158063482025717591237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4654877417976034290121649 3491158063482025717591237)
              ·
                refine ⟨654592136902879822048357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3491158063482025717591237 654592136902879822048357)
                ·
                  refine ⟨122736025669289966634067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 654592136902879822048357 122736025669289966634067)
                  ·
                    rfl

theorem cell22_1075624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_1075624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075624 prefixEnd_1075624 := by exact prefixLift 1075624
  have htrace : WordTrace (prefixWord ++ tailWord_1075624) baseStart_1075624 baseEnd_1075624 := by
    simpa [prefixWord, tailWord_1075624, baseEnd_1075624] using wordTrace_append hprefix tailTrace_1075624
  have hstable : (prefixWord ++ tailWord_1075624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075624).length < 2 ^ (prefixWord ++ tailWord_1075624).sum := by decide
  have hdescent : baseEnd_1075624 < baseStart_1075624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075639 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 2, 3]
def baseStart_1075639 : Nat := 118140960795 + 1075639 * 2 ^ 59
def prefixEnd_1075639 : Nat := 4983230072969 + 3 ^ 40 * 1075639 * 2
def baseEnd_1075639 : Nat := 368213211814414860777155

theorem tailTrace_1075639 : CollatzResearch.WordTrace tailWord_1075639 prefixEnd_1075639 368213211814414860777155 := by
  unfold tailWord_1075639
  simp only [CollatzResearch.WordTrace]
  refine ⟨39231777350151082360845971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26154518233434054907230647 39231777350151082360845971)
  ·
    refine ⟨58847666025226623541268957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39231777350151082360845971 58847666025226623541268957)
    ·
      refine ⟨22067874759459983827975859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58847666025226623541268957 22067874759459983827975859)
      ·
        refine ⟨33101812139189975741963789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22067874759459983827975859 33101812139189975741963789)
        ·
          refine ⟨12413179552196240903236421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33101812139189975741963789 12413179552196240903236421)
          ·
            refine ⟨2327471166036795169356829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12413179552196240903236421 2327471166036795169356829)
            ·
              refine ⟨872801687263798188508811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2327471166036795169356829 872801687263798188508811)
              ·
                refine ⟨1309202530895697282763217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872801687263798188508811 1309202530895697282763217)
                ·
                  refine ⟨981901898171772962072413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1309202530895697282763217 981901898171772962072413)
                  ·
                    refine ⟨368213211814414860777155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981901898171772962072413 368213211814414860777155)
                    ·
                      rfl

theorem cell22_1075639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_1075639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075639 prefixEnd_1075639 := by exact prefixLift 1075639
  have htrace : WordTrace (prefixWord ++ tailWord_1075639) baseStart_1075639 baseEnd_1075639 := by
    simpa [prefixWord, tailWord_1075639, baseEnd_1075639] using wordTrace_append hprefix tailTrace_1075639
  have hstable : (prefixWord ++ tailWord_1075639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075639).length < 2 ^ (prefixWord ++ tailWord_1075639).sum := by decide
  have hdescent : baseEnd_1075639 < baseStart_1075639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075652 : List Nat := [2, 3, 3, 2, 2, 1, 1, 8]
def baseStart_1075652 : Nat := 118140960795 + 1075652 * 2 ^ 59
def prefixEnd_1075652 : Nat := 4983230072969 + 3 ^ 40 * 1075652 * 2
def baseEnd_1075652 : Nat := 40913073553343017800235

theorem tailTrace_1075652 : CollatzResearch.WordTrace tailWord_1075652 prefixEnd_1075652 40913073553343017800235 := by
  unfold tailWord_1075652
  simp only [CollatzResearch.WordTrace]
  refine ⟨19616125749551992790534605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26154834332735990387379473 19616125749551992790534605)
  ·
    refine ⟨7356047156081997296450477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19616125749551992790534605 7356047156081997296450477)
    ·
      refine ⟨2758517683530748986168929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7356047156081997296450477 2758517683530748986168929)
      ·
        refine ⟨2068888262648061739626697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2758517683530748986168929 2068888262648061739626697)
        ·
          refine ⟨1551666196986046304720023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068888262648061739626697 1551666196986046304720023)
          ·
            refine ⟨2327499295479069457080035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551666196986046304720023 2327499295479069457080035)
            ·
              refine ⟨3491248943218604185620053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327499295479069457080035 3491248943218604185620053)
              ·
                refine ⟨40913073553343017800235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3491248943218604185620053 40913073553343017800235)
                ·
                  rfl

theorem cell22_1075652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 8].length) (baseStart_1075652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075652 prefixEnd_1075652 := by exact prefixLift 1075652
  have htrace : WordTrace (prefixWord ++ tailWord_1075652) baseStart_1075652 baseEnd_1075652 := by
    simpa [prefixWord, tailWord_1075652, baseEnd_1075652] using wordTrace_append hprefix tailTrace_1075652
  have hstable : (prefixWord ++ tailWord_1075652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075652).length < 2 ^ (prefixWord ++ tailWord_1075652).sum := by decide
  have hdescent : baseEnd_1075652 < baseStart_1075652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075680 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 5]
def baseStart_1075680 : Nat := 118140960795 + 1075680 * 2 ^ 59
def prefixEnd_1075680 : Nat := 4983230072969 + 3 ^ 40 * 1075680 * 2
def baseEnd_1075680 : Nat := 122742415650768140167343

theorem tailTrace_1075680 : CollatzResearch.WordTrace tailWord_1075680 prefixEnd_1075680 122742415650768140167343 := by
  unfold tailWord_1075680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19616636371501273181544247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26155515162001697575392329 19616636371501273181544247)
  ·
    refine ⟨29424954557251909772316371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19616636371501273181544247 29424954557251909772316371)
    ·
      refine ⟨44137431835877864658474557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29424954557251909772316371 44137431835877864658474557)
      ·
        refine ⟨16551536938454199246927959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44137431835877864658474557 16551536938454199246927959)
        ·
          refine ⟨24827305407681298870391939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16551536938454199246927959 24827305407681298870391939)
          ·
            refine ⟨37240958111521948305587909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24827305407681298870391939 37240958111521948305587909)
            ·
              refine ⟨6982679645910365307297733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37240958111521948305587909 6982679645910365307297733)
              ·
                refine ⟨1309252433608193495118325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6982679645910365307297733 1309252433608193495118325)
                ·
                  refine ⟨122742415650768140167343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1309252433608193495118325 122742415650768140167343)
                  ·
                    rfl

theorem cell22_1075680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_1075680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075680 prefixEnd_1075680 := by exact prefixLift 1075680
  have htrace : WordTrace (prefixWord ++ tailWord_1075680) baseStart_1075680 baseEnd_1075680 := by
    simpa [prefixWord, tailWord_1075680, baseEnd_1075680] using wordTrace_append hprefix tailTrace_1075680
  have hstable : (prefixWord ++ tailWord_1075680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075680).length < 2 ^ (prefixWord ++ tailWord_1075680).sum := by decide
  have hdescent : baseEnd_1075680 < baseStart_1075680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075735 : List Nat := [1, 1, 3, 6, 1, 2, 2, 2, 1, 3]
def baseStart_1075735 : Nat := 118140960795 + 1075735 * 2 ^ 59
def prefixEnd_1075735 : Nat := 4983230072969 + 3 ^ 40 * 1075735 * 2
def baseEnd_1075735 : Nat := 368246074576302610376861

theorem tailTrace_1075735 : CollatzResearch.WordTrace tailWord_1075735 prefixEnd_1075735 368246074576302610376861 := by
  unfold tailWord_1075735
  simp only [CollatzResearch.WordTrace]
  refine ⟨39235278757803290756340659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26156852505202193837560439 39235278757803290756340659)
  ·
    refine ⟨58852918136704936134510989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39235278757803290756340659 58852918136704936134510989)
    ·
      refine ⟨22069844301264351050441621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58852918136704936134510989 22069844301264351050441621)
      ·
        refine ⟨1034523951621766455489451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22069844301264351050441621 1034523951621766455489451)
        ·
          refine ⟨1551785927432649683234177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034523951621766455489451 1551785927432649683234177)
          ·
            refine ⟨1163839445574487262425633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551785927432649683234177 1163839445574487262425633)
            ·
              refine ⟨872879584180865446819225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163839445574487262425633 872879584180865446819225)
              ·
                refine ⟨654659688135649085114419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872879584180865446819225 654659688135649085114419)
                ·
                  refine ⟨981989532203473627671629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654659688135649085114419 981989532203473627671629)
                  ·
                    refine ⟨368246074576302610376861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981989532203473627671629 368246074576302610376861)
                    ·
                      rfl

theorem cell22_1075735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_1075735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075735 prefixEnd_1075735 := by exact prefixLift 1075735
  have htrace : WordTrace (prefixWord ++ tailWord_1075735) baseStart_1075735 baseEnd_1075735 := by
    simpa [prefixWord, tailWord_1075735, baseEnd_1075735] using wordTrace_append hprefix tailTrace_1075735
  have hstable : (prefixWord ++ tailWord_1075735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075735).length < 2 ^ (prefixWord ++ tailWord_1075735).sum := by decide
  have hdescent : baseEnd_1075735 < baseStart_1075735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075755 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 4, 4]
def baseStart_1075755 : Nat := 118140960795 + 1075755 * 2 ^ 59
def prefixEnd_1075755 : Nat := 4983230072969 + 3 ^ 40 * 1075755 * 2
def baseEnd_1075755 : Nat := 368252920985029224876799

theorem tailTrace_1075755 : CollatzResearch.WordTrace tailWord_1075755 prefixEnd_1075755 368252920985029224876799 := by
  unfold tailWord_1075755
  simp only [CollatzResearch.WordTrace]
  refine ⟨39236008217730834172068719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26157338811820556114712479 39236008217730834172068719)
  ·
    refine ⟨58854012326596251258103079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39236008217730834172068719 58854012326596251258103079)
    ·
      refine ⟨88281018489894376887154619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58854012326596251258103079 88281018489894376887154619)
      ·
        refine ⟨132421527734841565330731929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88281018489894376887154619 132421527734841565330731929)
        ·
          refine ⟨99316145801131173998048947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132421527734841565330731929 99316145801131173998048947)
          ·
            refine ⟨148974218701696760997073421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99316145801131173998048947 148974218701696760997073421)
            ·
              refine ⟨55865332013136285373902533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148974218701696760997073421 55865332013136285373902533)
              ·
                refine ⟨10474749752463053507606725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55865332013136285373902533 10474749752463053507606725)
                ·
                  refine ⟨1964015578586822532676261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10474749752463053507606725 1964015578586822532676261)
                  ·
                    refine ⟨368252920985029224876799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964015578586822532676261 368252920985029224876799)
                    ·
                      rfl

theorem cell22_1075755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_1075755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075755 prefixEnd_1075755 := by exact prefixLift 1075755
  have htrace : WordTrace (prefixWord ++ tailWord_1075755) baseStart_1075755 baseEnd_1075755 := by
    simpa [prefixWord, tailWord_1075755, baseEnd_1075755] using wordTrace_append hprefix tailTrace_1075755
  have hstable : (prefixWord ++ tailWord_1075755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075755).length < 2 ^ (prefixWord ++ tailWord_1075755).sum := by decide
  have hdescent : baseEnd_1075755 < baseStart_1075755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075772 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_1075772 : Nat := 118140960795 + 1075772 * 2 ^ 59
def prefixEnd_1075772 : Nat := 4983230072969 + 3 ^ 40 * 1075772 * 2
def baseEnd_1075772 : Nat := 368258740432446847201747

theorem tailTrace_1075772 : CollatzResearch.WordTrace tailWord_1075772 prefixEnd_1075772 368258740432446847201747 := by
  unfold tailWord_1075772
  simp only [CollatzResearch.WordTrace]
  refine ⟨19618314129334623037718785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26157752172446164050291713 19618314129334623037718785)
  ·
    refine ⟨14713735597000967278289089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19618314129334623037718785 14713735597000967278289089)
    ·
      refine ⟨11035301697750725458716817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14713735597000967278289089 11035301697750725458716817)
      ·
        refine ⟨8276476273313044094037613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11035301697750725458716817 8276476273313044094037613)
        ·
          refine ⟨3103678602492391535264105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8276476273313044094037613 3103678602492391535264105)
          ·
            refine ⟨2327758951869293651448079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3103678602492391535264105 2327758951869293651448079)
            ·
              refine ⟨3491638427803940477172119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327758951869293651448079 3491638427803940477172119)
              ·
                refine ⟨5237457641705910715758179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3491638427803940477172119 5237457641705910715758179)
                ·
                  refine ⟨7856186462558866073637269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5237457641705910715758179 7856186462558866073637269)
                  ·
                    refine ⟨368258740432446847201747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7856186462558866073637269 368258740432446847201747)
                    ·
                      rfl

theorem cell22_1075772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_1075772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075772 prefixEnd_1075772 := by exact prefixLift 1075772
  have htrace : WordTrace (prefixWord ++ tailWord_1075772) baseStart_1075772 baseEnd_1075772 := by
    simpa [prefixWord, tailWord_1075772, baseEnd_1075772] using wordTrace_append hprefix tailTrace_1075772
  have hstable : (prefixWord ++ tailWord_1075772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075772).length < 2 ^ (prefixWord ++ tailWord_1075772).sum := by decide
  have hdescent : baseEnd_1075772 < baseStart_1075772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075800 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1075800 : Nat := 118140960795 + 1075800 * 2 ^ 59
def prefixEnd_1075800 : Nat := 4983230072969 + 3 ^ 40 * 1075800 * 2
def baseEnd_1075800 : Nat := 368268325404664107501661

theorem tailTrace_1075800 : CollatzResearch.WordTrace tailWord_1075800 prefixEnd_1075800 368268325404664107501661 := by
  unfold tailWord_1075800
  simp only [CollatzResearch.WordTrace]
  refine ⟨19618824751283903428728427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26158433001711871238304569 19618824751283903428728427)
  ·
    refine ⟨29428237126925855143092641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19618824751283903428728427 29428237126925855143092641)
    ·
      refine ⟨22071177845194391357319481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29428237126925855143092641 22071177845194391357319481)
      ·
        refine ⟨16553383383895793517989611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22071177845194391357319481 16553383383895793517989611)
        ·
          refine ⟨24830075075843690276984417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16553383383895793517989611 24830075075843690276984417)
          ·
            refine ⟨18622556306882767707738313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24830075075843690276984417 18622556306882767707738313)
            ·
              refine ⟨13966917230162075780803735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18622556306882767707738313 13966917230162075780803735)
              ·
                refine ⟨20950375845243113671205603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13966917230162075780803735 20950375845243113671205603)
                ·
                  refine ⟨31425563767864670506808405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20950375845243113671205603 31425563767864670506808405)
                  ·
                    refine ⟨368268325404664107501661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31425563767864670506808405 368268325404664107501661)
                    ·
                      rfl

theorem cell22_1075800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1075800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075800 prefixEnd_1075800 := by exact prefixLift 1075800
  have htrace : WordTrace (prefixWord ++ tailWord_1075800) baseStart_1075800 baseEnd_1075800 := by
    simpa [prefixWord, tailWord_1075800, baseEnd_1075800] using wordTrace_append hprefix tailTrace_1075800
  have hstable : (prefixWord ++ tailWord_1075800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075800).length < 2 ^ (prefixWord ++ tailWord_1075800).sum := by decide
  have hdescent : baseEnd_1075800 < baseStart_1075800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075836 : List Nat := [2, 2, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_1075836 : Nat := 118140960795 + 1075836 * 2 ^ 59
def prefixEnd_1075836 : Nat := 4983230072969 + 3 ^ 40 * 1075836 * 2
def baseEnd_1075836 : Nat := 368280648940372013601551

theorem tailTrace_1075836 : CollatzResearch.WordTrace tailWord_1075836 prefixEnd_1075836 368280648940372013601551 := by
  unfold tailWord_1075836
  simp only [CollatzResearch.WordTrace]
  refine ⟨19619481265218692502883681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26159308353624923337178241 19619481265218692502883681)
  ·
    refine ⟨14714610948914019377162761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19619481265218692502883681 14714610948914019377162761)
    ·
      refine ⟨11035958211685514532872071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14714610948914019377162761 11035958211685514532872071)
      ·
        refine ⟨16553937317528271799308107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11035958211685514532872071 16553937317528271799308107)
        ·
          refine ⟨24830905976292407698962161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16553937317528271799308107 24830905976292407698962161)
          ·
            refine ⟨18623179482219305774221621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24830905976292407698962161 18623179482219305774221621)
            ·
              refine ⟨1745923076458059916333277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18623179482219305774221621 1745923076458059916333277)
              ·
                refine ⟨654721153671772468624979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1745923076458059916333277 654721153671772468624979)
                ·
                  refine ⟨982081730507658702937469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654721153671772468624979 982081730507658702937469)
                  ·
                    refine ⟨368280648940372013601551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 982081730507658702937469 368280648940372013601551)
                    ·
                      rfl

theorem cell22_1075836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_1075836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075836 prefixEnd_1075836 := by exact prefixLift 1075836
  have htrace : WordTrace (prefixWord ++ tailWord_1075836) baseStart_1075836 baseEnd_1075836 := by
    simpa [prefixWord, tailWord_1075836, baseEnd_1075836] using wordTrace_append hprefix tailTrace_1075836
  have hstable : (prefixWord ++ tailWord_1075836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075836).length < 2 ^ (prefixWord ++ tailWord_1075836).sum := by decide
  have hdescent : baseEnd_1075836 < baseStart_1075836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075866 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_1075866 : Nat := 118140960795 + 1075866 * 2 ^ 59
def prefixEnd_1075866 : Nat := 4983230072969 + 3 ^ 40 * 1075866 * 2
def baseEnd_1075866 : Nat := 122763639517820645117153

theorem tailTrace_1075866 : CollatzResearch.WordTrace tailWord_1075866 prefixEnd_1075866 122763639517820645117153 := by
  unfold tailWord_1075866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9810014180082175032339863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26160037813552466752906301 9810014180082175032339863)
  ·
    refine ⟨14715021270123262548509795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9810014180082175032339863 14715021270123262548509795)
    ·
      refine ⟨22072531905184893822764693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14715021270123262548509795 22072531905184893822764693)
      ·
        refine ⟨1034649933055541897942095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22072531905184893822764693 1034649933055541897942095)
        ·
          refine ⟨1551974899583312846913143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034649933055541897942095 1551974899583312846913143)
          ·
            refine ⟨2327962349374969270369715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551974899583312846913143 2327962349374969270369715)
            ·
              refine ⟨3491943524062453905554573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327962349374969270369715 3491943524062453905554573)
              ·
                refine ⟨1309478821523420214582965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3491943524062453905554573 1309478821523420214582965)
                ·
                  refine ⟨122763639517820645117153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1309478821523420214582965 122763639517820645117153)
                  ·
                    rfl

theorem cell22_1075866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_1075866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075866 prefixEnd_1075866 := by exact prefixLift 1075866
  have htrace : WordTrace (prefixWord ++ tailWord_1075866) baseStart_1075866 baseEnd_1075866 := by
    simpa [prefixWord, tailWord_1075866, baseEnd_1075866] using wordTrace_append hprefix tailTrace_1075866
  have hstable : (prefixWord ++ tailWord_1075866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075866).length < 2 ^ (prefixWord ++ tailWord_1075866).sum := by decide
  have hdescent : baseEnd_1075866 < baseStart_1075866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075941 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_1075941 : Nat := 118140960795 + 1075941 * 2 ^ 59
def prefixEnd_1075941 : Nat := 4983230072969 + 3 ^ 40 * 1075941 * 2
def baseEnd_1075941 : Nat := 368316592586186739726229

theorem tailTrace_1075941 : CollatzResearch.WordTrace tailWord_1075941 prefixEnd_1075941 368316592586186739726229 := by
  unfold tailWord_1075941
  simp only [CollatzResearch.WordTrace]
  refine ⟨39242792195056987938339677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26161861463371325292226451 39242792195056987938339677)
  ·
    refine ⟨14716047073146370476877379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39242792195056987938339677 14716047073146370476877379)
    ·
      refine ⟨22074070609719555715316069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14716047073146370476877379 22074070609719555715316069)
      ·
        refine ⟨4138888239322416696621763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22074070609719555715316069 4138888239322416696621763)
        ·
          refine ⟨6208332358983625044932645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138888239322416696621763 6208332358983625044932645)
          ·
            refine ⟨1164062317309429695924871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6208332358983625044932645 1164062317309429695924871)
            ·
              refine ⟨1746093475964144543887307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164062317309429695924871 1746093475964144543887307)
              ·
                refine ⟨2619140213946216815830961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746093475964144543887307 2619140213946216815830961)
                ·
                  refine ⟨1964355160459662611873221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619140213946216815830961 1964355160459662611873221)
                  ·
                    refine ⟨368316592586186739726229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964355160459662611873221 368316592586186739726229)
                    ·
                      rfl

theorem cell22_1075941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_1075941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1075941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1075941 prefixEnd_1075941 := by exact prefixLift 1075941
  have htrace : WordTrace (prefixWord ++ tailWord_1075941) baseStart_1075941 baseEnd_1075941 := by
    simpa [prefixWord, tailWord_1075941, baseEnd_1075941] using wordTrace_append hprefix tailTrace_1075941
  have hstable : (prefixWord ++ tailWord_1075941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075941).length < 2 ^ (prefixWord ++ tailWord_1075941).sum := by decide
  have hdescent : baseEnd_1075941 < baseStart_1075941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076022 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1076022 : Nat := 118140960795 + 1076022 * 2 ^ 59
def prefixEnd_1076022 : Nat := 4983230072969 + 3 ^ 40 * 1076022 * 2
def baseEnd_1076022 : Nat := 368344320541529528450981

theorem tailTrace_1076022 : CollatzResearch.WordTrace tailWord_1076022 prefixEnd_1076022 368344320541529528450981 := by
  unfold tailWord_1076022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452859156735221173252395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26163831005175692514692213 2452859156735221173252395)
  ·
    refine ⟨3679288735102831759878593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2452859156735221173252395 3679288735102831759878593)
    ·
      refine ⟨2759466551327123819908945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3679288735102831759878593 2759466551327123819908945)
      ·
        refine ⟨2069599913495342864931709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2759466551327123819908945 2069599913495342864931709)
        ·
          refine ⟨776099967560753574349391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2069599913495342864931709 776099967560753574349391)
          ·
            refine ⟨1164149951341130361524087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776099967560753574349391 1164149951341130361524087)
            ·
              refine ⟨1746224927011695542286131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164149951341130361524087 1746224927011695542286131)
              ·
                refine ⟨2619337390517543313429197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746224927011695542286131 2619337390517543313429197)
                ·
                  refine ⟨982251521444078742535949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2619337390517543313429197 982251521444078742535949)
                  ·
                    refine ⟨368344320541529528450981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 982251521444078742535949 368344320541529528450981)
                    ·
                      rfl

theorem cell22_1076022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1076022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076022 prefixEnd_1076022 := by exact prefixLift 1076022
  have htrace : WordTrace (prefixWord ++ tailWord_1076022) baseStart_1076022 baseEnd_1076022 := by
    simpa [prefixWord, tailWord_1076022, baseEnd_1076022] using wordTrace_append hprefix tailTrace_1076022
  have hstable : (prefixWord ++ tailWord_1076022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076022).length < 2 ^ (prefixWord ++ tailWord_1076022).sum := by decide
  have hdescent : baseEnd_1076022 < baseStart_1076022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076119 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 7]
def baseStart_1076119 : Nat := 118140960795 + 1076119 * 2 ^ 59
def prefixEnd_1076119 : Nat := 4983230072969 + 3 ^ 40 * 1076119 * 2
def baseEnd_1076119 : Nat := 122792508541284536258561

theorem tailTrace_1076119 : CollatzResearch.WordTrace tailWord_1076119 prefixEnd_1076119 122792508541284536258561 := by
  unfold tailWord_1076119
  simp only [CollatzResearch.WordTrace]
  refine ⟨39249284388412124338319411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26166189592274749558879607 39249284388412124338319411)
  ·
    refine ⟨58873926582618186507479117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39249284388412124338319411 58873926582618186507479117)
    ·
      refine ⟨22077722468481819940304669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58873926582618186507479117 22077722468481819940304669)
      ·
        refine ⟨8279145925680682477614251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22077722468481819940304669 8279145925680682477614251)
        ·
          refine ⟨12418718888521023716421377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8279145925680682477614251 12418718888521023716421377)
          ·
            refine ⟨9314039166390767787316033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12418718888521023716421377 9314039166390767787316033)
            ·
              refine ⟨6985529374793075840487025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9314039166390767787316033 6985529374793075840487025)
              ·
                refine ⟨5239147031094806880365269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6985529374793075840487025 5239147031094806880365269)
                ·
                  refine ⟨122792508541284536258561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5239147031094806880365269 122792508541284536258561)
                  ·
                    rfl

theorem cell22_1076119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 7].length) (baseStart_1076119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076119 prefixEnd_1076119 := by exact prefixLift 1076119
  have htrace : WordTrace (prefixWord ++ tailWord_1076119) baseStart_1076119 baseEnd_1076119 := by
    simpa [prefixWord, tailWord_1076119, baseEnd_1076119] using wordTrace_append hprefix tailTrace_1076119
  have hstable : (prefixWord ++ tailWord_1076119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076119).length < 2 ^ (prefixWord ++ tailWord_1076119).sum := by decide
  have hdescent : baseEnd_1076119 < baseStart_1076119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076153 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 5]
def baseStart_1076153 : Nat := 118140960795 + 1076153 * 2 ^ 59
def prefixEnd_1076153 : Nat := 4983230072969 + 3 ^ 40 * 1076153 * 2
def baseEnd_1076153 : Nat := 122796388172896284475193

theorem tailTrace_1076153 : CollatzResearch.WordTrace tailWord_1076153 prefixEnd_1076153 122796388172896284475193 := by
  unfold tailWord_1076153
  simp only [CollatzResearch.WordTrace]
  refine ⟨39250524470288948145057113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26167016313525965430038075 39250524470288948145057113)
  ·
    refine ⟨29437893352716711108792835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39250524470288948145057113 29437893352716711108792835)
    ·
      refine ⟨44156840029075066663189253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29437893352716711108792835 44156840029075066663189253)
      ·
        refine ⟨8279407505451574999347985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44156840029075066663189253 8279407505451574999347985)
        ·
          refine ⟨6209555629088681249510989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8279407505451574999347985 6209555629088681249510989)
          ·
            refine ⟨2328583360908255468566621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6209555629088681249510989 2328583360908255468566621)
            ·
              refine ⟨873218760340595800712483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2328583360908255468566621 873218760340595800712483)
              ·
                refine ⟨1309828140510893701068725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873218760340595800712483 1309828140510893701068725)
                ·
                  refine ⟨122796388172896284475193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1309828140510893701068725 122796388172896284475193)
                  ·
                    rfl

theorem cell22_1076153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_1076153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076153 prefixEnd_1076153 := by exact prefixLift 1076153
  have htrace : WordTrace (prefixWord ++ tailWord_1076153) baseStart_1076153 baseEnd_1076153 := by
    simpa [prefixWord, tailWord_1076153, baseEnd_1076153] using wordTrace_append hprefix tailTrace_1076153
  have hstable : (prefixWord ++ tailWord_1076153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076153).length < 2 ^ (prefixWord ++ tailWord_1076153).sum := by decide
  have hdescent : baseEnd_1076153 < baseStart_1076153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076322 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1076322 : Nat := 118140960795 + 1076322 * 2 ^ 59
def prefixEnd_1076322 : Nat := 4983230072969 + 3 ^ 40 * 1076322 * 2
def baseEnd_1076322 : Nat := 122815672224142915316687

theorem tailTrace_1076322 : CollatzResearch.WordTrace tailWord_1076322 prefixEnd_1076322 122815672224142915316687 := by
  unfold tailWord_1076322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814172101669172501989805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26171125604451126671972813 9814172101669172501989805)
  ·
    refine ⟨3680314538125939688246177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9814172101669172501989805 3680314538125939688246177)
    ·
      refine ⟨2760235903594454766184633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3680314538125939688246177 2760235903594454766184633)
      ·
        refine ⟨2070176927695841074638475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2760235903594454766184633 2070176927695841074638475)
        ·
          refine ⟨3105265391543761611957713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070176927695841074638475 3105265391543761611957713)
          ·
            refine ⟨2328949043657821208968285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3105265391543761611957713 2328949043657821208968285)
            ·
              refine ⟨873355891371682953363107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2328949043657821208968285 873355891371682953363107)
              ·
                refine ⟨1310033837057524430044661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873355891371682953363107 1310033837057524430044661)
                ·
                  refine ⟨122815672224142915316687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1310033837057524430044661 122815672224142915316687)
                  ·
                    rfl

theorem cell22_1076322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1076322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076322 prefixEnd_1076322 := by exact prefixLift 1076322
  have htrace : WordTrace (prefixWord ++ tailWord_1076322) baseStart_1076322 baseEnd_1076322 := by
    simpa [prefixWord, tailWord_1076322, baseEnd_1076322] using wordTrace_append hprefix tailTrace_1076322
  have hstable : (prefixWord ++ tailWord_1076322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076322).length < 2 ^ (prefixWord ++ tailWord_1076322).sum := by decide
  have hdescent : baseEnd_1076322 < baseStart_1076322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076333 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 6]
def baseStart_1076333 : Nat := 118140960795 + 1076333 * 2 ^ 59
def prefixEnd_1076333 : Nat := 4983230072969 + 3 ^ 40 * 1076333 * 2
def baseEnd_1076333 : Nat := 122816927399076127975009

theorem tailTrace_1076333 : CollatzResearch.WordTrace tailWord_1076333 prefixEnd_1076333 122816927399076127975009 := by
  unfold tailWord_1076333
  simp only [CollatzResearch.WordTrace]
  refine ⟨39257089609636838886609653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26171393073091225924406435 39257089609636838886609653)
  ·
    refine ⟨3680352150903453645619655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39257089609636838886609653 3680352150903453645619655)
    ·
      refine ⟨5520528226355180468429483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3680352150903453645619655 5520528226355180468429483)
      ·
        refine ⟨8280792339532770702644225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5520528226355180468429483 8280792339532770702644225)
        ·
          refine ⟨6210594254649578026983169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8280792339532770702644225 6210594254649578026983169)
          ·
            refine ⟨4657945690987183520237377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6210594254649578026983169 4657945690987183520237377)
            ·
              refine ⟨3493459268240387640178033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4657945690987183520237377 3493459268240387640178033)
              ·
                refine ⟨2620094451180290730133525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3493459268240387640178033 2620094451180290730133525)
                ·
                  refine ⟨122816927399076127975009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2620094451180290730133525 122816927399076127975009)
                  ·
                    rfl

theorem cell22_1076333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_1076333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076333 prefixEnd_1076333 := by exact prefixLift 1076333
  have htrace : WordTrace (prefixWord ++ tailWord_1076333) baseStart_1076333 baseEnd_1076333 := by
    simpa [prefixWord, tailWord_1076333, baseEnd_1076333] using wordTrace_append hprefix tailTrace_1076333
  have hstable : (prefixWord ++ tailWord_1076333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076333).length < 2 ^ (prefixWord ++ tailWord_1076333).sum := by decide
  have hdescent : baseEnd_1076333 < baseStart_1076333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076348 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_1076348 : Nat := 118140960795 + 1076348 * 2 ^ 59
def prefixEnd_1076348 : Nat := 4983230072969 + 3 ^ 40 * 1076348 * 2
def baseEnd_1076348 : Nat := 368455917003773344799981

theorem tailTrace_1076348 : CollatzResearch.WordTrace tailWord_1076348 prefixEnd_1076348 368455917003773344799981 := by
  unfold tailWord_1076348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19628818352291248224202849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26171757803054997632270465 19628818352291248224202849)
  ·
    refine ⟨14721613764218436168152137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19628818352291248224202849 14721613764218436168152137)
    ·
      refine ⟨11041210323163827126114103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14721613764218436168152137 11041210323163827126114103)
      ·
        refine ⟨16561815484745740689171155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11041210323163827126114103 16561815484745740689171155)
        ·
          refine ⟨24842723227118611033756733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16561815484745740689171155 24842723227118611033756733)
          ·
            refine ⟨9316021210169479137658775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24842723227118611033756733 9316021210169479137658775)
            ·
              refine ⟨13974031815254218706488163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9316021210169479137658775 13974031815254218706488163)
              ·
                refine ⟨20961047722881328059732245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13974031815254218706488163 20961047722881328059732245)
                ·
                  refine ⟨982549112010062252799949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20961047722881328059732245 982549112010062252799949)
                  ·
                    refine ⟨368455917003773344799981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 982549112010062252799949 368455917003773344799981)
                    ·
                      rfl

theorem cell22_1076348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_1076348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076348 prefixEnd_1076348 := by exact prefixLift 1076348
  have htrace : WordTrace (prefixWord ++ tailWord_1076348) baseStart_1076348 baseEnd_1076348 := by
    simpa [prefixWord, tailWord_1076348, baseEnd_1076348] using wordTrace_append hprefix tailTrace_1076348
  have hstable : (prefixWord ++ tailWord_1076348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076348).length < 2 ^ (prefixWord ++ tailWord_1076348).sum := by decide
  have hdescent : baseEnd_1076348 < baseStart_1076348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076361 : List Nat := [1, 2, 1, 1, 4, 3, 10]
def baseStart_1076361 : Nat := 118140960795 + 1076361 * 2 ^ 59
def prefixEnd_1076361 : Nat := 4983230072969 + 3 ^ 40 * 1076361 * 2
def baseEnd_1076361 : Nat := 13646680265535023860183

theorem tailTrace_1076361 : CollatzResearch.WordTrace tailWord_1076361 prefixEnd_1076361 13646680265535023860183 := by
  unfold tailWord_1076361
  simp only [CollatzResearch.WordTrace]
  refine ⟨39258110853535399668628937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26172073902356933112419291 39258110853535399668628937)
  ·
    refine ⟨29443583140151549751471703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39258110853535399668628937 29443583140151549751471703)
    ·
      refine ⟨44165374710227324627207555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29443583140151549751471703 44165374710227324627207555)
      ·
        refine ⟨66248062065340986940811333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44165374710227324627207555 66248062065340986940811333)
        ·
          refine ⟨12421511637251435051402125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66248062065340986940811333 12421511637251435051402125)
          ·
            refine ⟨4658066863969288144275797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12421511637251435051402125 4658066863969288144275797)
            ·
              refine ⟨13646680265535023860183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4658066863969288144275797 13646680265535023860183)
              ·
                rfl

theorem cell22_1076361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 10].length) (baseStart_1076361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076361 prefixEnd_1076361 := by exact prefixLift 1076361
  have htrace : WordTrace (prefixWord ++ tailWord_1076361) baseStart_1076361 baseEnd_1076361 := by
    simpa [prefixWord, tailWord_1076361, baseEnd_1076361] using wordTrace_append hprefix tailTrace_1076361
  have hstable : (prefixWord ++ tailWord_1076361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076361).length < 2 ^ (prefixWord ++ tailWord_1076361).sum := by decide
  have hdescent : baseEnd_1076361 < baseStart_1076361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076378 : List Nat := [3, 1, 1, 5, 1, 1, 1, 9]
def baseStart_1076378 : Nat := 118140960795 + 1076378 * 2 ^ 59
def prefixEnd_1076378 : Nat := 4983230072969 + 3 ^ 40 * 1076378 * 2
def baseEnd_1076378 : Nat := 40940687401873696283321

theorem tailTrace_1076378 : CollatzResearch.WordTrace tailWord_1076378 prefixEnd_1076378 40940687401873696283321 := by
  unfold tailWord_1076378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814682723618452892999447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26172487262982541047998525 9814682723618452892999447)
  ·
    refine ⟨14722024085427679339499171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9814682723618452892999447 14722024085427679339499171)
    ·
      refine ⟨22083036128141519009248757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14722024085427679339499171 22083036128141519009248757)
      ·
        refine ⟨2070284637013267407117071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22083036128141519009248757 2070284637013267407117071)
        ·
          refine ⟨3105426955519901110675607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070284637013267407117071 3105426955519901110675607)
          ·
            refine ⟨4658140433279851666013411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105426955519901110675607 4658140433279851666013411)
            ·
              refine ⟨6987210649919777499020117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4658140433279851666013411 6987210649919777499020117)
              ·
                refine ⟨40940687401873696283321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6987210649919777499020117 40940687401873696283321)
                ·
                  rfl

theorem cell22_1076378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_1076378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076378 prefixEnd_1076378 := by exact prefixLift 1076378
  have htrace : WordTrace (prefixWord ++ tailWord_1076378) baseStart_1076378 baseEnd_1076378 := by
    simpa [prefixWord, tailWord_1076378, baseEnd_1076378] using wordTrace_append hprefix tailTrace_1076378
  have hstable : (prefixWord ++ tailWord_1076378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076378).length < 2 ^ (prefixWord ++ tailWord_1076378).sum := by decide
  have hdescent : baseEnd_1076378 < baseStart_1076378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076397 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1076397 : Nat := 118140960795 + 1076397 * 2 ^ 59
def prefixEnd_1076397 : Nat := 4983230072969 + 3 ^ 40 * 1076397 * 2
def baseEnd_1076397 : Nat := 368472690705153550324831

theorem tailTrace_1076397 : CollatzResearch.WordTrace tailWord_1076397 prefixEnd_1076397 368472690705153550324831 := by
  unfold tailWord_1076397
  simp only [CollatzResearch.WordTrace]
  refine ⟨39259423881404977816939445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26172949254269985211292963 39259423881404977816939445)
  ·
    refine ⟨3680570988881716670338073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39259423881404977816939445 3680570988881716670338073)
    ·
      refine ⟨2760428241661287502753555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3680570988881716670338073 2760428241661287502753555)
      ·
        refine ⟨4140642362491931254130333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760428241661287502753555 4140642362491931254130333)
        ·
          refine ⟨1552740885934474220298875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4140642362491931254130333 1552740885934474220298875)
          ·
            refine ⟨2329111328901711330448313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552740885934474220298875 2329111328901711330448313)
            ·
              refine ⟨1746833496676283497836235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2329111328901711330448313 1746833496676283497836235)
              ·
                refine ⟨2620250245014425246754353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746833496676283497836235 2620250245014425246754353)
                ·
                  refine ⟨1965187683760818935065765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2620250245014425246754353 1965187683760818935065765)
                  ·
                    refine ⟨368472690705153550324831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1965187683760818935065765 368472690705153550324831)
                    ·
                      rfl

theorem cell22_1076397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1076397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076397 prefixEnd_1076397 := by exact prefixLift 1076397
  have htrace : WordTrace (prefixWord ++ tailWord_1076397) baseStart_1076397 baseEnd_1076397 := by
    simpa [prefixWord, tailWord_1076397, baseEnd_1076397] using wordTrace_append hprefix tailTrace_1076397
  have hstable : (prefixWord ++ tailWord_1076397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076397).length < 2 ^ (prefixWord ++ tailWord_1076397).sum := by decide
  have hdescent : baseEnd_1076397 < baseStart_1076397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076418 : List Nat := [3, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1076418 : Nat := 118140960795 + 1076418 * 2 ^ 59
def prefixEnd_1076418 : Nat := 4983230072969 + 3 ^ 40 * 1076418 * 2
def baseEnd_1076418 : Nat := 122826626478105498516589

theorem tailTrace_1076418 : CollatzResearch.WordTrace tailWord_1076418 prefixEnd_1076418 122826626478105498516589 := by
  unfold tailWord_1076418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815047453582224600863477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26173459876219265602302605 9815047453582224600863477)
  ·
    refine ⟨920160698773333556330951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9815047453582224600863477 920160698773333556330951)
    ·
      refine ⟨1380241048160000334496427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920160698773333556330951 1380241048160000334496427)
      ·
        refine ⟨2070361572240000501744641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380241048160000334496427 2070361572240000501744641)
        ·
          refine ⟨1552771179180000376308481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2070361572240000501744641 1552771179180000376308481)
          ·
            refine ⟨1164578384385000282231361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1552771179180000376308481 1164578384385000282231361)
            ·
              refine ⟨873433788288750211673521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164578384385000282231361 873433788288750211673521)
              ·
                refine ⟨655075341216562658755141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873433788288750211673521 655075341216562658755141)
                ·
                  refine ⟨122826626478105498516589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655075341216562658755141 122826626478105498516589)
                  ·
                    rfl

theorem cell22_1076418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1076418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076418 prefixEnd_1076418 := by exact prefixLift 1076418
  have htrace : WordTrace (prefixWord ++ tailWord_1076418) baseStart_1076418 baseEnd_1076418 := by
    simpa [prefixWord, tailWord_1076418, baseEnd_1076418] using wordTrace_append hprefix tailTrace_1076418
  have hstable : (prefixWord ++ tailWord_1076418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076418).length < 2 ^ (prefixWord ++ tailWord_1076418).sum := by decide
  have hdescent : baseEnd_1076418 < baseStart_1076418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076429 : List Nat := [1, 6, 2, 2, 1, 2, 1, 7]
def baseStart_1076429 : Nat := 118140960795 + 1076429 * 2 ^ 59
def prefixEnd_1076429 : Nat := 4983230072969 + 3 ^ 40 * 1076429 * 2
def baseEnd_1076429 : Nat := 40942627217679570391637

theorem tailTrace_1076429 : CollatzResearch.WordTrace tailWord_1076429 prefixEnd_1076429 40942627217679570391637 := by
  unfold tailWord_1076429
  simp only [CollatzResearch.WordTrace]
  refine ⟨39260591017289047282104341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26173727344859364854736227 39260591017289047282104341)
  ·
    refine ⟨1840340203935424091348641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39260591017289047282104341 1840340203935424091348641)
    ·
      refine ⟨1380255152951568068511481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1840340203935424091348641 1380255152951568068511481)
      ·
        refine ⟨1035191364713676051383611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1380255152951568068511481 1035191364713676051383611)
        ·
          refine ⟨1552787047070514077075417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1035191364713676051383611 1552787047070514077075417)
          ·
            refine ⟨1164590285302885557806563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1552787047070514077075417 1164590285302885557806563)
            ·
              refine ⟨1746885427954328336709845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164590285302885557806563 1746885427954328336709845)
              ·
                refine ⟨40942627217679570391637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1746885427954328336709845 40942627217679570391637)
                ·
                  rfl

theorem cell22_1076429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 7].length) (baseStart_1076429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076429 prefixEnd_1076429 := by exact prefixLift 1076429
  have htrace : WordTrace (prefixWord ++ tailWord_1076429) baseStart_1076429 baseEnd_1076429 := by
    simpa [prefixWord, tailWord_1076429, baseEnd_1076429] using wordTrace_append hprefix tailTrace_1076429
  have hstable : (prefixWord ++ tailWord_1076429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076429).length < 2 ^ (prefixWord ++ tailWord_1076429).sum := by decide
  have hdescent : baseEnd_1076429 < baseStart_1076429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076485 : List Nat := [1, 3, 1, 1, 2, 1, 3, 6, 4]
def baseStart_1076485 : Nat := 118140960795 + 1076485 * 2 ^ 59
def prefixEnd_1076485 : Nat := 4983230072969 + 3 ^ 40 * 1076485 * 2
def baseEnd_1076485 : Nat := 122834271634516884708187

theorem tailTrace_1076485 : CollatzResearch.WordTrace tailWord_1076485 prefixEnd_1076485 122834271634516884708187 := by
  unfold tailWord_1076485
  simp only [CollatzResearch.WordTrace]
  refine ⟨39262633505086168846142909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26175089003390779230761939 39262633505086168846142909)
  ·
    refine ⟨14723487564407313317303591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39262633505086168846142909 14723487564407313317303591)
    ·
      refine ⟨22085231346610969975955387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14723487564407313317303591 22085231346610969975955387)
      ·
        refine ⟨33127847019916454963933081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22085231346610969975955387 33127847019916454963933081)
        ·
          refine ⟨24845885264937341222949811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33127847019916454963933081 24845885264937341222949811)
          ·
            refine ⟨37268827897406011834424717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24845885264937341222949811 37268827897406011834424717)
            ·
              refine ⟨13975810461527254437909269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37268827897406011834424717 13975810461527254437909269)
              ·
                refine ⟨655116115384090051776997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13975810461527254437909269 655116115384090051776997)
                ·
                  refine ⟨122834271634516884708187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655116115384090051776997 122834271634516884708187)
                  ·
                    rfl

theorem cell22_1076485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_1076485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076485 prefixEnd_1076485 := by exact prefixLift 1076485
  have htrace : WordTrace (prefixWord ++ tailWord_1076485) baseStart_1076485 baseEnd_1076485 := by
    simpa [prefixWord, tailWord_1076485, baseEnd_1076485] using wordTrace_append hprefix tailTrace_1076485
  have hstable : (prefixWord ++ tailWord_1076485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076485).length < 2 ^ (prefixWord ++ tailWord_1076485).sum := by decide
  have hdescent : baseEnd_1076485 < baseStart_1076485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076530 : List Nat := [3, 2, 1, 1, 4, 3, 8]
def baseStart_1076530 : Nat := 118140960795 + 1076530 * 2 ^ 59
def prefixEnd_1076530 : Nat := 4983230072969 + 3 ^ 40 * 1076530 * 2
def baseEnd_1076530 : Nat := 13648822937895760620349

theorem tailTrace_1076530 : CollatzResearch.WordTrace tailWord_1076530 prefixEnd_1076530 13648822937895760620349 := by
  unfold tailWord_1076530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9816068697480785382882761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26176183193282094354354029 9816068697480785382882761)
  ·
    refine ⟨7362051523110589037162071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9816068697480785382882761 7362051523110589037162071)
    ·
      refine ⟨11043077284665883555743107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7362051523110589037162071 11043077284665883555743107)
      ·
        refine ⟨16564615926998825333614661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11043077284665883555743107 16564615926998825333614661)
        ·
          refine ⟨3105865486312279750052749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16564615926998825333614661 3105865486312279750052749)
          ·
            refine ⟨1164699557367104906269781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3105865486312279750052749 1164699557367104906269781)
            ·
              refine ⟨13648822937895760620349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1164699557367104906269781 13648822937895760620349)
              ·
                rfl

theorem cell22_1076530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 8].length) (baseStart_1076530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076530 prefixEnd_1076530 := by exact prefixLift 1076530
  have htrace : WordTrace (prefixWord ++ tailWord_1076530) baseStart_1076530 baseEnd_1076530 := by
    simpa [prefixWord, tailWord_1076530, baseEnd_1076530] using wordTrace_append hprefix tailTrace_1076530
  have hstable : (prefixWord ++ tailWord_1076530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076530).length < 2 ^ (prefixWord ++ tailWord_1076530).sum := by decide
  have hdescent : baseEnd_1076530 < baseStart_1076530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076532 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1076532 : Nat := 118140960795 + 1076532 * 2 ^ 59
def prefixEnd_1076532 : Nat := 4983230072969 + 3 ^ 40 * 1076532 * 2
def baseEnd_1076532 : Nat := 368518903964058198199417

theorem tailTrace_1076532 : CollatzResearch.WordTrace tailWord_1076532 prefixEnd_1076532 368518903964058198199417 := by
  unfold tailWord_1076532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19632173867957947936551925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26176231823943930582069233 19632173867957947936551925)
  ·
    refine ⟨1840516300121057619051743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19632173867957947936551925 1840516300121057619051743)
    ·
      refine ⟨2760774450181586428577615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1840516300121057619051743 2760774450181586428577615)
      ·
        refine ⟨4141161675272379642866423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760774450181586428577615 4141161675272379642866423)
        ·
          refine ⟨6211742512908569464299635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4141161675272379642866423 6211742512908569464299635)
          ·
            refine ⟨9317613769362854196449453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6211742512908569464299635 9317613769362854196449453)
            ·
              refine ⟨3494105163511070323668545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9317613769362854196449453 3494105163511070323668545)
              ·
                refine ⟨2620578872633302742751409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3494105163511070323668545 2620578872633302742751409)
                ·
                  refine ⟨1965434154474977057063557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2620578872633302742751409 1965434154474977057063557)
                  ·
                    refine ⟨368518903964058198199417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1965434154474977057063557 368518903964058198199417)
                    ·
                      rfl

theorem cell22_1076532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1076532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076532 prefixEnd_1076532 := by exact prefixLift 1076532
  have htrace : WordTrace (prefixWord ++ tailWord_1076532) baseStart_1076532 baseEnd_1076532 := by
    simpa [prefixWord, tailWord_1076532, baseEnd_1076532] using wordTrace_append hprefix tailTrace_1076532
  have hstable : (prefixWord ++ tailWord_1076532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076532).length < 2 ^ (prefixWord ++ tailWord_1076532).sum := by decide
  have hdescent : baseEnd_1076532 < baseStart_1076532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076605 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1076605 : Nat := 118140960795 + 1076605 * 2 ^ 59
def prefixEnd_1076605 : Nat := 4983230072969 + 3 ^ 40 * 1076605 * 2
def baseEnd_1076605 : Nat := 368543893355910341124193

theorem tailTrace_1076605 : CollatzResearch.WordTrace tailWord_1076605 prefixEnd_1076605 368543893355910341124193 := by
  unfold tailWord_1076605
  simp only [CollatzResearch.WordTrace]
  refine ⟨39267010264651429340511269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26178006843100952893674179 39267010264651429340511269)
  ·
    refine ⟨7362564424622143001345863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39267010264651429340511269 7362564424622143001345863)
    ·
      refine ⟨11043846636933214502018795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7362564424622143001345863 11043846636933214502018795)
      ·
        refine ⟨16565769955399821753028193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11043846636933214502018795 16565769955399821753028193)
        ·
          refine ⟨12424327466549866314771145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16565769955399821753028193 12424327466549866314771145)
          ·
            refine ⟨9318245599912399736078359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12424327466549866314771145 9318245599912399736078359)
            ·
              refine ⟨13977368399868599604117539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9318245599912399736078359 13977368399868599604117539)
              ·
                refine ⟨20966052599802899406176309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13977368399868599604117539 20966052599802899406176309)
                ·
                  refine ⟨1965567431231521819329029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20966052599802899406176309 1965567431231521819329029)
                  ·
                    refine ⟨368543893355910341124193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1965567431231521819329029 368543893355910341124193)
                    ·
                      rfl

theorem cell22_1076605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1076605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076605 prefixEnd_1076605 := by exact prefixLift 1076605
  have htrace : WordTrace (prefixWord ++ tailWord_1076605) baseStart_1076605 baseEnd_1076605 := by
    simpa [prefixWord, tailWord_1076605, baseEnd_1076605] using wordTrace_append hprefix tailTrace_1076605
  have hstable : (prefixWord ++ tailWord_1076605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076605).length < 2 ^ (prefixWord ++ tailWord_1076605).sum := by decide
  have hdescent : baseEnd_1076605 < baseStart_1076605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076620 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 6]
def baseStart_1076620 : Nat := 118140960795 + 1076620 * 2 ^ 59
def prefixEnd_1076620 : Nat := 4983230072969 + 3 ^ 40 * 1076620 * 2
def baseEnd_1076620 : Nat := 122849676054151767333049

theorem tailTrace_1076620 : CollatzResearch.WordTrace tailWord_1076620 prefixEnd_1076620 122849676054151767333049 := by
  unfold tailWord_1076620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19633778679798543451153657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26178371573064724601538209 19633778679798543451153657)
  ·
    refine ⟨14725334009848907588365243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19633778679798543451153657 14725334009848907588365243)
    ·
      refine ⟨22088001014773361382547865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14725334009848907588365243 22088001014773361382547865)
      ·
        refine ⟨16566000761080021036910899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22088001014773361382547865 16566000761080021036910899)
        ·
          refine ⟨24849001141620031555366349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16566000761080021036910899 24849001141620031555366349)
          ·
            refine ⟨9318375428107511833262381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24849001141620031555366349 9318375428107511833262381)
            ·
              refine ⟨3494390785540316937473393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9318375428107511833262381 3494390785540316937473393)
              ·
                refine ⟨2620793089155237703105045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3494390785540316937473393 2620793089155237703105045)
                ·
                  refine ⟨122849676054151767333049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2620793089155237703105045 122849676054151767333049)
                  ·
                    rfl

theorem cell22_1076620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_1076620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076620 prefixEnd_1076620 := by exact prefixLift 1076620
  have htrace : WordTrace (prefixWord ++ tailWord_1076620) baseStart_1076620 baseEnd_1076620 := by
    simpa [prefixWord, tailWord_1076620, baseEnd_1076620] using wordTrace_append hprefix tailTrace_1076620
  have hstable : (prefixWord ++ tailWord_1076620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076620).length < 2 ^ (prefixWord ++ tailWord_1076620).sum := by decide
  have hdescent : baseEnd_1076620 < baseStart_1076620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076639 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 1, 4]
def baseStart_1076639 : Nat := 118140960795 + 1076639 * 2 ^ 59
def prefixEnd_1076639 : Nat := 4983230072969 + 3 ^ 40 * 1076639 * 2
def baseEnd_1076639 : Nat := 368555532250745585774089

theorem tailTrace_1076639 : CollatzResearch.WordTrace tailWord_1076639 prefixEnd_1076639 368555532250745585774089 := by
  unfold tailWord_1076639
  simp only [CollatzResearch.WordTrace]
  refine ⟨39268250346528253147248971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26178833564352168764832647 39268250346528253147248971)
  ·
    refine ⟨58902375519792379720873457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39268250346528253147248971 58902375519792379720873457)
    ·
      refine ⟨44176781639844284790655093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58902375519792379720873457 44176781639844284790655093)
      ·
        refine ⟨4141573278735401699123915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44176781639844284790655093 4141573278735401699123915)
        ·
          refine ⟨6212359918103102548685873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4141573278735401699123915 6212359918103102548685873)
          ·
            refine ⟨4659269938577326911514405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6212359918103102548685873 4659269938577326911514405)
            ·
              refine ⟨873613113483248795908951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4659269938577326911514405 873613113483248795908951)
              ·
                refine ⟨1310419670224873193863427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873613113483248795908951 1310419670224873193863427)
                ·
                  refine ⟨1965629505337309790795141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310419670224873193863427 1965629505337309790795141)
                  ·
                    refine ⟨368555532250745585774089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1965629505337309790795141 368555532250745585774089)
                    ·
                      rfl

theorem cell22_1076639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_1076639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076639 prefixEnd_1076639 := by exact prefixLift 1076639
  have htrace : WordTrace (prefixWord ++ tailWord_1076639) baseStart_1076639 baseEnd_1076639 := by
    simpa [prefixWord, tailWord_1076639, baseEnd_1076639] using wordTrace_append hprefix tailTrace_1076639
  have hstable : (prefixWord ++ tailWord_1076639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076639).length < 2 ^ (prefixWord ++ tailWord_1076639).sum := by decide
  have hdescent : baseEnd_1076639 < baseStart_1076639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076680 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1076680 : Nat := 118140960795 + 1076680 * 2 ^ 59
def prefixEnd_1076680 : Nat := 4983230072969 + 3 ^ 40 * 1076680 * 2
def baseEnd_1076680 : Nat := 368569567388635145498963

theorem tailTrace_1076680 : CollatzResearch.WordTrace tailWord_1076680 prefixEnd_1076680 368569567388635145498963 := by
  unfold tailWord_1076680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19634872869689858574745747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26179830492919811432994329 19634872869689858574745747)
  ·
    refine ⟨29452309304534787862118621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19634872869689858574745747 29452309304534787862118621)
    ·
      refine ⟨11044615989200545448294483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29452309304534787862118621 11044615989200545448294483)
      ·
        refine ⟨16566923983800818172441725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11044615989200545448294483 16566923983800818172441725)
        ·
          refine ⟨6212596493925306814665647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16566923983800818172441725 6212596493925306814665647)
          ·
            refine ⟨9318894740887960221998471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6212596493925306814665647 9318894740887960221998471)
            ·
              refine ⟨13978342111331940332997707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9318894740887960221998471 13978342111331940332997707)
              ·
                refine ⟨20967513166997910499496561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13978342111331940332997707 20967513166997910499496561)
                ·
                  refine ⟨15725634875248432874622421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20967513166997910499496561 15725634875248432874622421)
                  ·
                    refine ⟨368569567388635145498963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15725634875248432874622421 368569567388635145498963)
                    ·
                      rfl

theorem cell22_1076680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1076680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076680 prefixEnd_1076680 := by exact prefixLift 1076680
  have htrace : WordTrace (prefixWord ++ tailWord_1076680) baseStart_1076680 baseEnd_1076680 := by
    simpa [prefixWord, tailWord_1076680, baseEnd_1076680] using wordTrace_append hprefix tailTrace_1076680
  have hstable : (prefixWord ++ tailWord_1076680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076680).length < 2 ^ (prefixWord ++ tailWord_1076680).sum := by decide
  have hdescent : baseEnd_1076680 < baseStart_1076680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076682 : List Nat := [3, 1, 2, 1, 2, 3, 4, 6]
def baseStart_1076682 : Nat := 118140960795 + 1076682 * 2 ^ 59
def prefixEnd_1076682 : Nat := 4983230072969 + 3 ^ 40 * 1076682 * 2
def baseEnd_1076682 : Nat := 40952250225500867438773

theorem tailTrace_1076682 : CollatzResearch.WordTrace tailWord_1076682 prefixEnd_1076682 40952250225500867438773 := by
  unfold tailWord_1076682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817454671343117872766075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26179879123581647660709533 9817454671343117872766075)
  ·
    refine ⟨14726182007014676809149113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817454671343117872766075 14726182007014676809149113)
    ·
      refine ⟨11044636505261007606861835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14726182007014676809149113 11044636505261007606861835)
      ·
        refine ⟨16566954757891511410292753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11044636505261007606861835 16566954757891511410292753)
        ·
          refine ⟨12425216068418633557719565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16566954757891511410292753 12425216068418633557719565)
          ·
            refine ⟨4659456025656987584144837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12425216068418633557719565 4659456025656987584144837)
            ·
              refine ⟨873648004810685172027157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4659456025656987584144837 873648004810685172027157)
              ·
                refine ⟨40952250225500867438773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 873648004810685172027157 40952250225500867438773)
                ·
                  rfl

theorem cell22_1076682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_1076682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076682 prefixEnd_1076682 := by exact prefixLift 1076682
  have htrace : WordTrace (prefixWord ++ tailWord_1076682) baseStart_1076682 baseEnd_1076682 := by
    simpa [prefixWord, tailWord_1076682, baseEnd_1076682] using wordTrace_append hprefix tailTrace_1076682
  have hstable : (prefixWord ++ tailWord_1076682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076682).length < 2 ^ (prefixWord ++ tailWord_1076682).sum := by decide
  have hdescent : baseEnd_1076682 < baseStart_1076682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076787 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 1, 5]
def baseStart_1076787 : Nat := 118140960795 + 1076787 * 2 ^ 59
def prefixEnd_1076787 : Nat := 4983230072969 + 3 ^ 40 * 1076787 * 2
def baseEnd_1076787 : Nat := 368606195675322533073635

theorem tailTrace_1076787 : CollatzResearch.WordTrace tailWord_1076787 prefixEnd_1076787 368606195675322533073635 := by
  unfold tailWord_1076787
  simp only [CollatzResearch.WordTrace]
  refine ⟨39273648349992074423636615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26182432233328049615757743 39273648349992074423636615)
  ·
    refine ⟨58910472524988111635454923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39273648349992074423636615 58910472524988111635454923)
    ·
      refine ⟨88365708787482167453182385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58910472524988111635454923 88365708787482167453182385)
      ·
        refine ⟨66274281590611625589886789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88365708787482167453182385 66274281590611625589886789)
        ·
          refine ⟨12426427798239679798103773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66274281590611625589886789 12426427798239679798103773)
          ·
            refine ⟨4659910424339879924288915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12426427798239679798103773 4659910424339879924288915)
            ·
              refine ⟨6989865636509819886433373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659910424339879924288915 6989865636509819886433373)
              ·
                refine ⟨2621199613691182457412515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6989865636509819886433373 2621199613691182457412515)
                ·
                  refine ⟨3931799420536773686118773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621199613691182457412515 3931799420536773686118773)
                  ·
                    refine ⟨368606195675322533073635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3931799420536773686118773 368606195675322533073635)
                    ·
                      rfl

theorem cell22_1076787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_1076787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076787 prefixEnd_1076787 := by exact prefixLift 1076787
  have htrace : WordTrace (prefixWord ++ tailWord_1076787) baseStart_1076787 baseEnd_1076787 := by
    simpa [prefixWord, tailWord_1076787, baseEnd_1076787] using wordTrace_append hprefix tailTrace_1076787
  have hstable : (prefixWord ++ tailWord_1076787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076787).length < 2 ^ (prefixWord ++ tailWord_1076787).sum := by decide
  have hdescent : baseEnd_1076787 < baseStart_1076787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076896 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 5]
def baseStart_1076896 : Nat := 118140960795 + 1076896 * 2 ^ 59
def prefixEnd_1076896 : Nat := 4983230072969 + 3 ^ 40 * 1076896 * 2
def baseEnd_1076896 : Nat := 122881169534294194032767

theorem tailTrace_1076896 : CollatzResearch.WordTrace tailWord_1076896 prefixEnd_1076896 122881169534294194032767 := by
  unfold tailWord_1076896
  simp only [CollatzResearch.WordTrace]
  refine ⟨19638811953298593019677271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26185082604398124026236361 19638811953298593019677271)
  ·
    refine ⟨29458217929947889529515907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19638811953298593019677271 29458217929947889529515907)
    ·
      refine ⟨44187326894921834294273861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29458217929947889529515907 44187326894921834294273861)
      ·
        refine ⟨8285123792797843930176349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44187326894921834294273861 8285123792797843930176349)
        ·
          refine ⟨3106921422299191473816131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8285123792797843930176349 3106921422299191473816131)
          ·
            refine ⟨4660382133448787210724197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106921422299191473816131 4660382133448787210724197)
            ·
              refine ⟨873821650021647602010787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4660382133448787210724197 873821650021647602010787)
              ·
                refine ⟨1310732475032471403016181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873821650021647602010787 1310732475032471403016181)
                ·
                  refine ⟨122881169534294194032767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1310732475032471403016181 122881169534294194032767)
                  ·
                    rfl

theorem cell22_1076896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_1076896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076896 prefixEnd_1076896 := by exact prefixLift 1076896
  have htrace : WordTrace (prefixWord ++ tailWord_1076896) baseStart_1076896 baseEnd_1076896 := by
    simpa [prefixWord, tailWord_1076896, baseEnd_1076896] using wordTrace_append hprefix tailTrace_1076896
  have hstable : (prefixWord ++ tailWord_1076896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076896).length < 2 ^ (prefixWord ++ tailWord_1076896).sum := by decide
  have hdescent : baseEnd_1076896 < baseStart_1076896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076934 : List Nat := [6, 1, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1076934 : Nat := 118140960795 + 1076934 * 2 ^ 59
def prefixEnd_1076934 : Nat := 4983230072969 + 3 ^ 40 * 1076934 * 2
def baseEnd_1076934 : Nat := 368656516779463149648185

theorem tailTrace_1076934 : CollatzResearch.WordTrace tailWord_1076934 prefixEnd_1076934 368656516779463149648185 := by
  unfold tailWord_1076934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1227469058764359954038683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26186006586973012352825237 1227469058764359954038683)
  ·
    refine ⟨1841203588146539931058025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1227469058764359954038683 1841203588146539931058025)
    ·
      refine ⟨1380902691109904948293519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1841203588146539931058025 1380902691109904948293519)
      ·
        refine ⟨2071354036664857422440279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380902691109904948293519 2071354036664857422440279)
        ·
          refine ⟨3107031054997286133660419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071354036664857422440279 3107031054997286133660419)
          ·
            refine ⟨4660546582495929200490629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107031054997286133660419 4660546582495929200490629)
            ·
              refine ⟨873852484217986725091993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4660546582495929200490629 873852484217986725091993)
              ·
                refine ⟨655389363163490043818995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873852484217986725091993 655389363163490043818995)
                ·
                  refine ⟨983084044745235065728493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655389363163490043818995 983084044745235065728493)
                  ·
                    refine ⟨368656516779463149648185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983084044745235065728493 368656516779463149648185)
                    ·
                      rfl

theorem cell22_1076934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1076934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076934 prefixEnd_1076934 := by exact prefixLift 1076934
  have htrace : WordTrace (prefixWord ++ tailWord_1076934) baseStart_1076934 baseEnd_1076934 := by
    simpa [prefixWord, tailWord_1076934, baseEnd_1076934] using wordTrace_append hprefix tailTrace_1076934
  have hstable : (prefixWord ++ tailWord_1076934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076934).length < 2 ^ (prefixWord ++ tailWord_1076934).sum := by decide
  have hdescent : baseEnd_1076934 < baseStart_1076934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076939 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 4, 3]
def baseStart_1076939 : Nat := 118140960795 + 1076939 * 2 ^ 59
def prefixEnd_1076939 : Nat := 4983230072969 + 3 ^ 40 * 1076939 * 2
def baseEnd_1076939 : Nat := 368658228381644803273169

theorem tailTrace_1076939 : CollatzResearch.WordTrace tailWord_1076939 prefixEnd_1076939 368658228381644803273169 := by
  unfold tailWord_1076939
  simp only [CollatzResearch.WordTrace]
  refine ⟨39279192245441404383169871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26186128163627602922113247 39279192245441404383169871)
  ·
    refine ⟨58918788368162106574754807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39279192245441404383169871 58918788368162106574754807)
    ·
      refine ⟨88378182552243159862132211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58918788368162106574754807 88378182552243159862132211)
      ·
        refine ⟨132567273828364739793198317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88378182552243159862132211 132567273828364739793198317)
        ·
          refine ⟨49712727685636777422449369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132567273828364739793198317 49712727685636777422449369)
          ·
            refine ⟨37284545764227583066837027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49712727685636777422449369 37284545764227583066837027)
            ·
              refine ⟨55926818646341374600255541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37284545764227583066837027 55926818646341374600255541)
              ·
                refine ⟨5243139248094503868773957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55926818646341374600255541 5243139248094503868773957)
                ·
                  refine ⟨983088609017719475395117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5243139248094503868773957 983088609017719475395117)
                  ·
                    refine ⟨368658228381644803273169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983088609017719475395117 368658228381644803273169)
                    ·
                      rfl

theorem cell22_1076939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 3].length) (baseStart_1076939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1076939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1076939 prefixEnd_1076939 := by exact prefixLift 1076939
  have htrace : WordTrace (prefixWord ++ tailWord_1076939) baseStart_1076939 baseEnd_1076939 := by
    simpa [prefixWord, tailWord_1076939, baseEnd_1076939] using wordTrace_append hprefix tailTrace_1076939
  have hstable : (prefixWord ++ tailWord_1076939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076939).length < 2 ^ (prefixWord ++ tailWord_1076939).sum := by decide
  have hdescent : baseEnd_1076939 < baseStart_1076939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077119 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 2, 7]
def baseStart_1077119 : Nat := 118140960795 + 1077119 * 2 ^ 59
def prefixEnd_1077119 : Nat := 4983230072969 + 3 ^ 40 * 1077119 * 2
def baseEnd_1077119 : Nat := 368719846060184333772617

theorem tailTrace_1077119 : CollatzResearch.WordTrace tailWord_1077119 prefixEnd_1077119 368719846060184333772617 := by
  unfold tailWord_1077119
  simp only [CollatzResearch.WordTrace]
  refine ⟨39285757384789295124722411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26190504923192863416481607 39285757384789295124722411)
  ·
    refine ⟨58928636077183942687083617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39285757384789295124722411 58928636077183942687083617)
    ·
      refine ⟨44196477057887957015312713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58928636077183942687083617 44196477057887957015312713)
      ·
        refine ⟨33147357793415967761484535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44196477057887957015312713 33147357793415967761484535)
        ·
          refine ⟨49721036690123951642226803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33147357793415967761484535 49721036690123951642226803)
          ·
            refine ⟨74581555035185927463340205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49721036690123951642226803 74581555035185927463340205)
            ·
              refine ⟨27968083138194722798752577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74581555035185927463340205 27968083138194722798752577)
              ·
                refine ⟨20976062353646042099064433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27968083138194722798752577 20976062353646042099064433)
                ·
                  refine ⟨15732046765234531574298325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20976062353646042099064433 15732046765234531574298325)
                  ·
                    refine ⟨368719846060184333772617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15732046765234531574298325 368719846060184333772617)
                    ·
                      rfl

theorem cell22_1077119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_1077119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077119 prefixEnd_1077119 := by exact prefixLift 1077119
  have htrace : WordTrace (prefixWord ++ tailWord_1077119) baseStart_1077119 baseEnd_1077119 := by
    simpa [prefixWord, tailWord_1077119, baseEnd_1077119] using wordTrace_append hprefix tailTrace_1077119
  have hstable : (prefixWord ++ tailWord_1077119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077119).length < 2 ^ (prefixWord ++ tailWord_1077119).sum := by decide
  have hdescent : baseEnd_1077119 < baseStart_1077119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077136 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 5, 3]
def baseStart_1077136 : Nat := 118140960795 + 1077136 * 2 ^ 59
def prefixEnd_1077136 : Nat := 4983230072969 + 3 ^ 40 * 1077136 * 2
def baseEnd_1077136 : Nat := 368725665507601956097565

theorem tailTrace_1077136 : CollatzResearch.WordTrace tailWord_1077136 prefixEnd_1077136 368725665507601956097565 := by
  unfold tailWord_1077136
  simp only [CollatzResearch.WordTrace]
  refine ⟨19643188712863853514045631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26190918283818471352060841 19643188712863853514045631)
  ·
    refine ⟨29464783069295780271068447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19643188712863853514045631 29464783069295780271068447)
    ·
      refine ⟨44197174603943670406602671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29464783069295780271068447 44197174603943670406602671)
      ·
        refine ⟨66295761905915505609904007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44197174603943670406602671 66295761905915505609904007)
        ·
          refine ⟨99443642858873258414856011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66295761905915505609904007 99443642858873258414856011)
          ·
            refine ⟨149165464288309887622284017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99443642858873258414856011 149165464288309887622284017)
            ·
              refine ⟨111874098216232415716713013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149165464288309887622284017 111874098216232415716713013)
              ·
                refine ⟨10488196707771788973441845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111874098216232415716713013 10488196707771788973441845)
                ·
                  refine ⟨983268441353605216260173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10488196707771788973441845 983268441353605216260173)
                  ·
                    refine ⟨368725665507601956097565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983268441353605216260173 368725665507601956097565)
                    ·
                      rfl

theorem cell22_1077136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_1077136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077136 prefixEnd_1077136 := by exact prefixLift 1077136
  have htrace : WordTrace (prefixWord ++ tailWord_1077136) baseStart_1077136 baseEnd_1077136 := by
    simpa [prefixWord, tailWord_1077136, baseEnd_1077136] using wordTrace_append hprefix tailTrace_1077136
  have hstable : (prefixWord ++ tailWord_1077136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077136).length < 2 ^ (prefixWord ++ tailWord_1077136).sum := by decide
  have hdescent : baseEnd_1077136 < baseStart_1077136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077140 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1077140 : Nat := 118140960795 + 1077140 * 2 ^ 59
def prefixEnd_1077140 : Nat := 4983230072969 + 3 ^ 40 * 1077140 * 2
def baseEnd_1077140 : Nat := 368727034789347278997553

theorem tailTrace_1077140 : CollatzResearch.WordTrace tailWord_1077140 prefixEnd_1077140 368727034789347278997553 := by
  unfold tailWord_1077140
  simp only [CollatzResearch.WordTrace]
  refine ⟨19643261658856607855618437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26191015545142143807491249 19643261658856607855618437)
  ·
    refine ⟨3683111561035613972928457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19643261658856607855618437 3683111561035613972928457)
    ·
      refine ⟨2762333670776710479696343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3683111561035613972928457 2762333670776710479696343)
      ·
        refine ⟨4143500506165065719544515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762333670776710479696343 4143500506165065719544515)
        ·
          refine ⟨6215250759247598579316773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143500506165065719544515 6215250759247598579316773)
          ·
            refine ⟨1165359517358924733621895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6215250759247598579316773 1165359517358924733621895)
            ·
              refine ⟨1748039276038387100432843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165359517358924733621895 1748039276038387100432843)
              ·
                refine ⟨2622058914057580650649265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748039276038387100432843 2622058914057580650649265)
                ·
                  refine ⟨1966544185543185487986949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2622058914057580650649265 1966544185543185487986949)
                  ·
                    refine ⟨368727034789347278997553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1966544185543185487986949 368727034789347278997553)
                    ·
                      rfl

theorem cell22_1077140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1077140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077140 prefixEnd_1077140 := by exact prefixLift 1077140
  have htrace : WordTrace (prefixWord ++ tailWord_1077140) baseStart_1077140 baseEnd_1077140 := by
    simpa [prefixWord, tailWord_1077140, baseEnd_1077140] using wordTrace_append hprefix tailTrace_1077140
  have hstable : (prefixWord ++ tailWord_1077140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077140).length < 2 ^ (prefixWord ++ tailWord_1077140).sum := by decide
  have hdescent : baseEnd_1077140 < baseStart_1077140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077183 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 5]
def baseStart_1077183 : Nat := 118140960795 + 1077183 * 2 ^ 59
def prefixEnd_1077183 : Nat := 4983230072969 + 3 ^ 40 * 1077183 * 2
def baseEnd_1077183 : Nat := 122913918189369833390807

theorem tailTrace_1077183 : CollatzResearch.WordTrace tailWord_1077183 prefixEnd_1077183 122913918189369833390807 := by
  unfold tailWord_1077183
  simp only [CollatzResearch.WordTrace]
  refine ⟨39288091656557434055052203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26192061104371622703368135 39288091656557434055052203)
  ·
    refine ⟨58932137484836151082578305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39288091656557434055052203 58932137484836151082578305)
    ·
      refine ⟨44199103113627113311933729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58932137484836151082578305 44199103113627113311933729)
      ·
        refine ⟨33149327335220334983950297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44199103113627113311933729 33149327335220334983950297)
        ·
          refine ⟨24861995501415251237962723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33149327335220334983950297 24861995501415251237962723)
          ·
            refine ⟨37292993252122876856944085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24861995501415251237962723 37292993252122876856944085)
            ·
              refine ⟨874054529346629926334627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37292993252122876856944085 874054529346629926334627)
              ·
                refine ⟨1311081794019944889501941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874054529346629926334627 1311081794019944889501941)
                ·
                  refine ⟨122913918189369833390807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1311081794019944889501941 122913918189369833390807)
                  ·
                    rfl

theorem cell22_1077183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 5].length) (baseStart_1077183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077183 prefixEnd_1077183 := by exact prefixLift 1077183
  have htrace : WordTrace (prefixWord ++ tailWord_1077183) baseStart_1077183 baseEnd_1077183 := by
    simpa [prefixWord, tailWord_1077183, baseEnd_1077183] using wordTrace_append hprefix tailTrace_1077183
  have hstable : (prefixWord ++ tailWord_1077183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077183).length < 2 ^ (prefixWord ++ tailWord_1077183).sum := by decide
  have hdescent : baseEnd_1077183 < baseStart_1077183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077228 : List Nat := [2, 2, 1, 1, 2, 1, 1, 8, 4]
def baseStart_1077228 : Nat := 118140960795 + 1077228 * 2 ^ 59
def prefixEnd_1077228 : Nat := 4983230072969 + 3 ^ 40 * 1077228 * 2
def baseEnd_1077228 : Nat := 122919052995914794265761

theorem tailTrace_1077228 : CollatzResearch.WordTrace tailWord_1077228 prefixEnd_1077228 122919052995914794265761 := by
  unfold tailWord_1077228
  simp only [CollatzResearch.WordTrace]
  refine ⟨19644866470697203370220169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26193155294262937826960225 19644866470697203370220169)
  ·
    refine ⟨14733649853022902527665127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19644866470697203370220169 14733649853022902527665127)
    ·
      refine ⟨22100474779534353791497691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14733649853022902527665127 22100474779534353791497691)
      ·
        refine ⟨33150712169301530687246537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22100474779534353791497691 33150712169301530687246537)
        ·
          refine ⟨24863034126976148015434903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33150712169301530687246537 24863034126976148015434903)
          ·
            refine ⟨37294551190464222023152355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24863034126976148015434903 37294551190464222023152355)
            ·
              refine ⟨55941826785696333034728533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37294551190464222023152355 55941826785696333034728533)
              ·
                refine ⟨655568282644878902750725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 55941826785696333034728533 655568282644878902750725)
                ·
                  refine ⟨122919052995914794265761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655568282644878902750725 122919052995914794265761)
                  ·
                    rfl

theorem cell22_1077228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_1077228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077228 prefixEnd_1077228 := by exact prefixLift 1077228
  have htrace : WordTrace (prefixWord ++ tailWord_1077228) baseStart_1077228 baseEnd_1077228 := by
    simpa [prefixWord, tailWord_1077228, baseEnd_1077228] using wordTrace_append hprefix tailTrace_1077228
  have hstable : (prefixWord ++ tailWord_1077228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077228).length < 2 ^ (prefixWord ++ tailWord_1077228).sum := by decide
  have hdescent : baseEnd_1077228 < baseStart_1077228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077256 : List Nat := [2, 1, 3, 2, 1, 2, 1, 10]
def baseStart_1077256 : Nat := 118140960795 + 1077256 * 2 ^ 59
def prefixEnd_1077256 : Nat := 4983230072969 + 3 ^ 40 * 1077256 * 2
def baseEnd_1077256 : Nat := 40974082662217960344133

theorem tailTrace_1077256 : CollatzResearch.WordTrace tailWord_1077256 prefixEnd_1077256 40974082662217960344133 := by
  unfold tailWord_1077256
  simp only [CollatzResearch.WordTrace]
  refine ⟨19645377092646483761229811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26193836123528645014973081 19645377092646483761229811)
  ·
    refine ⟨29468065638969725641844717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19645377092646483761229811 29468065638969725641844717)
    ·
      refine ⟨11050524614613647115691769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29468065638969725641844717 11050524614613647115691769)
      ·
        refine ⟨8287893460960235336768827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11050524614613647115691769 8287893460960235336768827)
        ·
          refine ⟨12431840191440353005153241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8287893460960235336768827 12431840191440353005153241)
          ·
            refine ⟨9323880143580264753864931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12431840191440353005153241 9323880143580264753864931)
            ·
              refine ⟨13985820215370397130797397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9323880143580264753864931 13985820215370397130797397)
              ·
                refine ⟨40974082662217960344133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13985820215370397130797397 40974082662217960344133)
                ·
                  rfl

theorem cell22_1077256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_1077256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077256 prefixEnd_1077256 := by exact prefixLift 1077256
  have htrace : WordTrace (prefixWord ++ tailWord_1077256) baseStart_1077256 baseEnd_1077256 := by
    simpa [prefixWord, tailWord_1077256, baseEnd_1077256] using wordTrace_append hprefix tailTrace_1077256
  have hstable : (prefixWord ++ tailWord_1077256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077256).length < 2 ^ (prefixWord ++ tailWord_1077256).sum := by decide
  have hdescent : baseEnd_1077256 < baseStart_1077256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077277 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1077277 : Nat := 118140960795 + 1077277 * 2 ^ 59
def prefixEnd_1077277 : Nat := 4983230072969 + 3 ^ 40 * 1077277 * 2
def baseEnd_1077277 : Nat := 368773932689124588322133

theorem tailTrace_1077277 : CollatzResearch.WordTrace tailWord_1077277 prefixEnd_1077277 368773932689124588322133 := by
  unfold tailWord_1077277
  simp only [CollatzResearch.WordTrace]
  refine ⟨39291520118216888108974085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26194346745477925405982723 39291520118216888108974085)
  ·
    refine ⟨7367160022165666520432641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39291520118216888108974085 7367160022165666520432641)
    ·
      refine ⟨5525370016624249890324481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7367160022165666520432641 5525370016624249890324481)
      ·
        refine ⟨4144027512468187417743361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5525370016624249890324481 4144027512468187417743361)
        ·
          refine ⟨3108020634351140563307521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4144027512468187417743361 3108020634351140563307521)
          ·
            refine ⟨2331015475763355422480641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3108020634351140563307521 2331015475763355422480641)
            ·
              refine ⟨1748261606822516566860481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331015475763355422480641 1748261606822516566860481)
              ·
                refine ⟨1311196205116887425145361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1748261606822516566860481 1311196205116887425145361)
                ·
                  refine ⟨983397153837665568859021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1311196205116887425145361 983397153837665568859021)
                  ·
                    refine ⟨368773932689124588322133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983397153837665568859021 368773932689124588322133)
                    ·
                      rfl

theorem cell22_1077277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1077277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077277 prefixEnd_1077277 := by exact prefixLift 1077277
  have htrace : WordTrace (prefixWord ++ tailWord_1077277) baseStart_1077277 baseEnd_1077277 := by
    simpa [prefixWord, tailWord_1077277, baseEnd_1077277] using wordTrace_append hprefix tailTrace_1077277
  have hstable : (prefixWord ++ tailWord_1077277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077277).length < 2 ^ (prefixWord ++ tailWord_1077277).sum := by decide
  have hdescent : baseEnd_1077277 < baseStart_1077277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077290 : List Nat := [3, 1, 4, 1, 2, 3, 1, 7]
def baseStart_1077290 : Nat := 118140960795 + 1077290 * 2 ^ 59
def prefixEnd_1077290 : Nat := 4983230072969 + 3 ^ 40 * 1077290 * 2
def baseEnd_1077290 : Nat := 40975375872755209749677

theorem tailTrace_1077290 : CollatzResearch.WordTrace tailWord_1077290 prefixEnd_1077290 40975375872755209749677 := by
  unfold tailWord_1077290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822998566792447832299331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26194662844779860886131549 9822998566792447832299331)
  ·
    refine ⟨14734497850188671748448997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9822998566792447832299331 14734497850188671748448997)
    ·
      refine ⟨2762718346910375952834187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14734497850188671748448997 2762718346910375952834187)
      ·
        refine ⟨4144077520365563929251281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762718346910375952834187 4144077520365563929251281)
        ·
          refine ⟨3108058140274172946938461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4144077520365563929251281 3108058140274172946938461)
          ·
            refine ⟨1165521802602814855101923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3108058140274172946938461 1165521802602814855101923)
            ·
              refine ⟨1748282703904222282652885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165521802602814855101923 1748282703904222282652885)
              ·
                refine ⟨40975375872755209749677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1748282703904222282652885 40975375872755209749677)
                ·
                  rfl

theorem cell22_1077290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_1077290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077290 prefixEnd_1077290 := by exact prefixLift 1077290
  have htrace : WordTrace (prefixWord ++ tailWord_1077290) baseStart_1077290 baseEnd_1077290 := by
    simpa [prefixWord, tailWord_1077290, baseEnd_1077290] using wordTrace_append hprefix tailTrace_1077290
  have hstable : (prefixWord ++ tailWord_1077290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077290).length < 2 ^ (prefixWord ++ tailWord_1077290).sum := by decide
  have hdescent : baseEnd_1077290 < baseStart_1077290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077331 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 10]
def baseStart_1077331 : Nat := 118140960795 + 1077331 * 2 ^ 59
def prefixEnd_1077331 : Nat := 4983230072969 + 3 ^ 40 * 1077331 * 2
def baseEnd_1077331 : Nat := 368792417992686447471967

theorem tailTrace_1077331 : CollatzResearch.WordTrace tailWord_1077331 prefixEnd_1077331 368792417992686447471967 := by
  unfold tailWord_1077331
  simp only [CollatzResearch.WordTrace]
  refine ⟨39293489660021255331439847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26195659773347503554293231 39293489660021255331439847)
  ·
    refine ⟨58940234490031882997159771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39293489660021255331439847 58940234490031882997159771)
    ·
      refine ⟨88410351735047824495739657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58940234490031882997159771 88410351735047824495739657)
      ·
        refine ⟨66307763801285868371804743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88410351735047824495739657 66307763801285868371804743)
        ·
          refine ⟨99461645701928802557707115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66307763801285868371804743 99461645701928802557707115)
          ·
            refine ⟨149192468552893203836560673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99461645701928802557707115 149192468552893203836560673)
            ·
              refine ⟨111894351414669902877420505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149192468552893203836560673 111894351414669902877420505)
              ·
                refine ⟨83920763561002427158065379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111894351414669902877420505 83920763561002427158065379)
                ·
                  refine ⟨125881145341503640737098069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83920763561002427158065379 125881145341503640737098069)
                  ·
                    refine ⟨368792417992686447471967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 125881145341503640737098069 368792417992686447471967)
                    ·
                      rfl

theorem cell22_1077331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_1077331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077331 prefixEnd_1077331 := by exact prefixLift 1077331
  have htrace : WordTrace (prefixWord ++ tailWord_1077331) baseStart_1077331 baseEnd_1077331 := by
    simpa [prefixWord, tailWord_1077331, baseEnd_1077331] using wordTrace_append hprefix tailTrace_1077331
  have hstable : (prefixWord ++ tailWord_1077331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077331).length < 2 ^ (prefixWord ++ tailWord_1077331).sum := by decide
  have hdescent : baseEnd_1077331 < baseStart_1077331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077333 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1077333 : Nat := 118140960795 + 1077333 * 2 ^ 59
def prefixEnd_1077333 : Nat := 4983230072969 + 3 ^ 40 * 1077333 * 2
def baseEnd_1077333 : Nat := 368793102633559108921961

theorem tailTrace_1077333 : CollatzResearch.WordTrace tailWord_1077333 prefixEnd_1077333 368793102633559108921961 := by
  unfold tailWord_1077333
  simp only [CollatzResearch.WordTrace]
  refine ⟨39293562606014009673012653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26195708404009339782008435 39293562606014009673012653)
  ·
    refine ⟨14735085977255253627379745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39293562606014009673012653 14735085977255253627379745)
    ·
      refine ⟨11051314482941440220534809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14735085977255253627379745 11051314482941440220534809)
      ·
        refine ⟨8288485862206080165401107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11051314482941440220534809 8288485862206080165401107)
        ·
          refine ⟨12432728793309120248101661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8288485862206080165401107 12432728793309120248101661)
          ·
            refine ⟨4662273297490920093038123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12432728793309120248101661 4662273297490920093038123)
            ·
              refine ⟨6993409946236380139557185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4662273297490920093038123 6993409946236380139557185)
              ·
                refine ⟨5245057459677285104667889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6993409946236380139557185 5245057459677285104667889)
                ·
                  refine ⟨3933793094757963828500917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5245057459677285104667889 3933793094757963828500917)
                  ·
                    refine ⟨368793102633559108921961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3933793094757963828500917 368793102633559108921961)
                    ·
                      rfl

theorem cell22_1077333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1077333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077333 prefixEnd_1077333 := by exact prefixLift 1077333
  have htrace : WordTrace (prefixWord ++ tailWord_1077333) baseStart_1077333 baseEnd_1077333 := by
    simpa [prefixWord, tailWord_1077333, baseEnd_1077333] using wordTrace_append hprefix tailTrace_1077333
  have hstable : (prefixWord ++ tailWord_1077333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077333).length < 2 ^ (prefixWord ++ tailWord_1077333).sum := by decide
  have hdescent : baseEnd_1077333 < baseStart_1077333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077348 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1077348 : Nat := 118140960795 + 1077348 * 2 ^ 59
def prefixEnd_1077348 : Nat := 4983230072969 + 3 ^ 40 * 1077348 * 2
def baseEnd_1077348 : Nat := 368798237440104069796915

theorem tailTrace_1077348 : CollatzResearch.WordTrace tailWord_1077348 prefixEnd_1077348 368798237440104069796915 := by
  unfold tailWord_1077348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19647054850479833617404349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26196073133973111489872465 19647054850479833617404349)
  ·
    refine ⟨7367645568929937606526631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19647054850479833617404349 7367645568929937606526631)
    ·
      refine ⟨11051468353394906409789947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7367645568929937606526631 11051468353394906409789947)
      ·
        refine ⟨16577202530092359614684921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11051468353394906409789947 16577202530092359614684921)
        ·
          refine ⟨12432901897569269711013691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16577202530092359614684921 12432901897569269711013691)
          ·
            refine ⟨18649352846353904566520537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12432901897569269711013691 18649352846353904566520537)
            ·
              refine ⟨13987014634765428424890403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18649352846353904566520537 13987014634765428424890403)
              ·
                refine ⟨20980521952148142637335605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13987014634765428424890403 20980521952148142637335605)
                ·
                  refine ⟨1966923933013888372250213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20980521952148142637335605 1966923933013888372250213)
                  ·
                    refine ⟨368798237440104069796915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1966923933013888372250213 368798237440104069796915)
                    ·
                      rfl

theorem cell22_1077348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1077348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077348 prefixEnd_1077348 := by exact prefixLift 1077348
  have htrace : WordTrace (prefixWord ++ tailWord_1077348) baseStart_1077348 baseEnd_1077348 := by
    simpa [prefixWord, tailWord_1077348, baseEnd_1077348] using wordTrace_append hprefix tailTrace_1077348
  have hstable : (prefixWord ++ tailWord_1077348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077348).length < 2 ^ (prefixWord ++ tailWord_1077348).sum := by decide
  have hdescent : baseEnd_1077348 < baseStart_1077348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077395 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 2, 3]
def baseStart_1077395 : Nat := 118140960795 + 1077395 * 2 ^ 59
def prefixEnd_1077395 : Nat := 4983230072969 + 3 ^ 40 * 1077395 * 2
def baseEnd_1077395 : Nat := 368814326500611613871771

theorem tailTrace_1077395 : CollatzResearch.WordTrace tailWord_1077395 prefixEnd_1077395 368814326500611613871771 := by
  unfold tailWord_1077395
  simp only [CollatzResearch.WordTrace]
  refine ⟨39295823931789394261769639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26197215954526262841179759 39295823931789394261769639)
  ·
    refine ⟨58943735897684091392654459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39295823931789394261769639 58943735897684091392654459)
    ·
      refine ⟨88415603846526137088981689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58943735897684091392654459 88415603846526137088981689)
      ·
        refine ⟨66311702884894602816736267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88415603846526137088981689 66311702884894602816736267)
        ·
          refine ⟨99467554327341904225104401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66311702884894602816736267 99467554327341904225104401)
          ·
            refine ⟨74600665745506428168828301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99467554327341904225104401 74600665745506428168828301)
            ·
              refine ⟨27975249654564910563310613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74600665745506428168828301 27975249654564910563310613)
              ·
                refine ⟨1311339827557730182655185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27975249654564910563310613 1311339827557730182655185)
                ·
                  refine ⟨983504870668297636991389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1311339827557730182655185 983504870668297636991389)
                  ·
                    refine ⟨368814326500611613871771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983504870668297636991389 368814326500611613871771)
                    ·
                      rfl

theorem cell22_1077395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 3].length) (baseStart_1077395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077395 prefixEnd_1077395 := by exact prefixLift 1077395
  have htrace : WordTrace (prefixWord ++ tailWord_1077395) baseStart_1077395 baseEnd_1077395 := by
    simpa [prefixWord, tailWord_1077395, baseEnd_1077395] using wordTrace_append hprefix tailTrace_1077395
  have hstable : (prefixWord ++ tailWord_1077395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077395).length < 2 ^ (prefixWord ++ tailWord_1077395).sum := by decide
  have hdescent : baseEnd_1077395 < baseStart_1077395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077397 : List Nat := [1, 3, 2, 1, 1, 1, 7, 2, 4]
def baseStart_1077397 : Nat := 118140960795 + 1077397 * 2 ^ 59
def prefixEnd_1077397 : Nat := 4983230072969 + 3 ^ 40 * 1077397 * 2
def baseEnd_1077397 : Nat := 122938337047161425107255

theorem tailTrace_1077397 : CollatzResearch.WordTrace tailWord_1077397 prefixEnd_1077397 122938337047161425107255 := by
  unfold tailWord_1077397
  simp only [CollatzResearch.WordTrace]
  refine ⟨39295896877782148603342445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26197264585188099068894963 39295896877782148603342445)
  ·
    refine ⟨14735961329168305726253417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39295896877782148603342445 14735961329168305726253417)
    ·
      refine ⟨11051970996876229294690063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14735961329168305726253417 11051970996876229294690063)
      ·
        refine ⟨16577956495314343942035095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11051970996876229294690063 16577956495314343942035095)
        ·
          refine ⟨24866934742971515913052643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16577956495314343942035095 24866934742971515913052643)
          ·
            refine ⟨37300402114457273869578965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24866934742971515913052643 37300402114457273869578965)
            ·
              refine ⟨874228174557592356318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37300402114457273869578965 874228174557592356318257)
              ·
                refine ⟨655671130918194267238693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874228174557592356318257 655671130918194267238693)
                ·
                  refine ⟨122938337047161425107255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655671130918194267238693 122938337047161425107255)
                  ·
                    rfl

theorem cell22_1077397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_1077397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077397 prefixEnd_1077397 := by exact prefixLift 1077397
  have htrace : WordTrace (prefixWord ++ tailWord_1077397) baseStart_1077397 baseEnd_1077397 := by
    simpa [prefixWord, tailWord_1077397, baseEnd_1077397] using wordTrace_append hprefix tailTrace_1077397
  have hstable : (prefixWord ++ tailWord_1077397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077397).length < 2 ^ (prefixWord ++ tailWord_1077397).sum := by decide
  have hdescent : baseEnd_1077397 < baseStart_1077397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077408 : List Nat := [2, 1, 1, 4, 2, 2, 1, 9]
def baseStart_1077408 : Nat := 118140960795 + 1077408 * 2 ^ 59
def prefixEnd_1077408 : Nat := 4983230072969 + 3 ^ 40 * 1077408 * 2
def baseEnd_1077408 : Nat := 40979864074031545921859

theorem tailTrace_1077408 : CollatzResearch.WordTrace tailWord_1077408 prefixEnd_1077408 40979864074031545921859 := by
  unfold tailWord_1077408
  simp only [CollatzResearch.WordTrace]
  refine ⟨19648149040371148740996439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26197532053828198321328585 19648149040371148740996439)
  ·
    refine ⟨29472223560556723111494659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19648149040371148740996439 29472223560556723111494659)
    ·
      refine ⟨44208335340835084667241989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29472223560556723111494659 44208335340835084667241989)
      ·
        refine ⟨8289062876406578375107873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44208335340835084667241989 8289062876406578375107873)
        ·
          refine ⟨6216797157304933781330905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8289062876406578375107873 6216797157304933781330905)
          ·
            refine ⟨4662597867978700335998179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6216797157304933781330905 4662597867978700335998179)
            ·
              refine ⟨6993896801968050503997269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4662597867978700335998179 6993896801968050503997269)
              ·
                refine ⟨40979864074031545921859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6993896801968050503997269 40979864074031545921859)
                ·
                  rfl

theorem cell22_1077408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_1077408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077408 prefixEnd_1077408 := by exact prefixLift 1077408
  have htrace : WordTrace (prefixWord ++ tailWord_1077408) baseStart_1077408 baseEnd_1077408 := by
    simpa [prefixWord, tailWord_1077408, baseEnd_1077408] using wordTrace_append hprefix tailTrace_1077408
  have hstable : (prefixWord ++ tailWord_1077408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077408).length < 2 ^ (prefixWord ++ tailWord_1077408).sum := by decide
  have hdescent : baseEnd_1077408 < baseStart_1077408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077442 : List Nat := [3, 5, 1, 1, 1, 11]
def baseStart_1077442 : Nat := 118140960795 + 1077442 * 2 ^ 59
def prefixEnd_1077442 : Nat := 4983230072969 + 3 ^ 40 * 1077442 * 2
def baseEnd_1077442 : Nat := 4553461920507643925267

theorem tailTrace_1077442 : CollatzResearch.WordTrace tailWord_1077442 prefixEnd_1077442 4553461920507643925267 := by
  unfold tailWord_1077442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824384540654780322182645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26198358775079414192487053 9824384540654780322182645)
  ·
    refine ⟨921036050686385655204623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9824384540654780322182645 921036050686385655204623)
    ·
      refine ⟨1381554076029578482806935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 921036050686385655204623 1381554076029578482806935)
      ·
        refine ⟨2072331114044367724210403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381554076029578482806935 2072331114044367724210403)
        ·
          refine ⟨3108496671066551586315605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072331114044367724210403 3108496671066551586315605)
          ·
            refine ⟨4553461920507643925267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3108496671066551586315605 4553461920507643925267)
            ·
              rfl

theorem cell22_1077442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 11].length) (baseStart_1077442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077442 prefixEnd_1077442 := by exact prefixLift 1077442
  have htrace : WordTrace (prefixWord ++ tailWord_1077442) baseStart_1077442 baseEnd_1077442 := by
    simpa [prefixWord, tailWord_1077442, baseEnd_1077442] using wordTrace_append hprefix tailTrace_1077442
  have hstable : (prefixWord ++ tailWord_1077442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077442).length < 2 ^ (prefixWord ++ tailWord_1077442).sum := by decide
  have hdescent : baseEnd_1077442 < baseStart_1077442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077515 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 6]
def baseStart_1077515 : Nat := 118140960795 + 1077515 * 2 ^ 59
def prefixEnd_1077515 : Nat := 4983230072969 + 3 ^ 40 * 1077515 * 2
def baseEnd_1077515 : Nat := 122951801650990433623801

theorem tailTrace_1077515 : CollatzResearch.WordTrace tailWord_1077515 prefixEnd_1077515 122951801650990433623801 := by
  unfold tailWord_1077515
  simp only [CollatzResearch.WordTrace]
  refine ⟨39300200691354654756137999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26200133794236436504091999 39300200691354654756137999)
  ·
    refine ⟨58950301037031982134206999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39300200691354654756137999 58950301037031982134206999)
    ·
      refine ⟨88425451555547973201310499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58950301037031982134206999 88425451555547973201310499)
      ·
        refine ⟨132638177333321959801965749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88425451555547973201310499 132638177333321959801965749)
        ·
          refine ⟨12434829124998933731434289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132638177333321959801965749 12434829124998933731434289)
          ·
            refine ⟨9326121843749200298575717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12434829124998933731434289 9326121843749200298575717)
            ·
              refine ⟨1748647845702975055982947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9326121843749200298575717 1748647845702975055982947)
              ·
                refine ⟨2622971768554462583974421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748647845702975055982947 2622971768554462583974421)
                ·
                  refine ⟨122951801650990433623801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2622971768554462583974421 122951801650990433623801)
                  ·
                    rfl

theorem cell22_1077515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 6].length) (baseStart_1077515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077515 prefixEnd_1077515 := by exact prefixLift 1077515
  have htrace : WordTrace (prefixWord ++ tailWord_1077515) baseStart_1077515 baseEnd_1077515 := by
    simpa [prefixWord, tailWord_1077515, baseEnd_1077515] using wordTrace_append hprefix tailTrace_1077515
  have hstable : (prefixWord ++ tailWord_1077515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077515).length < 2 ^ (prefixWord ++ tailWord_1077515).sum := by decide
  have hdescent : baseEnd_1077515 < baseStart_1077515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077562 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_1077562 : Nat := 118140960795 + 1077562 * 2 ^ 59
def prefixEnd_1077562 : Nat := 4983230072969 + 3 ^ 40 * 1077562 * 2
def baseEnd_1077562 : Nat := 368871494013478844946259

theorem tailTrace_1077562 : CollatzResearch.WordTrace tailWord_1077562 prefixEnd_1077562 368871494013478844946259 := by
  unfold tailWord_1077562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825478730546095445774735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26201276614789587855399293 9825478730546095445774735)
  ·
    refine ⟨14738218095819143168662103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9825478730546095445774735 14738218095819143168662103)
    ·
      refine ⟨22107327143728714752993155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14738218095819143168662103 22107327143728714752993155)
      ·
        refine ⟨33160990715593072129489733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22107327143728714752993155 33160990715593072129489733)
        ·
          refine ⟨6217685759173701024279325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33160990715593072129489733 6217685759173701024279325)
          ·
            refine ⟨2331632159690137884104747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6217685759173701024279325 2331632159690137884104747)
            ·
              refine ⟨3497448239535206826157121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331632159690137884104747 3497448239535206826157121)
              ·
                refine ⟨2623086179651405119617841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497448239535206826157121 2623086179651405119617841)
                ·
                  refine ⟨1967314634738553839713381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623086179651405119617841 1967314634738553839713381)
                  ·
                    refine ⟨368871494013478844946259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1967314634738553839713381 368871494013478844946259)
                    ·
                      rfl

theorem cell22_1077562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_1077562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077562 prefixEnd_1077562 := by exact prefixLift 1077562
  have htrace : WordTrace (prefixWord ++ tailWord_1077562) baseStart_1077562 baseEnd_1077562 := by
    simpa [prefixWord, tailWord_1077562, baseEnd_1077562] using wordTrace_append hprefix tailTrace_1077562
  have hstable : (prefixWord ++ tailWord_1077562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077562).length < 2 ^ (prefixWord ++ tailWord_1077562).sum := by decide
  have hdescent : baseEnd_1077562 < baseStart_1077562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077566 : List Nat := [4, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1077566 : Nat := 118140960795 + 1077566 * 2 ^ 59
def prefixEnd_1077566 : Nat := 4983230072969 + 3 ^ 40 * 1077566 * 2
def baseEnd_1077566 : Nat := 122957621098408055948749

theorem tailTrace_1077566 : CollatzResearch.WordTrace tailWord_1077566 prefixEnd_1077566 122957621098408055948749 := by
  unfold tailWord_1077566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4912757601771236308280569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26201373876113260310829701 4912757601771236308280569)
  ·
    refine ⟨3684568201328427231210427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4912757601771236308280569 3684568201328427231210427)
    ·
      refine ⟨5526852301992640846815641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3684568201328427231210427 5526852301992640846815641)
      ·
        refine ⟨4145139226494480635111731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5526852301992640846815641 4145139226494480635111731)
        ·
          refine ⟨6217708839741720952667597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145139226494480635111731 6217708839741720952667597)
          ·
            refine ⟨2331640814903145357250349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6217708839741720952667597 2331640814903145357250349)
            ·
              refine ⟨874365305588679508968881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2331640814903145357250349 874365305588679508968881)
              ·
                refine ⟨655773979191509631726661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874365305588679508968881 655773979191509631726661)
                ·
                  refine ⟨122957621098408055948749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655773979191509631726661 122957621098408055948749)
                  ·
                    rfl

theorem cell22_1077566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1077566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077566 prefixEnd_1077566 := by exact prefixLift 1077566
  have htrace : WordTrace (prefixWord ++ tailWord_1077566) baseStart_1077566 baseEnd_1077566 := by
    simpa [prefixWord, tailWord_1077566, baseEnd_1077566] using wordTrace_append hprefix tailTrace_1077566
  have hstable : (prefixWord ++ tailWord_1077566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077566).length < 2 ^ (prefixWord ++ tailWord_1077566).sum := by decide
  have hdescent : baseEnd_1077566 < baseStart_1077566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077596 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1077596 : Nat := 118140960795 + 1077596 * 2 ^ 59
def prefixEnd_1077596 : Nat := 4983230072969 + 3 ^ 40 * 1077596 * 2
def baseEnd_1077596 : Nat := 368883132908314089596155

theorem tailTrace_1077596 : CollatzResearch.WordTrace tailWord_1077596 prefixEnd_1077596 368883132908314089596155 := by
  unfold tailWord_1077596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19651577502030602794918321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26202103336040803726557761 19651577502030602794918321)
  ·
    refine ⟨14738683126522952096188741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19651577502030602794918321 14738683126522952096188741)
    ·
      refine ⟨2763503086223053518035389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14738683126522952096188741 2763503086223053518035389)
      ·
        refine ⟨1036313657333645069263271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2763503086223053518035389 1036313657333645069263271)
        ·
          refine ⟨1554470486000467603894907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036313657333645069263271 1554470486000467603894907)
          ·
            refine ⟨2331705729000701405842361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554470486000467603894907 2331705729000701405842361)
            ·
              refine ⟨1748779296750526054381771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331705729000701405842361 1748779296750526054381771)
              ·
                refine ⟨2623168945125789081572657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748779296750526054381771 2623168945125789081572657)
                ·
                  refine ⟨1967376708844341811179493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623168945125789081572657 1967376708844341811179493)
                  ·
                    refine ⟨368883132908314089596155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1967376708844341811179493 368883132908314089596155)
                    ·
                      rfl

theorem cell22_1077596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1077596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077596 prefixEnd_1077596 := by exact prefixLift 1077596
  have htrace : WordTrace (prefixWord ++ tailWord_1077596) baseStart_1077596 baseEnd_1077596 := by
    simpa [prefixWord, tailWord_1077596, baseEnd_1077596] using wordTrace_append hprefix tailTrace_1077596
  have hstable : (prefixWord ++ tailWord_1077596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077596).length < 2 ^ (prefixWord ++ tailWord_1077596).sum := by decide
  have hdescent : baseEnd_1077596 < baseStart_1077596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077609 : List Nat := [1, 2, 1, 1, 1, 3, 4, 5, 1, 3]
def baseStart_1077609 : Nat := 118140960795 + 1077609 * 2 ^ 59
def prefixEnd_1077609 : Nat := 4983230072969 + 3 ^ 40 * 1077609 * 2
def baseEnd_1077609 : Nat := 368887583073986389021115

theorem tailTrace_1077609 : CollatzResearch.WordTrace tailWord_1077609 prefixEnd_1077609 368887583073986389021115 := by
  unfold tailWord_1077609
  simp only [CollatzResearch.WordTrace]
  refine ⟨39303629153014108810059881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26202419435342739206706587 39303629153014108810059881)
  ·
    refine ⟨29477721864760581607544911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39303629153014108810059881 29477721864760581607544911)
    ·
      refine ⟨44216582797140872411317367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29477721864760581607544911 44216582797140872411317367)
      ·
        refine ⟨66324874195711308616976051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44216582797140872411317367 66324874195711308616976051)
        ·
          refine ⟨99487311293566962925464077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66324874195711308616976051 99487311293566962925464077)
          ·
            refine ⟨37307741735087611097049029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99487311293566962925464077 37307741735087611097049029)
            ·
              refine ⟨6995201575328927080696693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37307741735087611097049029 6995201575328927080696693)
              ·
                refine ⟨655800147687086913815315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6995201575328927080696693 655800147687086913815315)
                ·
                  refine ⟨983700221530630370722973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655800147687086913815315 983700221530630370722973)
                  ·
                    refine ⟨368887583073986389021115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983700221530630370722973 368887583073986389021115)
                    ·
                      rfl

theorem cell22_1077609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 3].length) (baseStart_1077609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077609 prefixEnd_1077609 := by exact prefixLift 1077609
  have htrace : WordTrace (prefixWord ++ tailWord_1077609) baseStart_1077609 baseEnd_1077609 := by
    simpa [prefixWord, tailWord_1077609, baseEnd_1077609] using wordTrace_append hprefix tailTrace_1077609
  have hstable : (prefixWord ++ tailWord_1077609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077609).length < 2 ^ (prefixWord ++ tailWord_1077609).sum := by decide
  have hdescent : baseEnd_1077609 < baseStart_1077609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077795 : List Nat := [1, 1, 1, 4, 4, 3, 2, 2, 1, 3]
def baseStart_1077795 : Nat := 118140960795 + 1077795 * 2 ^ 59
def prefixEnd_1077795 : Nat := 4983230072969 + 3 ^ 40 * 1077795 * 2
def baseEnd_1077795 : Nat := 368951254675143903870545

theorem tailTrace_1077795 : CollatzResearch.WordTrace tailWord_1077795 prefixEnd_1077795 368951254675143903870545 := by
  unfold tailWord_1077795
  simp only [CollatzResearch.WordTrace]
  refine ⟨39310413130340262576330839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26206942086893508384220559 39310413130340262576330839)
  ·
    refine ⟨58965619695510393864496259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39310413130340262576330839 58965619695510393864496259)
    ·
      refine ⟨88448429543265590796744389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58965619695510393864496259 88448429543265590796744389)
      ·
        refine ⟨16584080539362298274389573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88448429543265590796744389 16584080539362298274389573)
        ·
          refine ⟨3109515101130430926448045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16584080539362298274389573 3109515101130430926448045)
          ·
            refine ⟨1166068162923911597418017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3109515101130430926448045 1166068162923911597418017)
            ·
              refine ⟨874551122192933698063513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166068162923911597418017 874551122192933698063513)
              ·
                refine ⟨655913341644700273547635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874551122192933698063513 655913341644700273547635)
                ·
                  refine ⟨983870012467050410321453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655913341644700273547635 983870012467050410321453)
                  ·
                    refine ⟨368951254675143903870545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983870012467050410321453 368951254675143903870545)
                    ·
                      rfl

theorem cell22_1077795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 3].length) (baseStart_1077795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077795 prefixEnd_1077795 := by exact prefixLift 1077795
  have htrace : WordTrace (prefixWord ++ tailWord_1077795) baseStart_1077795 baseEnd_1077795 := by
    simpa [prefixWord, tailWord_1077795, baseEnd_1077795] using wordTrace_append hprefix tailTrace_1077795
  have hstable : (prefixWord ++ tailWord_1077795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077795).length < 2 ^ (prefixWord ++ tailWord_1077795).sum := by decide
  have hdescent : baseEnd_1077795 < baseStart_1077795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077806 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1077806 : Nat := 118140960795 + 1077806 * 2 ^ 59
def prefixEnd_1077806 : Nat := 4983230072969 + 3 ^ 40 * 1077806 * 2
def baseEnd_1077806 : Nat := 368955020199943541845511

theorem tailTrace_1077806 : CollatzResearch.WordTrace tailWord_1077806 prefixEnd_1077806 368955020199943541845511 := by
  unfold tailWord_1077806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913851791662551431872659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26207209555533607636654181 4913851791662551431872659)
  ·
    refine ⟨7370777687493827147808989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4913851791662551431872659 7370777687493827147808989)
    ·
      refine ⟨2764041632810185180428371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7370777687493827147808989 2764041632810185180428371)
      ·
        refine ⟨4146062449215277770642557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2764041632810185180428371 4146062449215277770642557)
        ·
          refine ⟨1554773418455729163990959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4146062449215277770642557 1554773418455729163990959)
          ·
            refine ⟨2332160127683593745986439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554773418455729163990959 2332160127683593745986439)
            ·
              refine ⟨3498240191525390618979659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332160127683593745986439 3498240191525390618979659)
              ·
                refine ⟨5247360287288085928469489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498240191525390618979659 5247360287288085928469489)
                ·
                  refine ⟨3935520215466064446352117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247360287288085928469489 3935520215466064446352117)
                  ·
                    refine ⟨368955020199943541845511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3935520215466064446352117 368955020199943541845511)
                    ·
                      rfl

theorem cell22_1077806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1077806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077806 prefixEnd_1077806 := by exact prefixLift 1077806
  have htrace : WordTrace (prefixWord ++ tailWord_1077806) baseStart_1077806 baseEnd_1077806 := by
    simpa [prefixWord, tailWord_1077806, baseEnd_1077806] using wordTrace_append hprefix tailTrace_1077806
  have hstable : (prefixWord ++ tailWord_1077806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077806).length < 2 ^ (prefixWord ++ tailWord_1077806).sum := by decide
  have hdescent : baseEnd_1077806 < baseStart_1077806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077834 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1077834 : Nat := 118140960795 + 1077834 * 2 ^ 59
def prefixEnd_1077834 : Nat := 4983230072969 + 3 ^ 40 * 1077834 * 2
def baseEnd_1077834 : Nat := 368964605172160802145425

theorem tailTrace_1077834 : CollatzResearch.WordTrace tailWord_1077834 prefixEnd_1077834 368964605172160802145425 := by
  unfold tailWord_1077834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9827958894299743059250139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26207890384799314824667037 9827958894299743059250139)
  ·
    refine ⟨14741938341449614588875209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9827958894299743059250139 14741938341449614588875209)
    ·
      refine ⟨11056453756087210941656407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14741938341449614588875209 11056453756087210941656407)
      ·
        refine ⟨16584680634130816412484611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11056453756087210941656407 16584680634130816412484611)
        ·
          refine ⟨24877020951196224618726917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16584680634130816412484611 24877020951196224618726917)
          ·
            refine ⟨4664441428349292116011297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24877020951196224618726917 4664441428349292116011297)
            ·
              refine ⟨3498331071261969087008473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4664441428349292116011297 3498331071261969087008473)
              ·
                refine ⟨2623748303446476815256355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3498331071261969087008473 2623748303446476815256355)
                ·
                  refine ⟨3935622455169715222884533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623748303446476815256355 3935622455169715222884533)
                  ·
                    refine ⟨368964605172160802145425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3935622455169715222884533 368964605172160802145425)
                    ·
                      rfl

theorem cell22_1077834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1077834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077834 prefixEnd_1077834 := by exact prefixLift 1077834
  have htrace : WordTrace (prefixWord ++ tailWord_1077834) baseStart_1077834 baseEnd_1077834 := by
    simpa [prefixWord, tailWord_1077834, baseEnd_1077834] using wordTrace_append hprefix tailTrace_1077834
  have hstable : (prefixWord ++ tailWord_1077834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077834).length < 2 ^ (prefixWord ++ tailWord_1077834).sum := by decide
  have hdescent : baseEnd_1077834 < baseStart_1077834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077836 : List Nat := [2, 2, 1, 3, 1, 2, 4, 3, 4]
def baseStart_1077836 : Nat := 118140960795 + 1077836 * 2 ^ 59
def prefixEnd_1077836 : Nat := 4983230072969 + 3 ^ 40 * 1077836 * 2
def baseEnd_1077836 : Nat := 122988429937677821198473

theorem tailTrace_1077836 : CollatzResearch.WordTrace tailWord_1077836 prefixEnd_1077836 122988429937677821198473 := by
  unfold tailWord_1077836
  simp only [CollatzResearch.WordTrace]
  refine ⟨19655954261595863289286681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26207939015461151052382241 19655954261595863289286681)
  ·
    refine ⟨14741965696196897466965011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19655954261595863289286681 14741965696196897466965011)
    ·
      refine ⟨22112948544295346200447517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14741965696196897466965011 22112948544295346200447517)
      ·
        refine ⟨8292355704110754825167819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22112948544295346200447517 8292355704110754825167819)
        ·
          refine ⟨12438533556166132237751729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8292355704110754825167819 12438533556166132237751729)
          ·
            refine ⟨9328900167124599178313797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12438533556166132237751729 9328900167124599178313797)
            ·
              refine ⟨1749168781335862345933837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9328900167124599178313797 1749168781335862345933837)
              ·
                refine ⟨655938293000948379725189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1749168781335862345933837 655938293000948379725189)
                ·
                  refine ⟨122988429937677821198473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655938293000948379725189 122988429937677821198473)
                  ·
                    rfl

theorem cell22_1077836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_1077836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077836 prefixEnd_1077836 := by exact prefixLift 1077836
  have htrace : WordTrace (prefixWord ++ tailWord_1077836) baseStart_1077836 baseEnd_1077836 := by
    simpa [prefixWord, tailWord_1077836, baseEnd_1077836] using wordTrace_append hprefix tailTrace_1077836
  have hstable : (prefixWord ++ tailWord_1077836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077836).length < 2 ^ (prefixWord ++ tailWord_1077836).sum := by decide
  have hdescent : baseEnd_1077836 < baseStart_1077836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077847 : List Nat := [1, 1, 3, 2, 2, 2, 11]
def baseStart_1077847 : Nat := 118140960795 + 1077847 * 2 ^ 59
def prefixEnd_1077847 : Nat := 4983230072969 + 3 ^ 40 * 1077847 * 2
def baseEnd_1077847 : Nat := 13665520568067892650755

theorem tailTrace_1077847 : CollatzResearch.WordTrace tailWord_1077847 prefixEnd_1077847 13665520568067892650755 := by
  unfold tailWord_1077847
  simp only [CollatzResearch.WordTrace]
  refine ⟨39312309726151875457223795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26208206484101250304815863 39312309726151875457223795)
  ·
    refine ⟨58968464589227813185835693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39312309726151875457223795 58968464589227813185835693)
    ·
      refine ⟨22113174220960429944688385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58968464589227813185835693 22113174220960429944688385)
      ·
        refine ⟨16584880665720322458516289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22113174220960429944688385 16584880665720322458516289)
        ·
          refine ⟨12438660499290241843887217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16584880665720322458516289 12438660499290241843887217)
          ·
            refine ⟨9328995374467681382915413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12438660499290241843887217 9328995374467681382915413)
            ·
              refine ⟨13665520568067892650755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9328995374467681382915413 13665520568067892650755)
              ·
                rfl

theorem cell22_1077847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 11].length) (baseStart_1077847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077847 prefixEnd_1077847 := by exact prefixLift 1077847
  have htrace : WordTrace (prefixWord ++ tailWord_1077847) baseStart_1077847 baseEnd_1077847 := by
    simpa [prefixWord, tailWord_1077847, baseEnd_1077847] using wordTrace_append hprefix tailTrace_1077847
  have hstable : (prefixWord ++ tailWord_1077847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077847).length < 2 ^ (prefixWord ++ tailWord_1077847).sum := by decide
  have hdescent : baseEnd_1077847 < baseStart_1077847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077881 : List Nat := [1, 2, 1, 3, 3, 4, 2, 6]
def baseStart_1077881 : Nat := 118140960795 + 1077881 * 2 ^ 59
def prefixEnd_1077881 : Nat := 4983230072969 + 3 ^ 40 * 1077881 * 2
def baseEnd_1077881 : Nat := 40997854914740927357809

theorem tailTrace_1077881 : CollatzResearch.WordTrace tailWord_1077881 prefixEnd_1077881 40997854914740927357809 := by
  unfold tailWord_1077881
  simp only [CollatzResearch.WordTrace]
  refine ⟨39313549808028699263961497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26209033205352466175974331 39313549808028699263961497)
  ·
    refine ⟨29485162356021524447971123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39313549808028699263961497 29485162356021524447971123)
    ·
      refine ⟨44227743534032286671956685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29485162356021524447971123 44227743534032286671956685)
      ·
        refine ⟨16585403825262107501983757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44227743534032286671956685 16585403825262107501983757)
        ·
          refine ⟨6219526434473290313243909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16585403825262107501983757 6219526434473290313243909)
          ·
            refine ⟨1166161206463741933733233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6219526434473290313243909 1166161206463741933733233)
            ·
              refine ⟨874620904847806450299925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166161206463741933733233 874620904847806450299925)
              ·
                refine ⟨40997854914740927357809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 874620904847806450299925 40997854914740927357809)
                ·
                  rfl

theorem cell22_1077881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 6].length) (baseStart_1077881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077881 prefixEnd_1077881 := by exact prefixLift 1077881
  have htrace : WordTrace (prefixWord ++ tailWord_1077881) baseStart_1077881 baseEnd_1077881 := by
    simpa [prefixWord, tailWord_1077881, baseEnd_1077881] using wordTrace_append hprefix tailTrace_1077881
  have hstable : (prefixWord ++ tailWord_1077881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077881).length < 2 ^ (prefixWord ++ tailWord_1077881).sum := by decide
  have hdescent : baseEnd_1077881 < baseStart_1077881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077924 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1077924 : Nat := 118140960795 + 1077924 * 2 ^ 59
def prefixEnd_1077924 : Nat := 4983230072969 + 3 ^ 40 * 1077924 * 2
def baseEnd_1077924 : Nat := 368995414011430567395149

theorem tailTrace_1077924 : CollatzResearch.WordTrace tailWord_1077924 prefixEnd_1077924 368995414011430567395149 := by
  unfold tailWord_1077924
  simp only [CollatzResearch.WordTrace]
  refine ⟨19657559073436458803888413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26210078764581945071851217 19657559073436458803888413)
  ·
    refine ⟨7371584652538672051458155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19657559073436458803888413 7371584652538672051458155)
    ·
      refine ⟨11057376978808008077187233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7371584652538672051458155 11057376978808008077187233)
      ·
        refine ⟨8293032734106006057890425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11057376978808008077187233 8293032734106006057890425)
        ·
          refine ⟨6219774550579504543417819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8293032734106006057890425 6219774550579504543417819)
          ·
            refine ⟨9329661825869256815126729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6219774550579504543417819 9329661825869256815126729)
            ·
              refine ⟨6997246369401942611345047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9329661825869256815126729 6997246369401942611345047)
              ·
                refine ⟨10495869554102913917017571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6997246369401942611345047 10495869554102913917017571)
                ·
                  refine ⟨15743804331154370875526357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10495869554102913917017571 15743804331154370875526357)
                  ·
                    refine ⟨368995414011430567395149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15743804331154370875526357 368995414011430567395149)
                    ·
                      rfl

theorem cell22_1077924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1077924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077924 prefixEnd_1077924 := by exact prefixLift 1077924
  have htrace : WordTrace (prefixWord ++ tailWord_1077924) baseStart_1077924 baseEnd_1077924 := by
    simpa [prefixWord, tailWord_1077924, baseEnd_1077924] using wordTrace_append hprefix tailTrace_1077924
  have hstable : (prefixWord ++ tailWord_1077924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077924).length < 2 ^ (prefixWord ++ tailWord_1077924).sum := by decide
  have hdescent : baseEnd_1077924 < baseStart_1077924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077969 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_1077969 : Nat := 118140960795 + 1077969 * 2 ^ 59
def prefixEnd_1077969 : Nat := 4983230072969 + 3 ^ 40 * 1077969 * 2
def baseEnd_1077969 : Nat := 369010818431065450020011

theorem tailTrace_1077969 : CollatzResearch.WordTrace tailWord_1077969 prefixEnd_1077969 369010818431065450020011 := by
  unfold tailWord_1077969
  simp only [CollatzResearch.WordTrace]
  refine ⟨39316759431709890293164961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26211172954473260195443307 39316759431709890293164961)
  ·
    refine ⟨29487569573782417719873721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39316759431709890293164961 29487569573782417719873721)
    ·
      refine ⟨22115677180336813289905291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29487569573782417719873721 22115677180336813289905291)
      ·
        refine ⟨33173515770505219934857937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22115677180336813289905291 33173515770505219934857937)
        ·
          refine ⟨24880136827878914951143453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33173515770505219934857937 24880136827878914951143453)
          ·
            refine ⟨9330051310454593106678795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24880136827878914951143453 9330051310454593106678795)
            ·
              refine ⟨13995076965681889660018193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9330051310454593106678795 13995076965681889660018193)
              ·
                refine ⟨10496307724261417245013645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13995076965681889660018193 10496307724261417245013645)
                ·
                  refine ⟨3936115396598031466880117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10496307724261417245013645 3936115396598031466880117)
                  ·
                    refine ⟨369010818431065450020011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3936115396598031466880117 369010818431065450020011)
                    ·
                      rfl

theorem cell22_1077969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_1077969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077969 prefixEnd_1077969 := by exact prefixLift 1077969
  have htrace : WordTrace (prefixWord ++ tailWord_1077969) baseStart_1077969 baseEnd_1077969 := by
    simpa [prefixWord, tailWord_1077969, baseEnd_1077969] using wordTrace_append hprefix tailTrace_1077969
  have hstable : (prefixWord ++ tailWord_1077969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077969).length < 2 ^ (prefixWord ++ tailWord_1077969).sum := by decide
  have hdescent : baseEnd_1077969 < baseStart_1077969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077984 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_1077984 : Nat := 118140960795 + 1077984 * 2 ^ 59
def prefixEnd_1077984 : Nat := 4983230072969 + 3 ^ 40 * 1077984 * 2
def baseEnd_1077984 : Nat := 369015953237610410894965

theorem tailTrace_1077984 : CollatzResearch.WordTrace tailWord_1077984 prefixEnd_1077984 369015953237610410894965 := by
  unfold tailWord_1077984
  simp only [CollatzResearch.WordTrace]
  refine ⟨19658653263327773927480503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26211537684437031903307337 19658653263327773927480503)
  ·
    refine ⟨29487979894991660891220755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19658653263327773927480503 29487979894991660891220755)
    ·
      refine ⟨44231969842487491336831133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29487979894991660891220755 44231969842487491336831133)
      ·
        refine ⟨16586988690932809251311675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44231969842487491336831133 16586988690932809251311675)
        ·
          refine ⟨24880483036399213876967513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16586988690932809251311675 24880483036399213876967513)
          ·
            refine ⟨18660362277299410407725635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24880483036399213876967513 18660362277299410407725635)
            ·
              refine ⟨27990543415949115611588453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18660362277299410407725635 27990543415949115611588453)
              ·
                refine ⟨5248226890490459177172835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27990543415949115611588453 5248226890490459177172835)
                ·
                  refine ⟨7872340335735688765759253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5248226890490459177172835 7872340335735688765759253)
                  ·
                    refine ⟨369015953237610410894965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7872340335735688765759253 369015953237610410894965)
                    ·
                      rfl

theorem cell22_1077984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_1077984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1077984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1077984 prefixEnd_1077984 := by exact prefixLift 1077984
  have htrace : WordTrace (prefixWord ++ tailWord_1077984) baseStart_1077984 baseEnd_1077984 := by
    simpa [prefixWord, tailWord_1077984, baseEnd_1077984] using wordTrace_append hprefix tailTrace_1077984
  have hstable : (prefixWord ++ tailWord_1077984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077984).length < 2 ^ (prefixWord ++ tailWord_1077984).sum := by decide
  have hdescent : baseEnd_1077984 < baseStart_1077984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078048 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 3, 3]
def baseStart_1078048 : Nat := 118140960795 + 1078048 * 2 ^ 59
def prefixEnd_1078048 : Nat := 4983230072969 + 3 ^ 40 * 1078048 * 2
def baseEnd_1078048 : Nat := 369037861745535577294769

theorem tailTrace_1078048 : CollatzResearch.WordTrace tailWord_1078048 prefixEnd_1078048 369037861745535577294769 := by
  unfold tailWord_1078048
  simp only [CollatzResearch.WordTrace]
  refine ⟨19659820399211843392645399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26213093865615791190193865 19659820399211843392645399)
  ·
    refine ⟨29489730598817765088968099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19659820399211843392645399 29489730598817765088968099)
    ·
      refine ⟨44234595898226647633452149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29489730598817765088968099 44234595898226647633452149)
      ·
        refine ⟨4146993365458748215636139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44234595898226647633452149 4146993365458748215636139)
        ·
          refine ⟨6220490048188122323454209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4146993365458748215636139 6220490048188122323454209)
          ·
            refine ⟨4665367536141091742590657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6220490048188122323454209 4665367536141091742590657)
            ·
              refine ⟨3499025652105818806942993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4665367536141091742590657 3499025652105818806942993)
              ·
                refine ⟨2624269239079364105207245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3499025652105818806942993 2624269239079364105207245)
                ·
                  refine ⟨984100964654761539452717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2624269239079364105207245 984100964654761539452717)
                  ·
                    refine ⟨369037861745535577294769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984100964654761539452717 369037861745535577294769)
                    ·
                      rfl

theorem cell22_1078048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_1078048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078048 prefixEnd_1078048 := by exact prefixLift 1078048
  have htrace : WordTrace (prefixWord ++ tailWord_1078048) baseStart_1078048 baseEnd_1078048 := by
    simpa [prefixWord, tailWord_1078048, baseEnd_1078048] using wordTrace_append hprefix tailTrace_1078048
  have hstable : (prefixWord ++ tailWord_1078048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078048).length < 2 ^ (prefixWord ++ tailWord_1078048).sum := by decide
  have hdescent : baseEnd_1078048 < baseStart_1078048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078059 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 3, 7]
def baseStart_1078059 : Nat := 118140960795 + 1078059 * 2 ^ 59
def prefixEnd_1078059 : Nat := 4983230072969 + 3 ^ 40 * 1078059 * 2
def baseEnd_1078059 : Nat := 369041627270335215269735

theorem tailTrace_1078059 : CollatzResearch.WordTrace tailWord_1078059 prefixEnd_1078059 369041627270335215269735 := by
  unfold tailWord_1078059
  simp only [CollatzResearch.WordTrace]
  refine ⟨39320042001383835663941231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26213361334255890442627487 39320042001383835663941231)
  ·
    refine ⟨58980063002075753495911847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39320042001383835663941231 58980063002075753495911847)
    ·
      refine ⟨88470094503113630243867771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58980063002075753495911847 88470094503113630243867771)
      ·
        refine ⟨132705141754670445365801657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88470094503113630243867771 132705141754670445365801657)
        ·
          refine ⟨99528856316002834024351243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132705141754670445365801657 99528856316002834024351243)
          ·
            refine ⟨149293284474004251036526865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99528856316002834024351243 149293284474004251036526865)
            ·
              refine ⟨111969963355503188277395149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149293284474004251036526865 111969963355503188277395149)
              ·
                refine ⟨41988736258313695604023181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111969963355503188277395149 41988736258313695604023181)
                ·
                  refine ⟨15745776096867635851508693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41988736258313695604023181 15745776096867635851508693)
                  ·
                    refine ⟨369041627270335215269735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15745776096867635851508693 369041627270335215269735)
                    ·
                      rfl

theorem cell22_1078059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_1078059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078059 prefixEnd_1078059 := by exact prefixLift 1078059
  have htrace : WordTrace (prefixWord ++ tailWord_1078059) baseStart_1078059 baseEnd_1078059 := by
    simpa [prefixWord, tailWord_1078059, baseEnd_1078059] using wordTrace_append hprefix tailTrace_1078059
  have hstable : (prefixWord ++ tailWord_1078059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078059).length < 2 ^ (prefixWord ++ tailWord_1078059).sum := by decide
  have hdescent : baseEnd_1078059 < baseStart_1078059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078136 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1078136 : Nat := 118140960795 + 1078136 * 2 ^ 59
def prefixEnd_1078136 : Nat := 4983230072969 + 3 ^ 40 * 1078136 * 2
def baseEnd_1078136 : Nat := 369067985943932681094499

theorem tailTrace_1078136 : CollatzResearch.WordTrace tailWord_1078136 prefixEnd_1078136 369067985943932681094499 := by
  unfold tailWord_1078136
  simp only [CollatzResearch.WordTrace]
  refine ⟨19661425211052438907247131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26215233614736585209662841 19661425211052438907247131)
  ·
    refine ⟨29492137816578658360870697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19661425211052438907247131 29492137816578658360870697)
    ·
      refine ⟨22119103362433993770653023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29492137816578658360870697 22119103362433993770653023)
      ·
        refine ⟨33178655043650990655979535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22119103362433993770653023 33178655043650990655979535)
        ·
          refine ⟨49767982565476485983969303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33178655043650990655979535 49767982565476485983969303)
          ·
            refine ⟨74651973848214728975953955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49767982565476485983969303 74651973848214728975953955)
            ·
              refine ⟨111977960772322093463930933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74651973848214728975953955 111977960772322093463930933)
              ·
                refine ⟨10497933822405196262243525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111977960772322093463930933 10497933822405196262243525)
                ·
                  refine ⟨1968362591700974299170661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10497933822405196262243525 1968362591700974299170661)
                  ·
                    refine ⟨369067985943932681094499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968362591700974299170661 369067985943932681094499)
                    ·
                      rfl

theorem cell22_1078136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1078136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078136 prefixEnd_1078136 := by exact prefixLift 1078136
  have htrace : WordTrace (prefixWord ++ tailWord_1078136) baseStart_1078136 baseEnd_1078136 := by
    simpa [prefixWord, tailWord_1078136, baseEnd_1078136] using wordTrace_append hprefix tailTrace_1078136
  have hstable : (prefixWord ++ tailWord_1078136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078136).length < 2 ^ (prefixWord ++ tailWord_1078136).sum := by decide
  have hdescent : baseEnd_1078136 < baseStart_1078136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078200 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 3, 3]
def baseStart_1078200 : Nat := 118140960795 + 1078200 * 2 ^ 59
def prefixEnd_1078200 : Nat := 4983230072969 + 3 ^ 40 * 1078200 * 2
def baseEnd_1078200 : Nat := 369089894451857847494303

theorem tailTrace_1078200 : CollatzResearch.WordTrace tailWord_1078200 prefixEnd_1078200 369089894451857847494303 := by
  unfold tailWord_1078200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19662592346936508372412027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26216789795915344496549369 19662592346936508372412027)
  ·
    refine ⟨29493888520404762558618041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19662592346936508372412027 29493888520404762558618041)
    ·
      refine ⟨22120416390303571918963531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29493888520404762558618041 22120416390303571918963531)
      ·
        refine ⟨33180624585455357878445297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22120416390303571918963531 33180624585455357878445297)
        ·
          refine ⟨24885468439091518408833973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33180624585455357878445297 24885468439091518408833973)
          ·
            refine ⟨2333012666164829850828185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24885468439091518408833973 2333012666164829850828185)
            ·
              refine ⟨1749759499623622388121139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333012666164829850828185 1749759499623622388121139)
              ·
                refine ⟨2624639249435433582181709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749759499623622388121139 2624639249435433582181709)
                ·
                  refine ⟨984239718538287593318141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2624639249435433582181709 984239718538287593318141)
                  ·
                    refine ⟨369089894451857847494303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984239718538287593318141 369089894451857847494303)
                    ·
                      rfl

theorem cell22_1078200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_1078200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078200 prefixEnd_1078200 := by exact prefixLift 1078200
  have htrace : WordTrace (prefixWord ++ tailWord_1078200) baseStart_1078200 baseEnd_1078200 := by
    simpa [prefixWord, tailWord_1078200, baseEnd_1078200] using wordTrace_append hprefix tailTrace_1078200
  have hstable : (prefixWord ++ tailWord_1078200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078200).length < 2 ^ (prefixWord ++ tailWord_1078200).sum := by decide
  have hdescent : baseEnd_1078200 < baseStart_1078200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078230 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1078230 : Nat := 118140960795 + 1078230 * 2 ^ 59
def prefixEnd_1078230 : Nat := 4983230072969 + 3 ^ 40 * 1078230 * 2
def baseEnd_1078230 : Nat := 123033388021649256414737

theorem tailTrace_1078230 : CollatzResearch.WordTrace tailWord_1078230 prefixEnd_1078230 123033388021649256414737 := by
  unfold tailWord_1078230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457892430235270741776009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26217519255842887912277429 2457892430235270741776009)
  ·
    refine ⟨1843419322676453056332007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2457892430235270741776009 1843419322676453056332007)
    ·
      refine ⟨2765128984014679584498011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1843419322676453056332007 2765128984014679584498011)
      ·
        refine ⟨4147693476022019376747017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765128984014679584498011 4147693476022019376747017)
        ·
          refine ⟨3110770107016514532560263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4147693476022019376747017 3110770107016514532560263)
          ·
            refine ⟨4666155160524771798840395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110770107016514532560263 4666155160524771798840395)
            ·
              refine ⟨6999232740787157698260593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666155160524771798840395 6999232740787157698260593)
              ·
                refine ⟨5249424555590368273695445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6999232740787157698260593 5249424555590368273695445)
                ·
                  refine ⟨123033388021649256414737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5249424555590368273695445 123033388021649256414737)
                  ·
                    rfl

theorem cell22_1078230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1078230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078230 prefixEnd_1078230 := by exact prefixLift 1078230
  have htrace : WordTrace (prefixWord ++ tailWord_1078230) baseStart_1078230 baseEnd_1078230 := by
    simpa [prefixWord, tailWord_1078230, baseEnd_1078230] using wordTrace_append hprefix tailTrace_1078230
  have hstable : (prefixWord ++ tailWord_1078230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078230).length < 2 ^ (prefixWord ++ tailWord_1078230).sum := by decide
  have hdescent : baseEnd_1078230 < baseStart_1078230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078234 : List Nat := [3, 1, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_1078234 : Nat := 118140960795 + 1078234 * 2 ^ 59
def prefixEnd_1078234 : Nat := 4983230072969 + 3 ^ 40 * 1078234 * 2
def baseEnd_1078234 : Nat := 369101533346693092144199

theorem tailTrace_1078234 : CollatzResearch.WordTrace tailWord_1078234 prefixEnd_1078234 369101533346693092144199 := by
  unfold tailWord_1078234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9831606193937460137890439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26217616517166560367707837 9831606193937460137890439)
  ·
    refine ⟨14747409290906190206835659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9831606193937460137890439 14747409290906190206835659)
    ·
      refine ⟨22121113936359285310253489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14747409290906190206835659 22121113936359285310253489)
      ·
        refine ⟨16590835452269463982690117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22121113936359285310253489 16590835452269463982690117)
        ·
          refine ⟨3110781647300524496754397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16590835452269463982690117 3110781647300524496754397)
          ·
            refine ⟨1166543117737696686282899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3110781647300524496754397 1166543117737696686282899)
            ·
              refine ⟨1749814676606545029424349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166543117737696686282899 1749814676606545029424349)
              ·
                refine ⟨656180503727454386034131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1749814676606545029424349 656180503727454386034131)
                ·
                  refine ⟨984270755591181579051197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656180503727454386034131 984270755591181579051197)
                  ·
                    refine ⟨369101533346693092144199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984270755591181579051197 369101533346693092144199)
                    ·
                      rfl

theorem cell22_1078234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_1078234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078234 prefixEnd_1078234 := by exact prefixLift 1078234
  have htrace : WordTrace (prefixWord ++ tailWord_1078234) baseStart_1078234 baseEnd_1078234 := by
    simpa [prefixWord, tailWord_1078234, baseEnd_1078234] using wordTrace_append hprefix tailTrace_1078234
  have hstable : (prefixWord ++ tailWord_1078234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078234).length < 2 ^ (prefixWord ++ tailWord_1078234).sum := by decide
  have hdescent : baseEnd_1078234 < baseStart_1078234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078305 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1078305 : Nat := 118140960795 + 1078305 * 2 ^ 59
def prefixEnd_1078305 : Nat := 4983230072969 + 3 ^ 40 * 1078305 * 2
def baseEnd_1078305 : Nat := 369125838097672573618981

theorem tailTrace_1078305 : CollatzResearch.WordTrace tailWord_1078305 prefixEnd_1078305 369125838097672573618981 := by
  unfold tailWord_1078305
  simp only [CollatzResearch.WordTrace]
  refine ⟨39329014358492619677396369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26219342905661746451597579 39329014358492619677396369)
  ·
    refine ⟨29496760768869464758047277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39329014358492619677396369 29496760768869464758047277)
    ·
      refine ⟨11061285288326049284267729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29496760768869464758047277 11061285288326049284267729)
      ·
        refine ⟨8295963966244536963200797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11061285288326049284267729 8295963966244536963200797)
        ·
          refine ⟨3110986487341701361200299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8295963966244536963200797 3110986487341701361200299)
          ·
            refine ⟨4666479731012552041800449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110986487341701361200299 4666479731012552041800449)
            ·
              refine ⟨3499859798259414031350337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4666479731012552041800449 3499859798259414031350337)
              ·
                refine ⟨2624894848694560523512753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3499859798259414031350337 2624894848694560523512753)
                ·
                  refine ⟨1968671136520920392634565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624894848694560523512753 1968671136520920392634565)
                  ·
                    refine ⟨369125838097672573618981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968671136520920392634565 369125838097672573618981)
                    ·
                      rfl

theorem cell22_1078305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1078305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078305 prefixEnd_1078305 := by exact prefixLift 1078305
  have htrace : WordTrace (prefixWord ++ tailWord_1078305) baseStart_1078305 baseEnd_1078305 := by
    simpa [prefixWord, tailWord_1078305, baseEnd_1078305] using wordTrace_append hprefix tailTrace_1078305
  have hstable : (prefixWord ++ tailWord_1078305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078305).length < 2 ^ (prefixWord ++ tailWord_1078305).sum := by decide
  have hdescent : baseEnd_1078305 < baseStart_1078305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078307 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 2, 3]
def baseStart_1078307 : Nat := 118140960795 + 1078307 * 2 ^ 59
def prefixEnd_1078307 : Nat := 4983230072969 + 3 ^ 40 * 1078307 * 2
def baseEnd_1078307 : Nat := 369126522738545235068975

theorem tailTrace_1078307 : CollatzResearch.WordTrace tailWord_1078307 prefixEnd_1078307 369126522738545235068975 := by
  unfold tailWord_1078307
  simp only [CollatzResearch.WordTrace]
  refine ⟨39329087304485374018969175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26219391536323582679312783 39329087304485374018969175)
  ·
    refine ⟨58993630956728061028453763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39329087304485374018969175 58993630956728061028453763)
    ·
      refine ⟨88490446435092091542680645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58993630956728061028453763 88490446435092091542680645)
      ·
        refine ⟨16591958706579767164252621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88490446435092091542680645 16591958706579767164252621)
        ·
          refine ⟨6221984514967412686594733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16591958706579767164252621 6221984514967412686594733)
          ·
            refine ⟨2333244193112779757473025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6221984514967412686594733 2333244193112779757473025)
            ·
              refine ⟨1749933144834584818104769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333244193112779757473025 1749933144834584818104769)
              ·
                refine ⟨1312449858625938613578577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749933144834584818104769 1312449858625938613578577)
                ·
                  refine ⟨984337393969453960183933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312449858625938613578577 984337393969453960183933)
                  ·
                    refine ⟨369126522738545235068975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984337393969453960183933 369126522738545235068975)
                    ·
                      rfl

theorem cell22_1078307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 3].length) (baseStart_1078307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078307 prefixEnd_1078307 := by exact prefixLift 1078307
  have htrace : WordTrace (prefixWord ++ tailWord_1078307) baseStart_1078307 baseEnd_1078307 := by
    simpa [prefixWord, tailWord_1078307, baseEnd_1078307] using wordTrace_append hprefix tailTrace_1078307
  have hstable : (prefixWord ++ tailWord_1078307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078307).length < 2 ^ (prefixWord ++ tailWord_1078307).sum := by decide
  have hdescent : baseEnd_1078307 < baseStart_1078307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078324 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1078324 : Nat := 118140960795 + 1078324 * 2 ^ 59
def prefixEnd_1078324 : Nat := 4983230072969 + 3 ^ 40 * 1078324 * 2
def baseEnd_1078324 : Nat := 369132342185962857393923

theorem tailTrace_1078324 : CollatzResearch.WordTrace tailWord_1078324 prefixEnd_1078324 369132342185962857393923 := by
  unfold tailWord_1078324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19664853672711892961169013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26219804896949190614892017 19664853672711892961169013)
  ·
    refine ⟨1843580031816739965109595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19664853672711892961169013 1843580031816739965109595)
    ·
      refine ⟨2765370047725109947664393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1843580031816739965109595 2765370047725109947664393)
      ·
        refine ⟨2074027535793832460748295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2765370047725109947664393 2074027535793832460748295)
        ·
          refine ⟨3111041303690748691122443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074027535793832460748295 3111041303690748691122443)
          ·
            refine ⟨4666561955536123036683665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111041303690748691122443 4666561955536123036683665)
            ·
              refine ⟨3499921466652092277512749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4666561955536123036683665 3499921466652092277512749)
              ·
                refine ⟨1312470549994534604067281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3499921466652092277512749 1312470549994534604067281)
                ·
                  refine ⟨984352912495900953050461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312470549994534604067281 984352912495900953050461)
                  ·
                    refine ⟨369132342185962857393923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984352912495900953050461 369132342185962857393923)
                    ·
                      rfl

theorem cell22_1078324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1078324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078324 prefixEnd_1078324 := by exact prefixLift 1078324
  have htrace : WordTrace (prefixWord ++ tailWord_1078324) baseStart_1078324 baseEnd_1078324 := by
    simpa [prefixWord, tailWord_1078324, baseEnd_1078324] using wordTrace_append hprefix tailTrace_1078324
  have hstable : (prefixWord ++ tailWord_1078324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078324).length < 2 ^ (prefixWord ++ tailWord_1078324).sum := by decide
  have hdescent : baseEnd_1078324 < baseStart_1078324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078337 : List Nat := [1, 2, 5, 1, 3, 1, 3, 6]
def baseStart_1078337 : Nat := 118140960795 + 1078337 * 2 ^ 59
def prefixEnd_1078337 : Nat := 4983230072969 + 3 ^ 40 * 1078337 * 2
def baseEnd_1078337 : Nat := 41015199150181684090987

theorem tailTrace_1078337 : CollatzResearch.WordTrace tailWord_1078337 prefixEnd_1078337 41015199150181684090987 := by
  unfold tailWord_1078337
  simp only [CollatzResearch.WordTrace]
  refine ⟨39330181494376689142561265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26220120996251126095040843 39330181494376689142561265)
  ·
    refine ⟨29497636120782516856920949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39330181494376689142561265 29497636120782516856920949)
    ·
      refine ⟨2765403386323360955336339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29497636120782516856920949 2765403386323360955336339)
      ·
        refine ⟨4148105079485041433004509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765403386323360955336339 4148105079485041433004509)
        ·
          refine ⟨1555539404806890537376691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4148105079485041433004509 1555539404806890537376691)
          ·
            refine ⟨2333309107210335806065037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555539404806890537376691 2333309107210335806065037)
            ·
              refine ⟨874990915203875927274389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2333309107210335806065037 874990915203875927274389)
              ·
                refine ⟨41015199150181684090987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 874990915203875927274389 41015199150181684090987)
                ·
                  rfl

theorem cell22_1078337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 6].length) (baseStart_1078337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078337 prefixEnd_1078337 := by exact prefixLift 1078337
  have htrace : WordTrace (prefixWord ++ tailWord_1078337) baseStart_1078337 baseEnd_1078337 := by
    simpa [prefixWord, tailWord_1078337, baseEnd_1078337] using wordTrace_append hprefix tailTrace_1078337
  have hstable : (prefixWord ++ tailWord_1078337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078337).length < 2 ^ (prefixWord ++ tailWord_1078337).sum := by decide
  have hdescent : baseEnd_1078337 < baseStart_1078337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078348 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 7]
def baseStart_1078348 : Nat := 118140960795 + 1078348 * 2 ^ 59
def prefixEnd_1078348 : Nat := 4983230072969 + 3 ^ 40 * 1078348 * 2
def baseEnd_1078348 : Nat := 123046852625478264931283

theorem tailTrace_1078348 : CollatzResearch.WordTrace tailWord_1078348 prefixEnd_1078348 123046852625478264931283 := by
  unfold tailWord_1078348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19665291348668419010605849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26220388464891225347474465 19665291348668419010605849)
  ·
    refine ⟨14748968511501314257954387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19665291348668419010605849 14748968511501314257954387)
    ·
      refine ⟨22123452767251971386931581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14748968511501314257954387 22123452767251971386931581)
      ·
        refine ⟨8296294787719489270099343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22123452767251971386931581 8296294787719489270099343)
        ·
          refine ⟨12444442181579233905149015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8296294787719489270099343 12444442181579233905149015)
          ·
            refine ⟨18666663272368850857723523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12444442181579233905149015 18666663272368850857723523)
            ·
              refine ⟨27999994908553276286585285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18666663272368850857723523 27999994908553276286585285)
              ·
                refine ⟨5249999045353739303734741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27999994908553276286585285 5249999045353739303734741)
                ·
                  refine ⟨123046852625478264931283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5249999045353739303734741 123046852625478264931283)
                  ·
                    rfl

theorem cell22_1078348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_1078348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078348 prefixEnd_1078348 := by exact prefixLift 1078348
  have htrace : WordTrace (prefixWord ++ tailWord_1078348) baseStart_1078348 baseEnd_1078348 := by
    simpa [prefixWord, tailWord_1078348, baseEnd_1078348] using wordTrace_append hprefix tailTrace_1078348
  have hstable : (prefixWord ++ tailWord_1078348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078348).length < 2 ^ (prefixWord ++ tailWord_1078348).sum := by decide
  have hdescent : baseEnd_1078348 < baseStart_1078348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078358 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1078358 : Nat := 118140960795 + 1078358 * 2 ^ 59
def prefixEnd_1078358 : Nat := 4983230072969 + 3 ^ 40 * 1078358 * 2
def baseEnd_1078358 : Nat := 369143981080798102043819

theorem tailTrace_1078358 : CollatzResearch.WordTrace tailWord_1078358 prefixEnd_1078358 369143981080798102043819 := by
  unfold tailWord_1078358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458184214206288108067233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26220631618200406486050485 2458184214206288108067233)
  ·
    refine ⟨1843638160654716081050425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2458184214206288108067233 1843638160654716081050425)
    ·
      refine ⟨1382728620491037060787819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1843638160654716081050425 1382728620491037060787819)
      ·
        refine ⟨2074092930736555591181729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382728620491037060787819 2074092930736555591181729)
        ·
          refine ⟨1555569698052416693386297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2074092930736555591181729 1555569698052416693386297)
          ·
            refine ⟨1166677273539312520039723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1555569698052416693386297 1166677273539312520039723)
            ·
              refine ⟨1750015910308968780059585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166677273539312520039723 1750015910308968780059585)
              ·
                refine ⟨1312511932731726585044689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750015910308968780059585 1312511932731726585044689)
                ·
                  refine ⟨984383949548794938783517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312511932731726585044689 984383949548794938783517)
                  ·
                    refine ⟨369143981080798102043819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984383949548794938783517 369143981080798102043819)
                    ·
                      rfl

theorem cell22_1078358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1078358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078358 prefixEnd_1078358 := by exact prefixLift 1078358
  have htrace : WordTrace (prefixWord ++ tailWord_1078358) baseStart_1078358 baseEnd_1078358 := by
    simpa [prefixWord, tailWord_1078358, baseEnd_1078358] using wordTrace_append hprefix tailTrace_1078358
  have hstable : (prefixWord ++ tailWord_1078358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078358).length < 2 ^ (prefixWord ++ tailWord_1078358).sum := by decide
  have hdescent : baseEnd_1078358 < baseStart_1078358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078457 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_1078457 : Nat := 118140960795 + 1078457 * 2 ^ 59
def prefixEnd_1078457 : Nat := 4983230072969 + 3 ^ 40 * 1078457 * 2
def baseEnd_1078457 : Nat := 369177870803994843818515

theorem tailTrace_1078457 : CollatzResearch.WordTrace tailWord_1078457 prefixEnd_1078457 369177870803994843818515 := by
  unfold tailWord_1078457
  simp only [CollatzResearch.WordTrace]
  refine ⟨39334558253941949636929625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26223038835961299757953083 39334558253941949636929625)
  ·
    refine ⟨29500918690456462227697219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39334558253941949636929625 29500918690456462227697219)
    ·
      refine ⟨44251378035684693341545829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29500918690456462227697219 44251378035684693341545829)
      ·
        refine ⟨8297133381690880001539843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44251378035684693341545829 8297133381690880001539843)
        ·
          refine ⟨12445700072536320002309765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297133381690880001539843 12445700072536320002309765)
          ·
            refine ⟨2333568763600560000433081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12445700072536320002309765 2333568763600560000433081)
            ·
              refine ⟨1750176572700420000324811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333568763600560000433081 1750176572700420000324811)
              ·
                refine ⟨2625264859050630000487217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750176572700420000324811 2625264859050630000487217)
                ·
                  refine ⟨1968948644287972500365413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2625264859050630000487217 1968948644287972500365413)
                  ·
                    refine ⟨369177870803994843818515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968948644287972500365413 369177870803994843818515)
                    ·
                      rfl

theorem cell22_1078457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_1078457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078457 prefixEnd_1078457 := by exact prefixLift 1078457
  have htrace : WordTrace (prefixWord ++ tailWord_1078457) baseStart_1078457 baseEnd_1078457 := by
    simpa [prefixWord, tailWord_1078457, baseEnd_1078457] using wordTrace_append hprefix tailTrace_1078457
  have hstable : (prefixWord ++ tailWord_1078457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078457).length < 2 ^ (prefixWord ++ tailWord_1078457).sum := by decide
  have hdescent : baseEnd_1078457 < baseStart_1078457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078478 : List Nat := [4, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_1078478 : Nat := 118140960795 + 1078478 * 2 ^ 59
def prefixEnd_1078478 : Nat := 4983230072969 + 3 ^ 40 * 1078478 * 2
def baseEnd_1078478 : Nat := 123061686511052596347817

theorem tailTrace_1078478 : CollatzResearch.WordTrace tailWord_1078478 prefixEnd_1078478 123061686511052596347817 := by
  unfold tailWord_1078478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916915523358233777930511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26223549457910580148962725 4916915523358233777930511)
  ·
    refine ⟨7375373285037350666895767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4916915523358233777930511 7375373285037350666895767)
    ·
      refine ⟨11063059927556026000343651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7375373285037350666895767 11063059927556026000343651)
      ·
        refine ⟨16594589891334039000515477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11063059927556026000343651 16594589891334039000515477)
        ·
          refine ⟨777871401156283078149163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16594589891334039000515477 777871401156283078149163)
          ·
            refine ⟨1166807101734424617223745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777871401156283078149163 1166807101734424617223745)
            ·
              refine ⟨875105326300818462917809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166807101734424617223745 875105326300818462917809)
              ·
                refine ⟨656328994725613847188357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875105326300818462917809 656328994725613847188357)
                ·
                  refine ⟨123061686511052596347817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656328994725613847188357 123061686511052596347817)
                  ·
                    rfl

theorem cell22_1078478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_1078478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078478 prefixEnd_1078478 := by exact prefixLift 1078478
  have htrace : WordTrace (prefixWord ++ tailWord_1078478) baseStart_1078478 baseEnd_1078478 := by
    simpa [prefixWord, tailWord_1078478, baseEnd_1078478] using wordTrace_append hprefix tailTrace_1078478
  have hstable : (prefixWord ++ tailWord_1078478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078478).length < 2 ^ (prefixWord ++ tailWord_1078478).sum := by decide
  have hdescent : baseEnd_1078478 < baseStart_1078478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078532 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1078532 : Nat := 118140960795 + 1078532 * 2 ^ 59
def prefixEnd_1078532 : Nat := 4983230072969 + 3 ^ 40 * 1078532 * 2
def baseEnd_1078532 : Nat := 369203544836719648193285

theorem tailTrace_1078532 : CollatzResearch.WordTrace tailWord_1078532 prefixEnd_1078532 369203544836719648193285 := by
  unfold tailWord_1078532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19668646864335118722954925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26224862485780158297273233 19668646864335118722954925)
  ·
    refine ⟨7375742574125669521108097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19668646864335118722954925 7375742574125669521108097)
    ·
      refine ⟨5531806930594252140831073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7375742574125669521108097 5531806930594252140831073)
      ·
        refine ⟨4148855197945689105623305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5531806930594252140831073 4148855197945689105623305)
        ·
          refine ⟨3111641398459266829217479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4148855197945689105623305 3111641398459266829217479)
          ·
            refine ⟨4667462097688900243826219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111641398459266829217479 4667462097688900243826219)
            ·
              refine ⟨7001193146533350365739329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667462097688900243826219 7001193146533350365739329)
              ·
                refine ⟨5250894859900012774304497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7001193146533350365739329 5250894859900012774304497)
                ·
                  refine ⟨3938171144925009580728373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5250894859900012774304497 3938171144925009580728373)
                  ·
                    refine ⟨369203544836719648193285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3938171144925009580728373 369203544836719648193285)
                    ·
                      rfl

theorem cell22_1078532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1078532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078532 prefixEnd_1078532 := by exact prefixLift 1078532
  have htrace : WordTrace (prefixWord ++ tailWord_1078532) baseStart_1078532 baseEnd_1078532 := by
    simpa [prefixWord, tailWord_1078532, baseEnd_1078532] using wordTrace_append hprefix tailTrace_1078532
  have hstable : (prefixWord ++ tailWord_1078532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078532).length < 2 ^ (prefixWord ++ tailWord_1078532).sum := by decide
  have hdescent : baseEnd_1078532 < baseStart_1078532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078564 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_1078564 : Nat := 118140960795 + 1078564 * 2 ^ 59
def prefixEnd_1078564 : Nat := 4983230072969 + 3 ^ 40 * 1078564 * 2
def baseEnd_1078564 : Nat := 369214499090682231393187

theorem tailTrace_1078564 : CollatzResearch.WordTrace tailWord_1078564 prefixEnd_1078564 369214499090682231393187 := by
  unfold tailWord_1078564
  simp only [CollatzResearch.WordTrace]
  refine ⟨19669230432277153455537373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26225640576369537940716497 19669230432277153455537373)
  ·
    refine ⟨7375961412103932545826515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19669230432277153455537373 7375961412103932545826515)
    ·
      refine ⟨11063942118155898818739773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7375961412103932545826515 11063942118155898818739773)
      ·
        refine ⟨4148978294308462057027415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11063942118155898818739773 4148978294308462057027415)
        ·
          refine ⟨6223467441462693085541123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148978294308462057027415 6223467441462693085541123)
          ·
            refine ⟨9335201162194039628311685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223467441462693085541123 9335201162194039628311685)
            ·
              refine ⟨1750350217911382430308441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9335201162194039628311685 1750350217911382430308441)
              ·
                refine ⟨1312762663433536822731331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750350217911382430308441 1312762663433536822731331)
                ·
                  refine ⟨1969143995150305234096997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312762663433536822731331 1969143995150305234096997)
                  ·
                    refine ⟨369214499090682231393187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1969143995150305234096997 369214499090682231393187)
                    ·
                      rfl

theorem cell22_1078564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_1078564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078564 prefixEnd_1078564 := by exact prefixLift 1078564
  have htrace : WordTrace (prefixWord ++ tailWord_1078564) baseStart_1078564 baseEnd_1078564 := by
    simpa [prefixWord, tailWord_1078564, baseEnd_1078564] using wordTrace_append hprefix tailTrace_1078564
  have hstable : (prefixWord ++ tailWord_1078564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078564).length < 2 ^ (prefixWord ++ tailWord_1078564).sum := by decide
  have hdescent : baseEnd_1078564 < baseStart_1078564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078579 : List Nat := [1, 1, 1, 2, 5, 2, 3, 3, 4]
def baseStart_1078579 : Nat := 118140960795 + 1078579 * 2 ^ 59
def prefixEnd_1078579 : Nat := 4983230072969 + 3 ^ 40 * 1078579 * 2
def baseEnd_1078579 : Nat := 123073211299075730756047

theorem tailTrace_1078579 : CollatzResearch.WordTrace tailWord_1078579 prefixEnd_1078579 123073211299075730756047 := by
  unfold tailWord_1078579
  simp only [CollatzResearch.WordTrace]
  refine ⟨39339007959499964472870791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26226005306333309648580527 39339007959499964472870791)
  ·
    refine ⟨59008511939249946709306187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39339007959499964472870791 59008511939249946709306187)
    ·
      refine ⟨88512767908874920063959281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59008511939249946709306187 88512767908874920063959281)
      ·
        refine ⟨66384575931656190047969461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88512767908874920063959281 66384575931656190047969461)
        ·
          refine ⟨6223553993592767816997137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66384575931656190047969461 6223553993592767816997137)
          ·
            refine ⟨4667665495194575862747853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6223553993592767816997137 4667665495194575862747853)
            ·
              refine ⟨1750374560697965948530445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4667665495194575862747853 1750374560697965948530445)
              ·
                refine ⟨656390460261737230698917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1750374560697965948530445 656390460261737230698917)
                ·
                  refine ⟨123073211299075730756047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656390460261737230698917 123073211299075730756047)
                  ·
                    rfl

theorem cell22_1078579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 4].length) (baseStart_1078579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078579 prefixEnd_1078579 := by exact prefixLift 1078579
  have htrace : WordTrace (prefixWord ++ tailWord_1078579) baseStart_1078579 baseEnd_1078579 := by
    simpa [prefixWord, tailWord_1078579, baseEnd_1078579] using wordTrace_append hprefix tailTrace_1078579
  have hstable : (prefixWord ++ tailWord_1078579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078579).length < 2 ^ (prefixWord ++ tailWord_1078579).sum := by decide
  have hdescent : baseEnd_1078579 < baseStart_1078579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078592 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_1078592 : Nat := 118140960795 + 1078592 * 2 ^ 59
def prefixEnd_1078592 : Nat := 4983230072969 + 3 ^ 40 * 1078592 * 2
def baseEnd_1078592 : Nat := 369224084062899491693101

theorem tailTrace_1078592 : CollatzResearch.WordTrace tailWord_1078592 prefixEnd_1078592 369224084062899491693101 := by
  unfold tailWord_1078592
  simp only [CollatzResearch.WordTrace]
  refine ⟨19669741054226433846547015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26226321405635245128729353 19669741054226433846547015)
  ·
    refine ⟨29504611581339650769820523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19669741054226433846547015 29504611581339650769820523)
    ·
      refine ⟨44256917372009476154730785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29504611581339650769820523 44256917372009476154730785)
      ·
        refine ⟨33192688029007107116048089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44256917372009476154730785 33192688029007107116048089)
        ·
          refine ⟨24894516021755330337036067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33192688029007107116048089 24894516021755330337036067)
          ·
            refine ⟨37341774032632995505554101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24894516021755330337036067 37341774032632995505554101)
            ·
              refine ⟨3500791315559343328645697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37341774032632995505554101 3500791315559343328645697)
              ·
                refine ⟨2625593486669507496484273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3500791315559343328645697 2625593486669507496484273)
                ·
                  refine ⟨1969195115002130622363205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2625593486669507496484273 1969195115002130622363205)
                  ·
                    refine ⟨369224084062899491693101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1969195115002130622363205 369224084062899491693101)
                    ·
                      rfl

theorem cell22_1078592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_1078592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078592 prefixEnd_1078592 := by exact prefixLift 1078592
  have htrace : WordTrace (prefixWord ++ tailWord_1078592) baseStart_1078592 baseEnd_1078592 := by
    simpa [prefixWord, tailWord_1078592, baseEnd_1078592] using wordTrace_append hprefix tailTrace_1078592
  have hstable : (prefixWord ++ tailWord_1078592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078592).length < 2 ^ (prefixWord ++ tailWord_1078592).sum := by decide
  have hdescent : baseEnd_1078592 < baseStart_1078592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078596 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 6]
def baseStart_1078596 : Nat := 118140960795 + 1078596 * 2 ^ 59
def prefixEnd_1078596 : Nat := 4983230072969 + 3 ^ 40 * 1078596 * 2
def baseEnd_1078596 : Nat := 123075151114881604864363

theorem tailTrace_1078596 : CollatzResearch.WordTrace tailWord_1078596 prefixEnd_1078596 123075151114881604864363 := by
  unfold tailWord_1078596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19669814000219188188119821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26226418666958917584159761 19669814000219188188119821)
  ·
    refine ⟨7376180250082195570544933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19669814000219188188119821 7376180250082195570544933)
    ·
      refine ⟨1383033796890411669477175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7376180250082195570544933 1383033796890411669477175)
      ·
        refine ⟨2074550695335617504215763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383033796890411669477175 2074550695335617504215763)
        ·
          refine ⟨3111826043003426256323645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074550695335617504215763 3111826043003426256323645)
          ·
            refine ⟨1166934766126284846121367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3111826043003426256323645 1166934766126284846121367)
            ·
              refine ⟨1750402149189427269182051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166934766126284846121367 1750402149189427269182051)
              ·
                refine ⟨2625603223784140903773077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750402149189427269182051 2625603223784140903773077)
                ·
                  refine ⟨123075151114881604864363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2625603223784140903773077 123075151114881604864363)
                  ·
                    rfl

theorem cell22_1078596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_1078596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078596 prefixEnd_1078596 := by exact prefixLift 1078596
  have htrace : WordTrace (prefixWord ++ tailWord_1078596) baseStart_1078596 baseEnd_1078596 := by
    simpa [prefixWord, tailWord_1078596, baseEnd_1078596] using wordTrace_append hprefix tailTrace_1078596
  have hstable : (prefixWord ++ tailWord_1078596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078596).length < 2 ^ (prefixWord ++ tailWord_1078596).sum := by decide
  have hdescent : baseEnd_1078596 < baseStart_1078596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078667 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 2, 5]
def baseStart_1078667 : Nat := 118140960795 + 1078667 * 2 ^ 59
def prefixEnd_1078667 : Nat := 4983230072969 + 3 ^ 40 * 1078667 * 2
def baseEnd_1078667 : Nat := 369249758095624296067871

theorem tailTrace_1078667 : CollatzResearch.WordTrace tailWord_1078667 prefixEnd_1078667 369249758095624296067871 := by
  unfold tailWord_1078667
  simp only [CollatzResearch.WordTrace]
  refine ⟨39342217583181155502074255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26228145055454103668049503 39342217583181155502074255)
  ·
    refine ⟨59013326374771733253111383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39342217583181155502074255 59013326374771733253111383)
    ·
      refine ⟨88519989562157599879667075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59013326374771733253111383 88519989562157599879667075)
      ·
        refine ⟨132779984343236399819500613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88519989562157599879667075 132779984343236399819500613)
        ·
          refine ⟨24896247064356824966156365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132779984343236399819500613 24896247064356824966156365)
          ·
            refine ⟨9336092649133809362308637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24896247064356824966156365 9336092649133809362308637)
            ·
              refine ⟨3501034743425178510865739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9336092649133809362308637 3501034743425178510865739)
              ·
                refine ⟨5251552115137767766298609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501034743425178510865739 5251552115137767766298609)
                ·
                  refine ⟨3938664086353325824723957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251552115137767766298609 3938664086353325824723957)
                  ·
                    refine ⟨369249758095624296067871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3938664086353325824723957 369249758095624296067871)
                    ·
                      rfl

theorem cell22_1078667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_1078667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078667 prefixEnd_1078667 := by exact prefixLift 1078667
  have htrace : WordTrace (prefixWord ++ tailWord_1078667) baseStart_1078667 baseEnd_1078667 := by
    simpa [prefixWord, tailWord_1078667, baseEnd_1078667] using wordTrace_append hprefix tailTrace_1078667
  have hstable : (prefixWord ++ tailWord_1078667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078667).length < 2 ^ (prefixWord ++ tailWord_1078667).sum := by decide
  have hdescent : baseEnd_1078667 < baseStart_1078667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078712 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1078712 : Nat := 118140960795 + 1078712 * 2 ^ 59
def prefixEnd_1078712 : Nat := 4983230072969 + 3 ^ 40 * 1078712 * 2
def baseEnd_1078712 : Nat := 369265162515259178692733

theorem tailTrace_1078712 : CollatzResearch.WordTrace tailWord_1078712 prefixEnd_1078712 369265162515259178692733 := by
  unfold tailWord_1078712
  simp only [CollatzResearch.WordTrace]
  refine ⟨19671929434009064093731195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26229239245345418791641593 19671929434009064093731195)
  ·
    refine ⟨29507894151013596140596793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19671929434009064093731195 29507894151013596140596793)
    ·
      refine ⟨22130920613260197105447595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29507894151013596140596793 22130920613260197105447595)
      ·
        refine ⟨33196380919890295658171393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22130920613260197105447595 33196380919890295658171393)
        ·
          refine ⟨24897285689917721743628545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33196380919890295658171393 24897285689917721743628545)
          ·
            refine ⟨18672964267438291307721409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24897285689917721743628545 18672964267438291307721409)
            ·
              refine ⟨14004723200578718480791057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18672964267438291307721409 14004723200578718480791057)
              ·
                refine ⟨10503542400434038860593293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14004723200578718480791057 10503542400434038860593293)
                ·
                  refine ⟨3938828400162764572722485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10503542400434038860593293 3938828400162764572722485)
                  ·
                    refine ⟨369265162515259178692733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3938828400162764572722485 369265162515259178692733)
                    ·
                      rfl

theorem cell22_1078712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1078712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078712 prefixEnd_1078712 := by exact prefixLift 1078712
  have htrace : WordTrace (prefixWord ++ tailWord_1078712) baseStart_1078712 baseEnd_1078712 := by
    simpa [prefixWord, tailWord_1078712, baseEnd_1078712] using wordTrace_append hprefix tailTrace_1078712
  have hstable : (prefixWord ++ tailWord_1078712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078712).length < 2 ^ (prefixWord ++ tailWord_1078712).sum := by decide
  have hdescent : baseEnd_1078712 < baseStart_1078712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078727 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1078727 : Nat := 118140960795 + 1078727 * 2 ^ 59
def prefixEnd_1078727 : Nat := 4983230072969 + 3 ^ 40 * 1078727 * 2
def baseEnd_1078727 : Nat := 369270297321804139567687

theorem tailTrace_1078727 : CollatzResearch.WordTrace tailWord_1078727 prefixEnd_1078727 369270297321804139567687 := by
  unfold tailWord_1078727
  simp only [CollatzResearch.WordTrace]
  refine ⟨39344405962963785749258435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26229603975309190499505623 39344405962963785749258435)
  ·
    refine ⟨59016608944445678623887653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39344405962963785749258435 59016608944445678623887653)
    ·
      refine ⟨11065614177083564741978935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59016608944445678623887653 11065614177083564741978935)
      ·
        refine ⟨16598421265625347112968403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11065614177083564741978935 16598421265625347112968403)
        ·
          refine ⟨24897631898438020669452605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16598421265625347112968403 24897631898438020669452605)
          ·
            refine ⟨9336611961914257751044727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24897631898438020669452605 9336611961914257751044727)
            ·
              refine ⟨14004917942871386626567091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336611961914257751044727 14004917942871386626567091)
              ·
                refine ⟨21007376914307079939850637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14004917942871386626567091 21007376914307079939850637)
                ·
                  refine ⟨7877766342865154977443989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21007376914307079939850637 7877766342865154977443989)
                  ·
                    refine ⟨369270297321804139567687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7877766342865154977443989 369270297321804139567687)
                    ·
                      rfl

theorem cell22_1078727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1078727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078727 prefixEnd_1078727 := by exact prefixLift 1078727
  have htrace : WordTrace (prefixWord ++ tailWord_1078727) baseStart_1078727 baseEnd_1078727 := by
    simpa [prefixWord, tailWord_1078727, baseEnd_1078727] using wordTrace_append hprefix tailTrace_1078727
  have hstable : (prefixWord ++ tailWord_1078727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078727).length < 2 ^ (prefixWord ++ tailWord_1078727).sum := by decide
  have hdescent : baseEnd_1078727 < baseStart_1078727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078759 : List Nat := [1, 1, 5, 2, 1, 4, 8]
def baseStart_1078759 : Nat := 118140960795 + 1078759 * 2 ^ 59
def prefixEnd_1078759 : Nat := 4983230072969 + 3 ^ 40 * 1078759 * 2
def baseEnd_1078759 : Nat := 13677083391695063806207

theorem tailTrace_1078759 : CollatzResearch.WordTrace tailWord_1078759 prefixEnd_1078759 13677083391695063806207 := by
  unfold tailWord_1078759
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345573098847855214423331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26230382065898570142948887 39345573098847855214423331)
  ·
    refine ⟨59018359648271782821634997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39345573098847855214423331 59018359648271782821634997)
    ·
      refine ⟨5532971217025479639528281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59018359648271782821634997 5532971217025479639528281)
      ·
        refine ⟨4149728412769109729646211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5532971217025479639528281 4149728412769109729646211)
        ·
          refine ⟨6224592619153664594469317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149728412769109729646211 6224592619153664594469317)
          ·
            refine ⟨1167111116091312111462997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6224592619153664594469317 1167111116091312111462997)
            ·
              refine ⟨13677083391695063806207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1167111116091312111462997 13677083391695063806207)
              ·
                rfl

theorem cell22_1078759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 8].length) (baseStart_1078759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078759 prefixEnd_1078759 := by exact prefixLift 1078759
  have htrace : WordTrace (prefixWord ++ tailWord_1078759) baseStart_1078759 baseEnd_1078759 := by
    simpa [prefixWord, tailWord_1078759, baseEnd_1078759] using wordTrace_append hprefix tailTrace_1078759
  have hstable : (prefixWord ++ tailWord_1078759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078759).length < 2 ^ (prefixWord ++ tailWord_1078759).sum := by decide
  have hdescent : baseEnd_1078759 < baseStart_1078759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078765 : List Nat := [1, 5, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1078765 : Nat := 118140960795 + 1078765 * 2 ^ 59
def prefixEnd_1078765 : Nat := 4983230072969 + 3 ^ 40 * 1078765 * 2
def baseEnd_1078765 : Nat := 123094435166128235705857

theorem tailTrace_1078765 : CollatzResearch.WordTrace tailWord_1078765 prefixEnd_1078765 123094435166128235705857 := by
  unfold tailWord_1078765
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345791936826118239141749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26230527957884078826094499 39345791936826118239141749)
  ·
    refine ⟨3688667994077448584919539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39345791936826118239141749 3688667994077448584919539)
    ·
      refine ⟨5533001991116172877379309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688667994077448584919539 5533001991116172877379309)
      ·
        refine ⟨2074875746668564829017241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5533001991116172877379309 2074875746668564829017241)
        ·
          refine ⟨1556156810001423621762931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2074875746668564829017241 1556156810001423621762931)
          ·
            refine ⟨2334235215002135432644397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556156810001423621762931 2334235215002135432644397)
            ·
              refine ⟨875338205625800787241649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2334235215002135432644397 875338205625800787241649)
              ·
                refine ⟨656503654219350590431237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875338205625800787241649 656503654219350590431237)
                ·
                  refine ⟨123094435166128235705857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656503654219350590431237 123094435166128235705857)
                  ·
                    rfl

theorem cell22_1078765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1078765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078765 prefixEnd_1078765 := by exact prefixLift 1078765
  have htrace : WordTrace (prefixWord ++ tailWord_1078765) baseStart_1078765 baseEnd_1078765 := by
    simpa [prefixWord, tailWord_1078765, baseEnd_1078765] using wordTrace_append hprefix tailTrace_1078765
  have hstable : (prefixWord ++ tailWord_1078765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078765).length < 2 ^ (prefixWord ++ tailWord_1078765).sum := by decide
  have hdescent : baseEnd_1078765 < baseStart_1078765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078787 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 9]
def baseStart_1078787 : Nat := 118140960795 + 1078787 * 2 ^ 59
def prefixEnd_1078787 : Nat := 4983230072969 + 3 ^ 40 * 1078787 * 2
def baseEnd_1078787 : Nat := 123096945515994661022501

theorem tailTrace_1078787 : CollatzResearch.WordTrace tailWord_1078787 prefixEnd_1078787 123096945515994661022501 := by
  unfold tailWord_1078787
  simp only [CollatzResearch.WordTrace]
  refine ⟨39346594342746415996442615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26231062895164277330961743 39346594342746415996442615)
  ·
    refine ⟨59019891514119623994663923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39346594342746415996442615 59019891514119623994663923)
    ·
      refine ⟨88529837271179435991995885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59019891514119623994663923 88529837271179435991995885)
      ·
        refine ⟨33198688976692288496998457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88529837271179435991995885 33198688976692288496998457)
        ·
          refine ⟨24899016732519216372748843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33198688976692288496998457 24899016732519216372748843)
          ·
            refine ⟨37348525098778824559123265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24899016732519216372748843 37348525098778824559123265)
            ·
              refine ⟨28011393824084118419342449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37348525098778824559123265 28011393824084118419342449)
              ·
                refine ⟨21008545368063088814506837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28011393824084118419342449 21008545368063088814506837)
                ·
                  refine ⟨123096945515994661022501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21008545368063088814506837 123096945515994661022501)
                  ·
                    rfl

theorem cell22_1078787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_1078787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078787 prefixEnd_1078787 := by exact prefixLift 1078787
  have htrace : WordTrace (prefixWord ++ tailWord_1078787) baseStart_1078787 baseEnd_1078787 := by
    simpa [prefixWord, tailWord_1078787, baseEnd_1078787] using wordTrace_append hprefix tailTrace_1078787
  have hstable : (prefixWord ++ tailWord_1078787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078787).length < 2 ^ (prefixWord ++ tailWord_1078787).sum := by decide
  have hdescent : baseEnd_1078787 < baseStart_1078787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078814 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1078814 : Nat := 118140960795 + 1078814 * 2 ^ 59
def prefixEnd_1078814 : Nat := 4983230072969 + 3 ^ 40 * 1078814 * 2
def baseEnd_1078814 : Nat := 369300079199764912642421

theorem tailTrace_1078814 : CollatzResearch.WordTrace tailWord_1078814 prefixEnd_1078814 369300079199764912642421 := by
  unfold tailWord_1078814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4918447389206074950959437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26231719409099066405116997 4918447389206074950959437)
  ·
    refine ⟨1844417770952278106609789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4918447389206074950959437 1844417770952278106609789)
    ·
      refine ⟨691656664107104289978671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1844417770952278106609789 691656664107104289978671)
      ·
        refine ⟨1037484996160656434968007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691656664107104289978671 1037484996160656434968007)
        ·
          refine ⟨1556227494240984652452011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037484996160656434968007 1556227494240984652452011)
          ·
            refine ⟨2334341241361476978678017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556227494240984652452011 2334341241361476978678017)
            ·
              refine ⟨1750755931021107734008513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334341241361476978678017 1750755931021107734008513)
              ·
                refine ⟨1313066948265830800506385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750755931021107734008513 1313066948265830800506385)
                ·
                  refine ⟨984800211199373100379789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313066948265830800506385 984800211199373100379789)
                  ·
                    refine ⟨369300079199764912642421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984800211199373100379789 369300079199764912642421)
                    ·
                      rfl

theorem cell22_1078814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1078814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078814 prefixEnd_1078814 := by exact prefixLift 1078814
  have htrace : WordTrace (prefixWord ++ tailWord_1078814) baseStart_1078814 baseEnd_1078814 := by
    simpa [prefixWord, tailWord_1078814, baseEnd_1078814] using wordTrace_append hprefix tailTrace_1078814
  have hstable : (prefixWord ++ tailWord_1078814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078814).length < 2 ^ (prefixWord ++ tailWord_1078814).sum := by decide
  have hdescent : baseEnd_1078814 < baseStart_1078814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078864 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_1078864 : Nat := 118140960795 + 1078864 * 2 ^ 59
def prefixEnd_1078864 : Nat := 4983230072969 + 3 ^ 40 * 1078864 * 2
def baseEnd_1078864 : Nat := 369317195221581448892267

theorem tailTrace_1078864 : CollatzResearch.WordTrace tailWord_1078864 prefixEnd_1078864 369317195221581448892267 := by
  unfold tailWord_1078864
  simp only [CollatzResearch.WordTrace]
  refine ⟨19674701381733729073497823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26232935175644972097997097 19674701381733729073497823)
  ·
    refine ⟨29512052072600593610246735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19674701381733729073497823 29512052072600593610246735)
    ·
      refine ⟨44268078108900890415370103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29512052072600593610246735 44268078108900890415370103)
      ·
        refine ⟨66402117163351335623055155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44268078108900890415370103 66402117163351335623055155)
        ·
          refine ⟨99603175745027003434582733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66402117163351335623055155 99603175745027003434582733)
          ·
            refine ⟨37351190904385126287968525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99603175745027003434582733 37351190904385126287968525)
            ·
              refine ⟨14006696589144422357988197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37351190904385126287968525 14006696589144422357988197)
              ·
                refine ⟨2626255610464579192122787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14006696589144422357988197 2626255610464579192122787)
                ·
                  refine ⟨3939383415696868788184181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626255610464579192122787 3939383415696868788184181)
                  ·
                    refine ⟨369317195221581448892267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3939383415696868788184181 369317195221581448892267)
                    ·
                      rfl

theorem cell22_1078864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_1078864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078864 prefixEnd_1078864 := by exact prefixLift 1078864
  have htrace : WordTrace (prefixWord ++ tailWord_1078864) baseStart_1078864 baseEnd_1078864 := by
    simpa [prefixWord, tailWord_1078864, baseEnd_1078864] using wordTrace_append hprefix tailTrace_1078864
  have hstable : (prefixWord ++ tailWord_1078864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078864).length < 2 ^ (prefixWord ++ tailWord_1078864).sum := by decide
  have hdescent : baseEnd_1078864 < baseStart_1078864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078881 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1078881 : Nat := 118140960795 + 1078881 * 2 ^ 59
def prefixEnd_1078881 : Nat := 4983230072969 + 3 ^ 40 * 1078881 * 2
def baseEnd_1078881 : Nat := 369323014668999071217215

theorem tailTrace_1078881 : CollatzResearch.WordTrace tailWord_1078881 prefixEnd_1078881 369323014668999071217215 := by
  unfold tailWord_1078881
  simp only [CollatzResearch.WordTrace]
  refine ⟨39350022804405870050364497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26233348536270580033576331 39350022804405870050364497)
  ·
    refine ⟨29512517103304402537773373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39350022804405870050364497 29512517103304402537773373)
    ·
      refine ⟨11067193913739150951665015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29512517103304402537773373 11067193913739150951665015)
      ·
        refine ⟨16600790870608726427497523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11067193913739150951665015 16600790870608726427497523)
        ·
          refine ⟨24901186305913089641246285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16600790870608726427497523 24901186305913089641246285)
          ·
            refine ⟨9337944864717408615467357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24901186305913089641246285 9337944864717408615467357)
            ·
              refine ⟨3501729324269028230800259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9337944864717408615467357 3501729324269028230800259)
              ·
                refine ⟨5252593986403542346200389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501729324269028230800259 5252593986403542346200389)
                ·
                  refine ⟨984861372450664189912573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5252593986403542346200389 984861372450664189912573)
                  ·
                    refine ⟨369323014668999071217215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984861372450664189912573 369323014668999071217215)
                    ·
                      rfl

theorem cell22_1078881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1078881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078881 prefixEnd_1078881 := by exact prefixLift 1078881
  have htrace : WordTrace (prefixWord ++ tailWord_1078881) baseStart_1078881 baseEnd_1078881 := by
    simpa [prefixWord, tailWord_1078881, baseEnd_1078881] using wordTrace_append hprefix tailTrace_1078881
  have hstable : (prefixWord ++ tailWord_1078881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078881).length < 2 ^ (prefixWord ++ tailWord_1078881).sum := by decide
  have hdescent : baseEnd_1078881 < baseStart_1078881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078898 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_1078898 : Nat := 118140960795 + 1078898 * 2 ^ 59
def prefixEnd_1078898 : Nat := 4983230072969 + 3 ^ 40 * 1078898 * 2
def baseEnd_1078898 : Nat := 369328834116416693542163

theorem tailTrace_1078898 : CollatzResearch.WordTrace tailWord_1078898 prefixEnd_1078898 369328834116416693542163 := by
  unfold tailWord_1078898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9837660711336070488433337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26233761896896187969155565 9837660711336070488433337)
  ·
    refine ⟨7378245533502052866325003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9837660711336070488433337 7378245533502052866325003)
    ·
      refine ⟨11067368300253079299487505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7378245533502052866325003 11067368300253079299487505)
      ·
        refine ⟨8300526225189809474615629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11067368300253079299487505 8300526225189809474615629)
        ·
          refine ⟨3112697334446178552980861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8300526225189809474615629 3112697334446178552980861)
          ·
            refine ⟨1167261500417316957367823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3112697334446178552980861 1167261500417316957367823)
            ·
              refine ⟨1750892250625975436051735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167261500417316957367823 1750892250625975436051735)
              ·
                refine ⟨2626338375938963154077603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750892250625975436051735 2626338375938963154077603)
                ·
                  refine ⟨3939507563908444731116405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626338375938963154077603 3939507563908444731116405)
                  ·
                    refine ⟨369328834116416693542163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3939507563908444731116405 369328834116416693542163)
                    ·
                      rfl

theorem cell22_1078898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_1078898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078898 prefixEnd_1078898 := by exact prefixLift 1078898
  have htrace : WordTrace (prefixWord ++ tailWord_1078898) baseStart_1078898 baseEnd_1078898 := by
    simpa [prefixWord, tailWord_1078898, baseEnd_1078898] using wordTrace_append hprefix tailTrace_1078898
  have hstable : (prefixWord ++ tailWord_1078898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078898).length < 2 ^ (prefixWord ++ tailWord_1078898).sum := by decide
  have hdescent : baseEnd_1078898 < baseStart_1078898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078994 : List Nat := [3, 2, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1078994 : Nat := 118140960795 + 1078994 * 2 ^ 59
def prefixEnd_1078994 : Nat := 4983230072969 + 3 ^ 40 * 1078994 * 2
def baseEnd_1078994 : Nat := 369361696878304443141869

theorem tailTrace_1078994 : CollatzResearch.WordTrace tailWord_1078994 prefixEnd_1078994 369361696878304443141869 := by
  unfold tailWord_1078994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838536063249122587307009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26236096168664326899485357 9838536063249122587307009)
  ·
    refine ⟨7378902047436841940480257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9838536063249122587307009 7378902047436841940480257)
    ·
      refine ⟨5534176535577631455360193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7378902047436841940480257 5534176535577631455360193)
      ·
        refine ⟨4150632401683223591520145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5534176535577631455360193 4150632401683223591520145)
        ·
          refine ⟨3112974301262417693640109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4150632401683223591520145 3112974301262417693640109)
          ·
            refine ⟨1167365362973406635115041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3112974301262417693640109 1167365362973406635115041)
            ·
              refine ⟨875524022230054976336281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167365362973406635115041 875524022230054976336281)
              ·
                refine ⟨656643016672541232252211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875524022230054976336281 656643016672541232252211)
                ·
                  refine ⟨984964525008811848378317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656643016672541232252211 984964525008811848378317)
                  ·
                    refine ⟨369361696878304443141869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984964525008811848378317 369361696878304443141869)
                    ·
                      rfl

theorem cell22_1078994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1078994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1078994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1078994 prefixEnd_1078994 := by exact prefixLift 1078994
  have htrace : WordTrace (prefixWord ++ tailWord_1078994) baseStart_1078994 baseEnd_1078994 := by
    simpa [prefixWord, tailWord_1078994, baseEnd_1078994] using wordTrace_append hprefix tailTrace_1078994
  have hstable : (prefixWord ++ tailWord_1078994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078994).length < 2 ^ (prefixWord ++ tailWord_1078994).sum := by decide
  have hdescent : baseEnd_1078994 < baseStart_1078994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079005 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1079005 : Nat := 118140960795 + 1079005 * 2 ^ 59
def prefixEnd_1079005 : Nat := 4983230072969 + 3 ^ 40 * 1079005 * 2
def baseEnd_1079005 : Nat := 369365462403104081116835

theorem tailTrace_1079005 : CollatzResearch.WordTrace tailWord_1079005 prefixEnd_1079005 369365462403104081116835 := by
  unfold tailWord_1079005
  simp only [CollatzResearch.WordTrace]
  refine ⟨39354545455956639227878469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26236363637304426151918979 39354545455956639227878469)
  ·
    refine ⟨7378977272991869855227213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39354545455956639227878469 7378977272991869855227213)
    ·
      refine ⟨2767116477371951195710205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7378977272991869855227213 2767116477371951195710205)
      ·
        refine ⟨1037668679014481698391327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2767116477371951195710205 1037668679014481698391327)
        ·
          refine ⟨1556503018521722547586991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037668679014481698391327 1556503018521722547586991)
          ·
            refine ⟨2334754527782583821380487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556503018521722547586991 2334754527782583821380487)
            ·
              refine ⟨3502131791673875732070731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334754527782583821380487 3502131791673875732070731)
              ·
                refine ⟨5253197687510813598106097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3502131791673875732070731 5253197687510813598106097)
                ·
                  refine ⟨3939898265633110198579573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5253197687510813598106097 3939898265633110198579573)
                  ·
                    refine ⟨369365462403104081116835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3939898265633110198579573 369365462403104081116835)
                    ·
                      rfl

theorem cell22_1079005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1079005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079005 prefixEnd_1079005 := by exact prefixLift 1079005
  have htrace : WordTrace (prefixWord ++ tailWord_1079005) baseStart_1079005 baseEnd_1079005 := by
    simpa [prefixWord, tailWord_1079005, baseEnd_1079005] using wordTrace_append hprefix tailTrace_1079005
  have hstable : (prefixWord ++ tailWord_1079005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079005).length < 2 ^ (prefixWord ++ tailWord_1079005).sum := by decide
  have hdescent : baseEnd_1079005 < baseStart_1079005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079050 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_1079050 : Nat := 118140960795 + 1079050 * 2 ^ 59
def prefixEnd_1079050 : Nat := 4983230072969 + 3 ^ 40 * 1079050 * 2
def baseEnd_1079050 : Nat := 369380866822738963741697

theorem tailTrace_1079050 : CollatzResearch.WordTrace tailWord_1079050 prefixEnd_1079050 369380866822738963741697 := by
  unfold tailWord_1079050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9839046685198402978316651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26237457827195741275511069 9839046685198402978316651)
  ·
    refine ⟨14758570027797604467474977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9839046685198402978316651 14758570027797604467474977)
    ·
      refine ⟨11068927520848203350606233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14758570027797604467474977 11068927520848203350606233)
      ·
        refine ⟨8301695640636152512954675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11068927520848203350606233 8301695640636152512954675)
        ·
          refine ⟨12452543460954228769432013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8301695640636152512954675 12452543460954228769432013)
          ·
            refine ⟨4669703797857835788537005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12452543460954228769432013 4669703797857835788537005)
            ·
              refine ⟨1751138924196688420701377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4669703797857835788537005 1751138924196688420701377)
              ·
                refine ⟨1313354193147516315526033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751138924196688420701377 1313354193147516315526033)
                ·
                  refine ⟨985015644860637236644525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313354193147516315526033 985015644860637236644525)
                  ·
                    refine ⟨369380866822738963741697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985015644860637236644525 369380866822738963741697)
                    ·
                      rfl

theorem cell22_1079050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_1079050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079050 prefixEnd_1079050 := by exact prefixLift 1079050
  have htrace : WordTrace (prefixWord ++ tailWord_1079050) baseStart_1079050 baseEnd_1079050 := by
    simpa [prefixWord, tailWord_1079050, baseEnd_1079050] using wordTrace_append hprefix tailTrace_1079050
  have hstable : (prefixWord ++ tailWord_1079050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079050).length < 2 ^ (prefixWord ++ tailWord_1079050).sum := by decide
  have hdescent : baseEnd_1079050 < baseStart_1079050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079080 : List Nat := [2, 1, 5, 1, 1, 4, 2, 6]
def baseStart_1079080 : Nat := 118140960795 + 1079080 * 2 ^ 59
def prefixEnd_1079080 : Nat := 4983230072969 + 3 ^ 40 * 1079080 * 2
def baseEnd_1079080 : Nat := 41043459603980987276845

theorem tailTrace_1079080 : CollatzResearch.WordTrace tailWord_1079080 prefixEnd_1079080 41043459603980987276845 := by
  unfold tailWord_1079080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19678640465342463518429347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26238187287123284691239129 19678640465342463518429347)
  ·
    refine ⟨29517960698013695277644021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19678640465342463518429347 29517960698013695277644021)
    ·
      refine ⟨2767308815438783932279127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29517960698013695277644021 2767308815438783932279127)
      ·
        refine ⟨4150963223158175898418691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2767308815438783932279127 4150963223158175898418691)
        ·
          refine ⟨6226444834737263847628037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150963223158175898418691 6226444834737263847628037)
          ·
            refine ⟨1167458406513236971430257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6226444834737263847628037 1167458406513236971430257)
            ·
              refine ⟨875593804884927728572693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167458406513236971430257 875593804884927728572693)
              ·
                refine ⟨41043459603980987276845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 875593804884927728572693 41043459603980987276845)
                ·
                  rfl

theorem cell22_1079080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 6].length) (baseStart_1079080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079080 prefixEnd_1079080 := by exact prefixLift 1079080
  have htrace : WordTrace (prefixWord ++ tailWord_1079080) baseStart_1079080 baseEnd_1079080 := by
    simpa [prefixWord, tailWord_1079080, baseEnd_1079080] using wordTrace_append hprefix tailTrace_1079080
  have hstable : (prefixWord ++ tailWord_1079080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079080).length < 2 ^ (prefixWord ++ tailWord_1079080).sum := by decide
  have hdescent : baseEnd_1079080 < baseStart_1079080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079095 : List Nat := [1, 1, 3, 1, 2, 1, 2, 7, 1, 3]
def baseStart_1079095 : Nat := 118140960795 + 1079095 * 2 ^ 59
def prefixEnd_1079095 : Nat := 4983230072969 + 3 ^ 40 * 1079095 * 2
def baseEnd_1079095 : Nat := 369396271242373846366559

theorem tailTrace_1079095 : CollatzResearch.WordTrace tailWord_1079095 prefixEnd_1079095 369396271242373846366559 := by
  unfold tailWord_1079095
  simp only [CollatzResearch.WordTrace]
  refine ⟨39357828025630584598654739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26238552017087056399103159 39357828025630584598654739)
  ·
    refine ⟨59036742038445876897982109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39357828025630584598654739 59036742038445876897982109)
    ·
      refine ⟨22138778264417203836743291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59036742038445876897982109 22138778264417203836743291)
      ·
        refine ⟨33208167396625805755114937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22138778264417203836743291 33208167396625805755114937)
        ·
          refine ⟨24906125547469354316336203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33208167396625805755114937 24906125547469354316336203)
          ·
            refine ⟨37359188321204031474504305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24906125547469354316336203 37359188321204031474504305)
            ·
              refine ⟨28019391240903023605878229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37359188321204031474504305 28019391240903023605878229)
              ·
                refine ⟨656704482208664615762771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28019391240903023605878229 656704482208664615762771)
                ·
                  refine ⟨985056723312996923644157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656704482208664615762771 985056723312996923644157)
                  ·
                    refine ⟨369396271242373846366559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985056723312996923644157 369396271242373846366559)
                    ·
                      rfl

theorem cell22_1079095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_1079095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079095 prefixEnd_1079095 := by exact prefixLift 1079095
  have htrace : WordTrace (prefixWord ++ tailWord_1079095) baseStart_1079095 baseEnd_1079095 := by
    simpa [prefixWord, tailWord_1079095, baseEnd_1079095] using wordTrace_append hprefix tailTrace_1079095
  have hstable : (prefixWord ++ tailWord_1079095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079095).length < 2 ^ (prefixWord ++ tailWord_1079095).sum := by decide
  have hdescent : baseEnd_1079095 < baseStart_1079095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079125 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 5]
def baseStart_1079125 : Nat := 118140960795 + 1079125 * 2 ^ 59
def prefixEnd_1079125 : Nat := 4983230072969 + 3 ^ 40 * 1079125 * 2
def baseEnd_1079125 : Nat := 123135513618487922705489

theorem tailTrace_1079125 : CollatzResearch.WordTrace tailWord_1079125 prefixEnd_1079125 123135513618487922705489 := by
  unfold tailWord_1079125
  simp only [CollatzResearch.WordTrace]
  refine ⟨39358922215521899722246829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26239281477014599814831219 39358922215521899722246829)
  ·
    refine ⟨14759595830820712395842561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39358922215521899722246829 14759595830820712395842561)
    ·
      refine ⟨11069696873115534296881921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14759595830820712395842561 11069696873115534296881921)
      ·
        refine ⟨8302272654836650722661441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11069696873115534296881921 8302272654836650722661441)
        ·
          refine ⟨6226704491127488041996081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8302272654836650722661441 6226704491127488041996081)
          ·
            refine ⟨4670028368345616031497061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6226704491127488041996081 4670028368345616031497061)
            ·
              refine ⟨875630319064803005905699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4670028368345616031497061 875630319064803005905699)
              ·
                refine ⟨1313445478597204508858549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875630319064803005905699 1313445478597204508858549)
                ·
                  refine ⟨123135513618487922705489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1313445478597204508858549 123135513618487922705489)
                  ·
                    rfl

theorem cell22_1079125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_1079125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079125 prefixEnd_1079125 := by exact prefixLift 1079125
  have htrace : WordTrace (prefixWord ++ tailWord_1079125) baseStart_1079125 baseEnd_1079125 := by
    simpa [prefixWord, tailWord_1079125, baseEnd_1079125] using wordTrace_append hprefix tailTrace_1079125
  have hstable : (prefixWord ++ tailWord_1079125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079125).length < 2 ^ (prefixWord ++ tailWord_1079125).sum := by decide
  have hdescent : baseEnd_1079125 < baseStart_1079125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079185 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 2, 3]
def baseStart_1079185 : Nat := 118140960795 + 1079185 * 2 ^ 59
def prefixEnd_1079185 : Nat := 4983230072969 + 3 ^ 40 * 1079185 * 2
def baseEnd_1079185 : Nat := 369427080081643611616283

theorem tailTrace_1079185 : CollatzResearch.WordTrace tailWord_1079185 prefixEnd_1079185 369427080081643611616283 := by
  unfold tailWord_1079185
  simp only [CollatzResearch.WordTrace]
  refine ⟨39361110595304529969431009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26240740396869686646287339 39361110595304529969431009)
  ·
    refine ⟨29520832946478397477073257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39361110595304529969431009 29520832946478397477073257)
    ·
      refine ⟨22140624709858798107804943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29520832946478397477073257 22140624709858798107804943)
      ·
        refine ⟨33210937064788197161707415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22140624709858798107804943 33210937064788197161707415)
        ·
          refine ⟨49816405597182295742561123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33210937064788197161707415 49816405597182295742561123)
          ·
            refine ⟨74724608395773443613841685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49816405597182295742561123 74724608395773443613841685)
            ·
              refine ⟨3502716018551880169398829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74724608395773443613841685 3502716018551880169398829)
              ·
                refine ⟨1313518506956955063524561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3502716018551880169398829 1313518506956955063524561)
                ·
                  refine ⟨985138880217716297643421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313518506956955063524561 985138880217716297643421)
                  ·
                    refine ⟨369427080081643611616283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985138880217716297643421 369427080081643611616283)
                    ·
                      rfl

theorem cell22_1079185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_1079185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079185 prefixEnd_1079185 := by exact prefixLift 1079185
  have htrace : WordTrace (prefixWord ++ tailWord_1079185) baseStart_1079185 baseEnd_1079185 := by
    simpa [prefixWord, tailWord_1079185, baseEnd_1079185] using wordTrace_append hprefix tailTrace_1079185
  have hstable : (prefixWord ++ tailWord_1079185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079185).length < 2 ^ (prefixWord ++ tailWord_1079185).sum := by decide
  have hdescent : baseEnd_1079185 < baseStart_1079185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079281 : List Nat := [1, 2, 2, 2, 5, 1, 3, 2, 1, 3]
def baseStart_1079281 : Nat := 118140960795 + 1079281 * 2 ^ 59
def prefixEnd_1079281 : Nat := 4983230072969 + 3 ^ 40 * 1079281 * 2
def baseEnd_1079281 : Nat := 369459942843531361215989

theorem tailTrace_1079281 : CollatzResearch.WordTrace tailWord_1079281 prefixEnd_1079281 369459942843531361215989 := by
  unfold tailWord_1079281
  simp only [CollatzResearch.WordTrace]
  refine ⟨39364612002956738364925697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26243074668637825576617131 39364612002956738364925697)
  ·
    refine ⟨29523459002217553773694273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39364612002956738364925697 29523459002217553773694273)
    ·
      refine ⟨22142594251663165330270705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29523459002217553773694273 22142594251663165330270705)
      ·
        refine ⟨16606945688747373997703029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22142594251663165330270705 16606945688747373997703029)
        ·
          refine ⟨1556901158320066312284659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16606945688747373997703029 1556901158320066312284659)
          ·
            refine ⟨2335351737480099468426989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556901158320066312284659 2335351737480099468426989)
            ·
              refine ⟨875756901555037300660121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2335351737480099468426989 875756901555037300660121)
              ·
                refine ⟨656817676166277975495091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875756901555037300660121 656817676166277975495091)
                ·
                  refine ⟨985226514249416963242637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656817676166277975495091 985226514249416963242637)
                  ·
                    refine ⟨369459942843531361215989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985226514249416963242637 369459942843531361215989)
                    ·
                      rfl

theorem cell22_1079281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_1079281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079281 prefixEnd_1079281 := by exact prefixLift 1079281
  have htrace : WordTrace (prefixWord ++ tailWord_1079281) baseStart_1079281 baseEnd_1079281 := by
    simpa [prefixWord, tailWord_1079281, baseEnd_1079281] using wordTrace_append hprefix tailTrace_1079281
  have hstable : (prefixWord ++ tailWord_1079281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079281).length < 2 ^ (prefixWord ++ tailWord_1079281).sum := by decide
  have hdescent : baseEnd_1079281 < baseStart_1079281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079294 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1079294 : Nat := 118140960795 + 1079294 * 2 ^ 59
def prefixEnd_1079294 : Nat := 4983230072969 + 3 ^ 40 * 1079294 * 2
def baseEnd_1079294 : Nat := 123154797669734553546983

theorem tailTrace_1079294 : CollatzResearch.WordTrace tailWord_1079294 prefixEnd_1079294 123154797669734553546983 := by
  unfold tailWord_1079294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4920635768988705198143617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26243390767939761056765957 4920635768988705198143617)
  ·
    refine ⟨3690476826741528898607713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4920635768988705198143617 3690476826741528898607713)
    ·
      refine ⟨2767857620056146673955785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3690476826741528898607713 2767857620056146673955785)
      ·
        refine ⟨2075893215042110005466839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2767857620056146673955785 2075893215042110005466839)
        ·
          refine ⟨3113839822563165008200259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075893215042110005466839 3113839822563165008200259)
          ·
            refine ⟨4670759733844747512300389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3113839822563165008200259 4670759733844747512300389)
            ·
              refine ⟨875767450095890158556323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4670759733844747512300389 875767450095890158556323)
              ·
                refine ⟨1313651175143835237834485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875767450095890158556323 1313651175143835237834485)
                ·
                  refine ⟨123154797669734553546983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1313651175143835237834485 123154797669734553546983)
                  ·
                    rfl

theorem cell22_1079294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1079294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079294 prefixEnd_1079294 := by exact prefixLift 1079294
  have htrace : WordTrace (prefixWord ++ tailWord_1079294) baseStart_1079294 baseEnd_1079294 := by
    simpa [prefixWord, tailWord_1079294, baseEnd_1079294] using wordTrace_append hprefix tailTrace_1079294
  have hstable : (prefixWord ++ tailWord_1079294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079294).length < 2 ^ (prefixWord ++ tailWord_1079294).sum := by decide
  have hdescent : baseEnd_1079294 < baseStart_1079294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079320 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_1079320 : Nat := 118140960795 + 1079320 * 2 ^ 59
def prefixEnd_1079320 : Nat := 4983230072969 + 3 ^ 40 * 1079320 * 2
def baseEnd_1079320 : Nat := 369473293340548259490869

theorem tailTrace_1079320 : CollatzResearch.WordTrace tailWord_1079320 prefixEnd_1079320 369473293340548259490869 := by
  unfold tailWord_1079320
  simp only [CollatzResearch.WordTrace]
  refine ⟨19683017224907724012797707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26244022966543632017063609 19683017224907724012797707)
  ·
    refine ⟨29524525837361586019196561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19683017224907724012797707 29524525837361586019196561)
    ·
      refine ⟨22143394378021189514397421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29524525837361586019196561 22143394378021189514397421)
      ·
        refine ⟨8303772891757946067899033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22143394378021189514397421 8303772891757946067899033)
        ·
          refine ⟨6227829668818459550924275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8303772891757946067899033 6227829668818459550924275)
          ·
            refine ⟨9341744503227689326386413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6227829668818459550924275 9341744503227689326386413)
            ·
              refine ⟨3503154188710383497394905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9341744503227689326386413 3503154188710383497394905)
              ·
                refine ⟨2627365641532787623046179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503154188710383497394905 2627365641532787623046179)
                ·
                  refine ⟨3941048462299181434569269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627365641532787623046179 3941048462299181434569269)
                  ·
                    refine ⟨369473293340548259490869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3941048462299181434569269 369473293340548259490869)
                    ·
                      rfl

theorem cell22_1079320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_1079320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079320 prefixEnd_1079320 := by exact prefixLift 1079320
  have htrace : WordTrace (prefixWord ++ tailWord_1079320) baseStart_1079320 baseEnd_1079320 := by
    simpa [prefixWord, tailWord_1079320, baseEnd_1079320] using wordTrace_append hprefix tailTrace_1079320
  have hstable : (prefixWord ++ tailWord_1079320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079320).length < 2 ^ (prefixWord ++ tailWord_1079320).sum := by decide
  have hdescent : baseEnd_1079320 < baseStart_1079320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079324 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1079324 : Nat := 118140960795 + 1079324 * 2 ^ 59
def prefixEnd_1079324 : Nat := 4983230072969 + 3 ^ 40 * 1079324 * 2
def baseEnd_1079324 : Nat := 369474662622293582390857

theorem tailTrace_1079324 : CollatzResearch.WordTrace tailWord_1079324 prefixEnd_1079324 369474662622293582390857 := by
  unfold tailWord_1079324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19683090170900478354370513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26244120227867304472494017 19683090170900478354370513)
  ·
    refine ⟨14762317628175358765777885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19683090170900478354370513 14762317628175358765777885)
    ·
      refine ⟨5535869110565759537166707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14762317628175358765777885 5535869110565759537166707)
      ·
        refine ⟨8303803665848639305750061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535869110565759537166707 8303803665848639305750061)
        ·
          refine ⟨3113926374693239739656273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8303803665848639305750061 3113926374693239739656273)
          ·
            refine ⟨2335444781019929804742205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3113926374693239739656273 2335444781019929804742205)
            ·
              refine ⟨875791792882473676778327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2335444781019929804742205 875791792882473676778327)
              ·
                refine ⟨1313687689323710515167491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875791792882473676778327 1313687689323710515167491)
                ·
                  refine ⟨1970531533985565772751237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1313687689323710515167491 1970531533985565772751237)
                  ·
                    refine ⟨369474662622293582390857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970531533985565772751237 369474662622293582390857)
                    ·
                      rfl

theorem cell22_1079324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1079324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079324 prefixEnd_1079324 := by exact prefixLift 1079324
  have htrace : WordTrace (prefixWord ++ tailWord_1079324) baseStart_1079324 baseEnd_1079324 := by
    simpa [prefixWord, tailWord_1079324, baseEnd_1079324] using wordTrace_append hprefix tailTrace_1079324
  have hstable : (prefixWord ++ tailWord_1079324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079324).length < 2 ^ (prefixWord ++ tailWord_1079324).sum := by decide
  have hdescent : baseEnd_1079324 < baseStart_1079324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079333 : List Nat := [1, 3, 1, 2, 2, 13]
def baseStart_1079333 : Nat := 118140960795 + 1079333 * 2 ^ 59
def prefixEnd_1079333 : Nat := 4983230072969 + 3 ^ 40 * 1079333 * 2
def baseEnd_1079333 : Nat := 4561453623533587147109

theorem tailTrace_1079333 : CollatzResearch.WordTrace tailWord_1079333 prefixEnd_1079333 4561453623533587147109 := by
  unfold tailWord_1079333
  simp only [CollatzResearch.WordTrace]
  refine ⟨39366508598768351245818653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26244339065845567497212435 39366508598768351245818653)
  ·
    refine ⟨14762440724538131717181995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39366508598768351245818653 14762440724538131717181995)
    ·
      refine ⟨22143661086807197575772993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14762440724538131717181995 22143661086807197575772993)
      ·
        refine ⟨16607745815105398181829745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22143661086807197575772993 16607745815105398181829745)
        ·
          refine ⟨12455809361329048636372309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16607745815105398181829745 12455809361329048636372309)
          ·
            refine ⟨4561453623533587147109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 12455809361329048636372309 4561453623533587147109)
            ·
              rfl

theorem cell22_1079333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 13].length) (baseStart_1079333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079333 prefixEnd_1079333 := by exact prefixLift 1079333
  have htrace : WordTrace (prefixWord ++ tailWord_1079333) baseStart_1079333 baseEnd_1079333 := by
    simpa [prefixWord, tailWord_1079333, baseEnd_1079333] using wordTrace_append hprefix tailTrace_1079333
  have hstable : (prefixWord ++ tailWord_1079333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079333).length < 2 ^ (prefixWord ++ tailWord_1079333).sum := by decide
  have hdescent : baseEnd_1079333 < baseStart_1079333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079399 : List Nat := [1, 1, 5, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1079399 : Nat := 118140960795 + 1079399 * 2 ^ 59
def prefixEnd_1079399 : Nat := 4983230072969 + 3 ^ 40 * 1079399 * 2
def baseEnd_1079399 : Nat := 369500336655018386765627

theorem tailTrace_1079399 : CollatzResearch.WordTrace tailWord_1079399 prefixEnd_1079399 369500336655018386765627 := by
  unfold tailWord_1079399
  simp only [CollatzResearch.WordTrace]
  refine ⟨39368915816529244517721251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26245943877686163011814167 39368915816529244517721251)
  ·
    refine ⟨59053373724793866776581877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39368915816529244517721251 59053373724793866776581877)
    ·
      refine ⟨5536253786699425010304551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59053373724793866776581877 5536253786699425010304551)
      ·
        refine ⟨8304380680049137515456827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5536253786699425010304551 8304380680049137515456827)
        ·
          refine ⟨12456571020073706273185241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8304380680049137515456827 12456571020073706273185241)
          ·
            refine ⟨9342428265055279704888931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12456571020073706273185241 9342428265055279704888931)
            ·
              refine ⟨14013642397582919557333397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9342428265055279704888931 14013642397582919557333397)
              ·
                refine ⟨656889487386699354250003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14013642397582919557333397 656889487386699354250003)
                ·
                  refine ⟨985334231080049031375005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656889487386699354250003 985334231080049031375005)
                  ·
                    refine ⟨369500336655018386765627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985334231080049031375005 369500336655018386765627)
                    ·
                      rfl

theorem cell22_1079399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1079399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079399 prefixEnd_1079399 := by exact prefixLift 1079399
  have htrace : WordTrace (prefixWord ++ tailWord_1079399) baseStart_1079399 baseEnd_1079399 := by
    simpa [prefixWord, tailWord_1079399, baseEnd_1079399] using wordTrace_append hprefix tailTrace_1079399
  have hstable : (prefixWord ++ tailWord_1079399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079399).length < 2 ^ (prefixWord ++ tailWord_1079399).sum := by decide
  have hdescent : baseEnd_1079399 < baseStart_1079399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079457 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 6]
def baseStart_1079457 : Nat := 118140960795 + 1079457 * 2 ^ 59
def prefixEnd_1079457 : Nat := 4983230072969 + 3 ^ 40 * 1079457 * 2
def baseEnd_1079457 : Nat := 123173397080108522938483

theorem tailTrace_1079457 : CollatzResearch.WordTrace tailWord_1079457 prefixEnd_1079457 123173397080108522938483 := by
  unfold tailWord_1079457
  simp only [CollatzResearch.WordTrace]
  refine ⟨39371031250319120423332625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26247354166879413615555083 39371031250319120423332625)
  ·
    refine ⟨29528273437739340317499469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39371031250319120423332625 29528273437739340317499469)
    ·
      refine ⟨11073102539152252619062301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29528273437739340317499469 11073102539152252619062301)
      ·
        refine ⟨4152413452182094732148363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11073102539152252619062301 4152413452182094732148363)
        ·
          refine ⟨6228620178273142098222545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152413452182094732148363 6228620178273142098222545)
          ·
            refine ⟨4671465133704856573666909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6228620178273142098222545 4671465133704856573666909)
            ·
              refine ⟨1751799425139321215125091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4671465133704856573666909 1751799425139321215125091)
              ·
                refine ⟨2627699137708981822687637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751799425139321215125091 2627699137708981822687637)
                ·
                  refine ⟨123173397080108522938483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2627699137708981822687637 123173397080108522938483)
                  ·
                    rfl

theorem cell22_1079457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_1079457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079457 prefixEnd_1079457 := by exact prefixLift 1079457
  have htrace : WordTrace (prefixWord ++ tailWord_1079457) baseStart_1079457 baseEnd_1079457 := by
    simpa [prefixWord, tailWord_1079457, baseEnd_1079457] using wordTrace_append hprefix tailTrace_1079457
  have hstable : (prefixWord ++ tailWord_1079457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079457).length < 2 ^ (prefixWord ++ tailWord_1079457).sum := by decide
  have hdescent : baseEnd_1079457 < baseStart_1079457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079463 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 5]
def baseStart_1079463 : Nat := 118140960795 + 1079463 * 2 ^ 59
def prefixEnd_1079463 : Nat := 4983230072969 + 3 ^ 40 * 1079463 * 2
def baseEnd_1079463 : Nat := 123174081720981184388477

theorem tailTrace_1079463 : CollatzResearch.WordTrace tailWord_1079463 prefixEnd_1079463 123174081720981184388477 := by
  unfold tailWord_1079463
  simp only [CollatzResearch.WordTrace]
  refine ⟨39371250088297383448051043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26247500058864922298700695 39371250088297383448051043)
  ·
    refine ⟨59056875132446075172076565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39371250088297383448051043 59056875132446075172076565)
    ·
      refine ⟨2768291021833409773691089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59056875132446075172076565 2768291021833409773691089)
      ·
        refine ⟨2076218266375057330268317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2768291021833409773691089 2076218266375057330268317)
        ·
          refine ⟨778581849890646498850619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2076218266375057330268317 778581849890646498850619)
          ·
            refine ⟨1167872774835969748275929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778581849890646498850619 1167872774835969748275929)
            ·
              refine ⟨875904581126977311206947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167872774835969748275929 875904581126977311206947)
              ·
                refine ⟨1313856871690465966810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875904581126977311206947 1313856871690465966810421)
                ·
                  refine ⟨123174081720981184388477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1313856871690465966810421 123174081720981184388477)
                  ·
                    rfl

theorem cell22_1079463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 5].length) (baseStart_1079463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079463 prefixEnd_1079463 := by exact prefixLift 1079463
  have htrace : WordTrace (prefixWord ++ tailWord_1079463) baseStart_1079463 baseEnd_1079463 := by
    simpa [prefixWord, tailWord_1079463, baseEnd_1079463] using wordTrace_append hprefix tailTrace_1079463
  have hstable : (prefixWord ++ tailWord_1079463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079463).length < 2 ^ (prefixWord ++ tailWord_1079463).sum := by decide
  have hdescent : baseEnd_1079463 < baseStart_1079463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079506 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1079506 : Nat := 118140960795 + 1079506 * 2 ^ 59
def prefixEnd_1079506 : Nat := 4983230072969 + 3 ^ 40 * 1079506 * 2
def baseEnd_1079506 : Nat := 369536964941705774340299

theorem tailTrace_1079506 : CollatzResearch.WordTrace tailWord_1079506 prefixEnd_1079506 369536964941705774340299 := by
  unfold tailWord_1079506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843204606785400447966593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26248545618094401194577581 9843204606785400447966593)
  ·
    refine ⟨7382403455089050335974945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9843204606785400447966593 7382403455089050335974945)
    ·
      refine ⟨5536802591316787751981209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7382403455089050335974945 5536802591316787751981209)
      ·
        refine ⟨4152601943487590813985907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5536802591316787751981209 4152601943487590813985907)
        ·
          refine ⟨6228902915231386220978861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152601943487590813985907 6228902915231386220978861)
          ·
            refine ⟨2335838593211769832867073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6228902915231386220978861 2335838593211769832867073)
            ·
              refine ⟨1751878944908827374650305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335838593211769832867073 1751878944908827374650305)
              ·
                refine ⟨1313909208681620530987729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751878944908827374650305 1313909208681620530987729)
                ·
                  refine ⟨985431906511215398240797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313909208681620530987729 985431906511215398240797)
                  ·
                    refine ⟨369536964941705774340299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985431906511215398240797 369536964941705774340299)
                    ·
                      rfl

theorem cell22_1079506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1079506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079506 prefixEnd_1079506 := by exact prefixLift 1079506
  have htrace : WordTrace (prefixWord ++ tailWord_1079506) baseStart_1079506 baseEnd_1079506 := by
    simpa [prefixWord, tailWord_1079506, baseEnd_1079506] using wordTrace_append hprefix tailTrace_1079506
  have hstable : (prefixWord ++ tailWord_1079506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079506).length < 2 ^ (prefixWord ++ tailWord_1079506).sum := by decide
  have hdescent : baseEnd_1079506 < baseStart_1079506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079515 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 2, 6]
def baseStart_1079515 : Nat := 118140960795 + 1079515 * 2 ^ 59
def prefixEnd_1079515 : Nat := 4983230072969 + 3 ^ 40 * 1079515 * 2
def baseEnd_1079515 : Nat := 369540045825632750865271

theorem tailTrace_1079515 : CollatzResearch.WordTrace tailWord_1079515 prefixEnd_1079515 369540045825632750865271 := by
  unfold tailWord_1079515
  simp only [CollatzResearch.WordTrace]
  refine ⟨39373146684108996328943999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26248764456072664219295999 39373146684108996328943999)
  ·
    refine ⟨59059720026163494493415999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39373146684108996328943999 59059720026163494493415999)
    ·
      refine ⟨88589580039245241740123999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59059720026163494493415999 88589580039245241740123999)
      ·
        refine ⟨132884370058867862610185999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88589580039245241740123999 132884370058867862610185999)
        ·
          refine ⟨199326555088301793915278999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132884370058867862610185999 199326555088301793915278999)
          ·
            refine ⟨298989832632452690872918499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199326555088301793915278999 298989832632452690872918499)
            ·
              refine ⟨448484748948679036309377749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298989832632452690872918499 448484748948679036309377749)
              ·
                refine ⟨10511361303484664913501041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 448484748948679036309377749 10511361303484664913501041)
                ·
                  refine ⟨7883520977613498685125781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10511361303484664913501041 7883520977613498685125781)
                  ·
                    refine ⟨369540045825632750865271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7883520977613498685125781 369540045825632750865271)
                    ·
                      rfl

theorem cell22_1079515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_1079515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079515 prefixEnd_1079515 := by exact prefixLift 1079515
  have htrace : WordTrace (prefixWord ++ tailWord_1079515) baseStart_1079515 baseEnd_1079515 := by
    simpa [prefixWord, tailWord_1079515, baseEnd_1079515] using wordTrace_append hprefix tailTrace_1079515
  have hstable : (prefixWord ++ tailWord_1079515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079515).length < 2 ^ (prefixWord ++ tailWord_1079515).sum := by decide
  have hdescent : baseEnd_1079515 < baseStart_1079515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079551 : List Nat := [1, 1, 2, 2, 1, 4, 4, 3, 1, 3]
def baseStart_1079551 : Nat := 118140960795 + 1079551 * 2 ^ 59
def prefixEnd_1079551 : Nat := 4983230072969 + 3 ^ 40 * 1079551 * 2
def baseEnd_1079551 : Nat := 369552369361340656965161

theorem tailTrace_1079551 : CollatzResearch.WordTrace tailWord_1079551 prefixEnd_1079551 369552369361340656965161 := by
  unfold tailWord_1079551
  simp only [CollatzResearch.WordTrace]
  refine ⟨39374459711978574477254507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26249639807985716318169671 39374459711978574477254507)
  ·
    refine ⟨59061689567967861715881761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39374459711978574477254507 59061689567967861715881761)
    ·
      refine ⟨44296267175975896286911321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59061689567967861715881761 44296267175975896286911321)
      ·
        refine ⟨33222200381981922215183491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44296267175975896286911321 33222200381981922215183491)
        ·
          refine ⟨49833300572972883322775237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33222200381981922215183491 49833300572972883322775237)
          ·
            refine ⟨9343743857432415623020357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49833300572972883322775237 9343743857432415623020357)
            ·
              refine ⟨1751951973268577929316317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9343743857432415623020357 1751951973268577929316317)
              ·
                refine ⟨656981989975716723493619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1751951973268577929316317 656981989975716723493619)
                ·
                  refine ⟨985472984963575085240429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656981989975716723493619 985472984963575085240429)
                  ·
                    refine ⟨369552369361340656965161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985472984963575085240429 369552369361340656965161)
                    ·
                      rfl

theorem cell22_1079551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 3].length) (baseStart_1079551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079551 prefixEnd_1079551 := by exact prefixLift 1079551
  have htrace : WordTrace (prefixWord ++ tailWord_1079551) baseStart_1079551 baseEnd_1079551 := by
    simpa [prefixWord, tailWord_1079551, baseEnd_1079551] using wordTrace_append hprefix tailTrace_1079551
  have hstable : (prefixWord ++ tailWord_1079551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079551).length < 2 ^ (prefixWord ++ tailWord_1079551).sum := by decide
  have hdescent : baseEnd_1079551 < baseStart_1079551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079562 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1079562 : Nat := 118140960795 + 1079562 * 2 ^ 59
def prefixEnd_1079562 : Nat := 4983230072969 + 3 ^ 40 * 1079562 * 2
def baseEnd_1079562 : Nat := 369556134886140294940127

theorem tailTrace_1079562 : CollatzResearch.WordTrace tailWord_1079562 prefixEnd_1079562 369556134886140294940127 := by
  unfold tailWord_1079562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843715228734680838976235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26249907276625815570603293 9843715228734680838976235)
  ·
    refine ⟨14765572843102021258464353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9843715228734680838976235 14765572843102021258464353)
    ·
      refine ⟨11074179632326515943848265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14765572843102021258464353 11074179632326515943848265)
      ·
        refine ⟨8305634724244886957886199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11074179632326515943848265 8305634724244886957886199)
        ·
          refine ⟨12458452086367330436829299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8305634724244886957886199 12458452086367330436829299)
          ·
            refine ⟨18687678129550995655243949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12458452086367330436829299 18687678129550995655243949)
            ·
              refine ⟨7007879298581623370716481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18687678129550995655243949 7007879298581623370716481)
              ·
                refine ⟨5255909473936217528037361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7007879298581623370716481 5255909473936217528037361)
                ·
                  refine ⟨3941932105452163146028021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5255909473936217528037361 3941932105452163146028021)
                  ·
                    refine ⟨369556134886140294940127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3941932105452163146028021 369556134886140294940127)
                    ·
                      rfl

theorem cell22_1079562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1079562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079562 prefixEnd_1079562 := by exact prefixLift 1079562
  have htrace : WordTrace (prefixWord ++ tailWord_1079562) baseStart_1079562 baseEnd_1079562 := by
    simpa [prefixWord, tailWord_1079562, baseEnd_1079562] using wordTrace_append hprefix tailTrace_1079562
  have hstable : (prefixWord ++ tailWord_1079562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079562).length < 2 ^ (prefixWord ++ tailWord_1079562).sum := by decide
  have hdescent : baseEnd_1079562 < baseStart_1079562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079607 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 1, 5]
def baseStart_1079607 : Nat := 118140960795 + 1079607 * 2 ^ 59
def prefixEnd_1079607 : Nat := 4983230072969 + 3 ^ 40 * 1079607 * 2
def baseEnd_1079607 : Nat := 369571539305775177564989

theorem tailTrace_1079607 : CollatzResearch.WordTrace tailWord_1079607 prefixEnd_1079607 369571539305775177564989 := by
  unfold tailWord_1079607
  simp only [CollatzResearch.WordTrace]
  refine ⟨39376502199775696041293075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26251001466517130694195383 39376502199775696041293075)
  ·
    refine ⟨59064753299663544061939613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39376502199775696041293075 59064753299663544061939613)
    ·
      refine ⟨22149282487373829023227355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59064753299663544061939613 22149282487373829023227355)
      ·
        refine ⟨33223923731060743534841033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22149282487373829023227355 33223923731060743534841033)
        ·
          refine ⟨24917942798295557651130775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33223923731060743534841033 24917942798295557651130775)
          ·
            refine ⟨37376914197443336476696163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24917942798295557651130775 37376914197443336476696163)
            ·
              refine ⟨56065371296165004715044245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37376914197443336476696163 56065371296165004715044245)
              ·
                refine ⟨2628064279507734596017699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56065371296165004715044245 2628064279507734596017699)
                ·
                  refine ⟨3942096419261601894026549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628064279507734596017699 3942096419261601894026549)
                  ·
                    refine ⟨369571539305775177564989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3942096419261601894026549 369571539305775177564989)
                    ·
                      rfl

theorem cell22_1079607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_1079607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079607 prefixEnd_1079607 := by exact prefixLift 1079607
  have htrace : WordTrace (prefixWord ++ tailWord_1079607) baseStart_1079607 baseEnd_1079607 := by
    simpa [prefixWord, tailWord_1079607, baseEnd_1079607] using wordTrace_append hprefix tailTrace_1079607
  have hstable : (prefixWord ++ tailWord_1079607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079607).length < 2 ^ (prefixWord ++ tailWord_1079607).sum := by decide
  have hdescent : baseEnd_1079607 < baseStart_1079607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079624 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1079624 : Nat := 118140960795 + 1079624 * 2 ^ 59
def prefixEnd_1079624 : Nat := 4983230072969 + 3 ^ 40 * 1079624 * 2
def baseEnd_1079624 : Nat := 369577358753192799889937

theorem tailTrace_1079624 : CollatzResearch.WordTrace tailWord_1079624 prefixEnd_1079624 369577358753192799889937 := by
  unfold tailWord_1079624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19688561120357053972330963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26251414827142738629774617 19688561120357053972330963)
  ·
    refine ⟨29532841680535580958496445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19688561120357053972330963 29532841680535580958496445)
    ·
      refine ⟨11074815630200842859436167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29532841680535580958496445 11074815630200842859436167)
      ·
        refine ⟨16612223445301264289154251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11074815630200842859436167 16612223445301264289154251)
        ·
          refine ⟨24918335167951896433731377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16612223445301264289154251 24918335167951896433731377)
          ·
            refine ⟨18688751375963922325298533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24918335167951896433731377 18688751375963922325298533)
            ·
              refine ⟨3504140882993235435993475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18688751375963922325298533 3504140882993235435993475)
              ·
                refine ⟨5256211324489853153990213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504140882993235435993475 5256211324489853153990213)
                ·
                  refine ⟨985539623341847466373165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5256211324489853153990213 985539623341847466373165)
                  ·
                    refine ⟨369577358753192799889937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985539623341847466373165 369577358753192799889937)
                    ·
                      rfl

theorem cell22_1079624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1079624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079624 prefixEnd_1079624 := by exact prefixLift 1079624
  have htrace : WordTrace (prefixWord ++ tailWord_1079624) baseStart_1079624 baseEnd_1079624 := by
    simpa [prefixWord, tailWord_1079624, baseEnd_1079624] using wordTrace_append hprefix tailTrace_1079624
  have hstable : (prefixWord ++ tailWord_1079624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079624).length < 2 ^ (prefixWord ++ tailWord_1079624).sum := by decide
  have hdescent : baseEnd_1079624 < baseStart_1079624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079656 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1079656 : Nat := 118140960795 + 1079656 * 2 ^ 59
def prefixEnd_1079656 : Nat := 4983230072969 + 3 ^ 40 * 1079656 * 2
def baseEnd_1079656 : Nat := 369588313007155383089839

theorem tailTrace_1079656 : CollatzResearch.WordTrace tailWord_1079656 prefixEnd_1079656 369588313007155383089839 := by
  unfold tailWord_1079656
  simp only [CollatzResearch.WordTrace]
  refine ⟨19689144688299088704913411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26252192917732118273217881 19689144688299088704913411)
  ·
    refine ⟨29533717032448633057370117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19689144688299088704913411 29533717032448633057370117)
    ·
      refine ⟨5537571943584118698256897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29533717032448633057370117 5537571943584118698256897)
      ·
        refine ⟨4153178957688089023692673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5537571943584118698256897 4153178957688089023692673)
        ·
          refine ⟨3114884218266066767769505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4153178957688089023692673 3114884218266066767769505)
          ·
            refine ⟨2336163163699550075827129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3114884218266066767769505 2336163163699550075827129)
            ·
              refine ⟨1752122372774662556870347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336163163699550075827129 1752122372774662556870347)
              ·
                refine ⟨2628183559161993835305521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752122372774662556870347 2628183559161993835305521)
                ·
                  refine ⟨1971137669371495376479141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628183559161993835305521 1971137669371495376479141)
                  ·
                    refine ⟨369588313007155383089839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971137669371495376479141 369588313007155383089839)
                    ·
                      rfl

theorem cell22_1079656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1079656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079656 prefixEnd_1079656 := by exact prefixLift 1079656
  have htrace : WordTrace (prefixWord ++ tailWord_1079656) baseStart_1079656 baseEnd_1079656 := by
    simpa [prefixWord, tailWord_1079656, baseEnd_1079656] using wordTrace_append hprefix tailTrace_1079656
  have hstable : (prefixWord ++ tailWord_1079656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079656).length < 2 ^ (prefixWord ++ tailWord_1079656).sum := by decide
  have hdescent : baseEnd_1079656 < baseStart_1079656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079714 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1079714 : Nat := 118140960795 + 1079714 * 2 ^ 59
def prefixEnd_1079714 : Nat := 4983230072969 + 3 ^ 40 * 1079714 * 2
def baseEnd_1079714 : Nat := 369608167592462565139661

theorem tailTrace_1079714 : CollatzResearch.WordTrace tailWord_1079714 prefixEnd_1079714 369608167592462565139661 := by
  unfold tailWord_1079714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9845101202597013328859549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26253603206925368876958797 9845101202597013328859549)
  ·
    refine ⟨3691912950973879998322331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9845101202597013328859549 3691912950973879998322331)
    ·
      refine ⟨5537869426460819997483497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691912950973879998322331 5537869426460819997483497)
      ·
        refine ⟨4153402069845614998112623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5537869426460819997483497 4153402069845614998112623)
        ·
          refine ⟨6230103104768422497168935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153402069845614998112623 6230103104768422497168935)
          ·
            refine ⟨9345154657152633745753403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230103104768422497168935 9345154657152633745753403)
            ·
              refine ⟨14017731985728950618630105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9345154657152633745753403 14017731985728950618630105)
              ·
                refine ⟨10513298989296712963972579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14017731985728950618630105 10513298989296712963972579)
                ·
                  refine ⟨15769948483945069445958869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10513298989296712963972579 15769948483945069445958869)
                  ·
                    refine ⟨369608167592462565139661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15769948483945069445958869 369608167592462565139661)
                    ·
                      rfl

theorem cell22_1079714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1079714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079714 prefixEnd_1079714 := by exact prefixLift 1079714
  have htrace : WordTrace (prefixWord ++ tailWord_1079714) baseStart_1079714 baseEnd_1079714 := by
    simpa [prefixWord, tailWord_1079714, baseEnd_1079714] using wordTrace_append hprefix tailTrace_1079714
  have hstable : (prefixWord ++ tailWord_1079714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079714).length < 2 ^ (prefixWord ++ tailWord_1079714).sum := by decide
  have hdescent : baseEnd_1079714 < baseStart_1079714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079720 : List Nat := [2, 1, 6, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1079720 : Nat := 118140960795 + 1079720 * 2 ^ 59
def prefixEnd_1079720 : Nat := 4983230072969 + 3 ^ 40 * 1079720 * 2
def baseEnd_1079720 : Nat := 369610221515080549489643

theorem tailTrace_1079720 : CollatzResearch.WordTrace tailWord_1079720 prefixEnd_1079720 369610221515080549489643 := by
  unfold tailWord_1079720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19690311824183158170078307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26253749098910877560104409 19690311824183158170078307)
  ·
    refine ⟨29535467736274737255117461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19690311824183158170078307 29535467736274737255117461)
    ·
      refine ⟨1384475050137878308833631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29535467736274737255117461 1384475050137878308833631)
      ·
        refine ⟨2076712575206817463250447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384475050137878308833631 2076712575206817463250447)
        ·
          refine ⟨3115068862810226194875671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076712575206817463250447 3115068862810226194875671)
          ·
            refine ⟨4672603294215339292313507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3115068862810226194875671 4672603294215339292313507)
            ·
              refine ⟨7008904941323008938470261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672603294215339292313507 7008904941323008938470261)
              ·
                refine ⟨657084838249032087981587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7008904941323008938470261 657084838249032087981587)
                ·
                  refine ⟨985627257373548131972381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657084838249032087981587 985627257373548131972381)
                  ·
                    refine ⟨369610221515080549489643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985627257373548131972381 369610221515080549489643)
                    ·
                      rfl

theorem cell22_1079720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1079720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079720 prefixEnd_1079720 := by exact prefixLift 1079720
  have htrace : WordTrace (prefixWord ++ tailWord_1079720) baseStart_1079720 baseEnd_1079720 := by
    simpa [prefixWord, tailWord_1079720, baseEnd_1079720] using wordTrace_append hprefix tailTrace_1079720
  have hstable : (prefixWord ++ tailWord_1079720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079720).length < 2 ^ (prefixWord ++ tailWord_1079720).sum := by decide
  have hdescent : baseEnd_1079720 < baseStart_1079720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079733 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 5]
def baseStart_1079733 : Nat := 118140960795 + 1079733 * 2 ^ 59
def prefixEnd_1079733 : Nat := 4983230072969 + 3 ^ 40 * 1079733 * 2
def baseEnd_1079733 : Nat := 123204890560250949638201

theorem tailTrace_1079733 : CollatzResearch.WordTrace tailWord_1079733 prefixEnd_1079733 123204890560250949638201 := by
  unfold tailWord_1079733
  simp only [CollatzResearch.WordTrace]
  refine ⟨39381097797319219560379853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26254065198212813040253235 39381097797319219560379853)
  ·
    refine ⟨14767911673994707335142445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39381097797319219560379853 14767911673994707335142445)
    ·
      refine ⟨5537966877748015250678417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14767911673994707335142445 5537966877748015250678417)
      ·
        refine ⟨4153475158311011438008813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5537966877748015250678417 4153475158311011438008813)
        ·
          refine ⟨1557553184366629289253305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4153475158311011438008813 1557553184366629289253305)
          ·
            refine ⟨1168164888274971966939979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1557553184366629289253305 1168164888274971966939979)
            ·
              refine ⟨1752247332412457950409969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168164888274971966939979 1752247332412457950409969)
              ·
                refine ⟨1314185499309343462807477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752247332412457950409969 1314185499309343462807477)
                ·
                  refine ⟨123204890560250949638201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1314185499309343462807477 123204890560250949638201)
                  ·
                    rfl

theorem cell22_1079733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_1079733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079733 prefixEnd_1079733 := by exact prefixLift 1079733
  have htrace : WordTrace (prefixWord ++ tailWord_1079733) baseStart_1079733 baseEnd_1079733 := by
    simpa [prefixWord, tailWord_1079733, baseEnd_1079733] using wordTrace_append hprefix tailTrace_1079733
  have hstable : (prefixWord ++ tailWord_1079733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079733).length < 2 ^ (prefixWord ++ tailWord_1079733).sum := by decide
  have hdescent : baseEnd_1079733 < baseStart_1079733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079814 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1079814 : Nat := 118140960795 + 1079814 * 2 ^ 59
def prefixEnd_1079814 : Nat := 4983230072969 + 3 ^ 40 * 1079814 * 2
def baseEnd_1079814 : Nat := 369642399636095637639355

theorem tailTrace_1079814 : CollatzResearch.WordTrace tailWord_1079814 prefixEnd_1079814 369642399636095637639355 := by
  unfold tailWord_1079814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230751628438305324814953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26256034740017180262718997 1230751628438305324814953)
  ·
    refine ⟨923063721328728993611215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1230751628438305324814953 923063721328728993611215)
    ·
      refine ⟨1384595581993093490416823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923063721328728993611215 1384595581993093490416823)
      ·
        refine ⟨2076893372989640235625235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384595581993093490416823 2076893372989640235625235)
        ·
          refine ⟨3115340059484460353437853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076893372989640235625235 3115340059484460353437853)
          ·
            refine ⟨1168252522306672632539195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3115340059484460353437853 1168252522306672632539195)
            ·
              refine ⟨1752378783460008948808793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168252522306672632539195 1752378783460008948808793)
              ·
                refine ⟨1314284087595006711606595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752378783460008948808793 1314284087595006711606595)
                ·
                  refine ⟨1971426131392510067409893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314284087595006711606595 1971426131392510067409893)
                  ·
                    refine ⟨369642399636095637639355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971426131392510067409893 369642399636095637639355)
                    ·
                      rfl

theorem cell22_1079814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1079814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079814 prefixEnd_1079814 := by exact prefixLift 1079814
  have htrace : WordTrace (prefixWord ++ tailWord_1079814) baseStart_1079814 baseEnd_1079814 := by
    simpa [prefixWord, tailWord_1079814, baseEnd_1079814] using wordTrace_append hprefix tailTrace_1079814
  have hstable : (prefixWord ++ tailWord_1079814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079814).length < 2 ^ (prefixWord ++ tailWord_1079814).sum := by decide
  have hdescent : baseEnd_1079814 < baseStart_1079814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079834 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_1079834 : Nat := 118140960795 + 1079834 * 2 ^ 59
def prefixEnd_1079834 : Nat := 4983230072969 + 3 ^ 40 * 1079834 * 2
def baseEnd_1079834 : Nat := 123216415348274084046431

theorem tailTrace_1079834 : CollatzResearch.WordTrace tailWord_1079834 prefixEnd_1079834 123216415348274084046431 := by
  unfold tailWord_1079834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846195392488328452451639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26256521046635542539871037 9846195392488328452451639)
  ·
    refine ⟨14769293088732492678677459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9846195392488328452451639 14769293088732492678677459)
    ·
      refine ⟨22153939633098739018016189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14769293088732492678677459 22153939633098739018016189)
      ·
        refine ⟨8307727362412027131756071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22153939633098739018016189 8307727362412027131756071)
        ·
          refine ⟨12461591043618040697634107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8307727362412027131756071 12461591043618040697634107)
          ·
            refine ⟨18692386565427061046451161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12461591043618040697634107 18692386565427061046451161)
            ·
              refine ⟨14019289924070295784838371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18692386565427061046451161 14019289924070295784838371)
              ·
                refine ⟨21028934886105443677257557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14019289924070295784838371 21028934886105443677257557)
                ·
                  refine ⟨123216415348274084046431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21028934886105443677257557 123216415348274084046431)
                  ·
                    rfl

theorem cell22_1079834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_1079834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079834 prefixEnd_1079834 := by exact prefixLift 1079834
  have htrace : WordTrace (prefixWord ++ tailWord_1079834) baseStart_1079834 baseEnd_1079834 := by
    simpa [prefixWord, tailWord_1079834, baseEnd_1079834] using wordTrace_append hprefix tailTrace_1079834
  have hstable : (prefixWord ++ tailWord_1079834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079834).length < 2 ^ (prefixWord ++ tailWord_1079834).sum := by decide
  have hdescent : baseEnd_1079834 < baseStart_1079834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079866 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_1079866 : Nat := 118140960795 + 1079866 * 2 ^ 59
def prefixEnd_1079866 : Nat := 4983230072969 + 3 ^ 40 * 1079866 * 2
def baseEnd_1079866 : Nat := 369660200298784835339195

theorem tailTrace_1079866 : CollatzResearch.WordTrace tailWord_1079866 prefixEnd_1079866 369660200298784835339195 := by
  unfold tailWord_1079866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846487176459345818742863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26257299137224922183314301 9846487176459345818742863)
  ·
    refine ⟨14769730764689018728114295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9846487176459345818742863 14769730764689018728114295)
    ·
      refine ⟨22154596147033528092171443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14769730764689018728114295 22154596147033528092171443)
      ·
        refine ⟨33231894220550292138257165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22154596147033528092171443 33231894220550292138257165)
        ·
          refine ⟨12461960332706359551846437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33231894220550292138257165 12461960332706359551846437)
          ·
            refine ⟨2336617562382442415971207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12461960332706359551846437 2336617562382442415971207)
            ·
              refine ⟨3504926343573663623956811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336617562382442415971207 3504926343573663623956811)
              ·
                refine ⟨5257389515360495435935217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504926343573663623956811 5257389515360495435935217)
                ·
                  refine ⟨3943042136520371576951413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257389515360495435935217 3943042136520371576951413)
                  ·
                    refine ⟨369660200298784835339195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3943042136520371576951413 369660200298784835339195)
                    ·
                      rfl

theorem cell22_1079866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_1079866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079866 prefixEnd_1079866 := by exact prefixLift 1079866
  have htrace : WordTrace (prefixWord ++ tailWord_1079866) baseStart_1079866 baseEnd_1079866 := by
    simpa [prefixWord, tailWord_1079866, baseEnd_1079866] using wordTrace_append hprefix tailTrace_1079866
  have hstable : (prefixWord ++ tailWord_1079866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079866).length < 2 ^ (prefixWord ++ tailWord_1079866).sum := by decide
  have hdescent : baseEnd_1079866 < baseStart_1079866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079902 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1079902 : Nat := 118140960795 + 1079902 * 2 ^ 59
def prefixEnd_1079902 : Nat := 4983230072969 + 3 ^ 40 * 1079902 * 2
def baseEnd_1079902 : Nat := 123224174611497580479695

theorem tailTrace_1079902 : CollatzResearch.WordTrace tailWord_1079902 prefixEnd_1079902 123224174611497580479695 := by
  unfold tailWord_1079902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4923407716713370177910245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26258174489137974282187973 4923407716713370177910245)
  ·
    refine ⟨923138946883756908358171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4923407716713370177910245 923138946883756908358171)
    ·
      refine ⟨1384708420325635362537257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923138946883756908358171 1384708420325635362537257)
      ·
        refine ⟨1038531315244226521902943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1384708420325635362537257 1038531315244226521902943)
        ·
          refine ⟨1557796972866339782854415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038531315244226521902943 1557796972866339782854415)
          ·
            refine ⟨2336695459299509674281623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557796972866339782854415 2336695459299509674281623)
            ·
              refine ⟨3505043188949264511422435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336695459299509674281623 3505043188949264511422435)
              ·
                refine ⟨5257564783423896767133653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3505043188949264511422435 5257564783423896767133653)
                ·
                  refine ⟨123224174611497580479695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5257564783423896767133653 123224174611497580479695)
                  ·
                    rfl

theorem cell22_1079902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1079902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079902 prefixEnd_1079902 := by exact prefixLift 1079902
  have htrace : WordTrace (prefixWord ++ tailWord_1079902) baseStart_1079902 baseEnd_1079902 := by
    simpa [prefixWord, tailWord_1079902, baseEnd_1079902] using wordTrace_append hprefix tailTrace_1079902
  have hstable : (prefixWord ++ tailWord_1079902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079902).length < 2 ^ (prefixWord ++ tailWord_1079902).sum := by decide
  have hdescent : baseEnd_1079902 < baseStart_1079902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079941 : List Nat := [1, 3, 1, 1, 4, 3, 1, 8]
def baseStart_1079941 : Nat := 118140960795 + 1079941 * 2 ^ 59
def prefixEnd_1079941 : Nat := 4983230072969 + 3 ^ 40 * 1079941 * 2
def baseEnd_1079941 : Nat := 41076208259056626634885

theorem tailTrace_1079941 : CollatzResearch.WordTrace tailWord_1079941 prefixEnd_1079941 41076208259056626634885 := by
  unfold tailWord_1079941
  simp only [CollatzResearch.WordTrace]
  refine ⟨39388684180565671083951677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26259122787043780722634451 39388684180565671083951677)
  ·
    refine ⟨14770756567712126656481879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39388684180565671083951677 14770756567712126656481879)
    ·
      refine ⟨22156134851568189984722819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14770756567712126656481879 22156134851568189984722819)
      ·
        refine ⟨33234202277352284977084229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22156134851568189984722819 33234202277352284977084229)
        ·
          refine ⟨6231412927003553433203293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33234202277352284977084229 6231412927003553433203293)
          ·
            refine ⟨2336779847626332537451235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6231412927003553433203293 2336779847626332537451235)
            ·
              refine ⟨3505169771439498806176853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336779847626332537451235 3505169771439498806176853)
              ·
                refine ⟨41076208259056626634885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3505169771439498806176853 41076208259056626634885)
                ·
                  rfl

theorem cell22_1079941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 8].length) (baseStart_1079941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079941 prefixEnd_1079941 := by exact prefixLift 1079941
  have htrace : WordTrace (prefixWord ++ tailWord_1079941) baseStart_1079941 baseEnd_1079941 := by
    simpa [prefixWord, tailWord_1079941, baseEnd_1079941] using wordTrace_append hprefix tailTrace_1079941
  have hstable : (prefixWord ++ tailWord_1079941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079941).length < 2 ^ (prefixWord ++ tailWord_1079941).sum := by decide
  have hdescent : baseEnd_1079941 < baseStart_1079941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079975 : List Nat := [1, 1, 6, 3, 1, 1, 2, 7]
def baseStart_1079975 : Nat := 118140960795 + 1079975 * 2 ^ 59
def prefixEnd_1079975 : Nat := 4983230072969 + 3 ^ 40 * 1079975 * 2
def baseEnd_1079975 : Nat := 41077501469593876040429

theorem tailTrace_1079975 : CollatzResearch.WordTrace tailWord_1079975 prefixEnd_1079975 41077501469593876040429 := by
  unfold tailWord_1079975
  simp only [CollatzResearch.WordTrace]
  refine ⟨39389924262442494890689379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26259949508294996593792919 39389924262442494890689379)
  ·
    refine ⟨59084886393663742336034069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39389924262442494890689379 59084886393663742336034069)
    ·
      refine ⟨2769604049702987922001597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59084886393663742336034069 2769604049702987922001597)
      ·
        refine ⟨1038601518638620470750599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2769604049702987922001597 1038601518638620470750599)
        ·
          refine ⟨1557902277957930706125899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038601518638620470750599 1557902277957930706125899)
          ·
            refine ⟨2336853416936896059188849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557902277957930706125899 2336853416936896059188849)
            ·
              refine ⟨1752640062702672044391637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336853416936896059188849 1752640062702672044391637)
              ·
                refine ⟨41077501469593876040429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1752640062702672044391637 41077501469593876040429)
                ·
                  rfl

theorem cell22_1079975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 7].length) (baseStart_1079975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1079975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1079975 prefixEnd_1079975 := by exact prefixLift 1079975
  have htrace : WordTrace (prefixWord ++ tailWord_1079975) baseStart_1079975 baseEnd_1079975 := by
    simpa [prefixWord, tailWord_1079975, baseEnd_1079975] using wordTrace_append hprefix tailTrace_1079975
  have hstable : (prefixWord ++ tailWord_1079975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079975).length < 2 ^ (prefixWord ++ tailWord_1079975).sum := by decide
  have hdescent : baseEnd_1079975 < baseStart_1079975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080024 : List Nat := [2, 1, 2, 2, 3, 4, 2, 2, 1, 3]
def baseStart_1080024 : Nat := 118140960795 + 1080024 * 2 ^ 59
def prefixEnd_1080024 : Nat := 4983230072969 + 3 ^ 40 * 1080024 * 2
def baseEnd_1080024 : Nat := 369714286927725089888711

theorem tailTrace_1080024 : CollatzResearch.WordTrace tailWord_1080024 prefixEnd_1080024 369714286927725089888711 := by
  unfold tailWord_1080024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19695855719632488129611563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26261140959509984172815417 19695855719632488129611563)
  ·
    refine ⟨29543783579448732194417345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19695855719632488129611563 29543783579448732194417345)
    ·
      refine ⟨22157837684586549145813009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29543783579448732194417345 22157837684586549145813009)
      ·
        refine ⟨16618378263439911859359757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22157837684586549145813009 16618378263439911859359757)
        ·
          refine ⟨6231891848789966947259909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16618378263439911859359757 6231891848789966947259909)
          ·
            refine ⟨1168479721648118802611233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6231891848789966947259909 1168479721648118802611233)
            ·
              refine ⟨876359791236089101958425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168479721648118802611233 876359791236089101958425)
              ·
                refine ⟨657269843427066826468819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876359791236089101958425 657269843427066826468819)
                ·
                  refine ⟨985904765140600239703229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657269843427066826468819 985904765140600239703229)
                  ·
                    refine ⟨369714286927725089888711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985904765140600239703229 369714286927725089888711)
                    ·
                      rfl

theorem cell22_1080024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_1080024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080024 prefixEnd_1080024 := by exact prefixLift 1080024
  have htrace : WordTrace (prefixWord ++ tailWord_1080024) baseStart_1080024 baseEnd_1080024 := by
    simpa [prefixWord, tailWord_1080024, baseEnd_1080024] using wordTrace_append hprefix tailTrace_1080024
  have hstable : (prefixWord ++ tailWord_1080024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080024).length < 2 ^ (prefixWord ++ tailWord_1080024).sum := by decide
  have hdescent : baseEnd_1080024 < baseStart_1080024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080033 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1080033 : Nat := 118140960795 + 1080033 * 2 ^ 59
def prefixEnd_1080033 : Nat := 4983230072969 + 3 ^ 40 * 1080033 * 2
def baseEnd_1080033 : Nat := 369717367811652066413683

theorem tailTrace_1080033 : CollatzResearch.WordTrace tailWord_1080033 prefixEnd_1080033 369717367811652066413683 := by
  unfold tailWord_1080033
  simp only [CollatzResearch.WordTrace]
  refine ⟨39392039696232370796300753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26261359797488247197533835 39392039696232370796300753)
  ·
    refine ⟨29544029772174278097225565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39392039696232370796300753 29544029772174278097225565)
    ·
      refine ⟨11079011164565354286459587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29544029772174278097225565 11079011164565354286459587)
      ·
        refine ⟨16618516746848031429689381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11079011164565354286459587 16618516746848031429689381)
        ·
          refine ⟨3115971890034005893066759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16618516746848031429689381 3115971890034005893066759)
          ·
            refine ⟨4673957835051008839600139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3115971890034005893066759 4673957835051008839600139)
            ·
              refine ⟨7010936752576513259400209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4673957835051008839600139 7010936752576513259400209)
              ·
                refine ⟨5258202564432384944550157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7010936752576513259400209 5258202564432384944550157)
                ·
                  refine ⟨1971825961662144354206309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5258202564432384944550157 1971825961662144354206309)
                  ·
                    refine ⟨369717367811652066413683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971825961662144354206309 369717367811652066413683)
                    ·
                      rfl

theorem cell22_1080033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1080033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080033 prefixEnd_1080033 := by exact prefixLift 1080033
  have htrace : WordTrace (prefixWord ++ tailWord_1080033) baseStart_1080033 baseEnd_1080033 := by
    simpa [prefixWord, tailWord_1080033, baseEnd_1080033] using wordTrace_append hprefix tailTrace_1080033
  have hstable : (prefixWord ++ tailWord_1080033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080033).length < 2 ^ (prefixWord ++ tailWord_1080033).sum := by decide
  have hdescent : baseEnd_1080033 < baseStart_1080033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080063 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 4, 3]
def baseStart_1080063 : Nat := 118140960795 + 1080063 * 2 ^ 59
def prefixEnd_1080063 : Nat := 4983230072969 + 3 ^ 40 * 1080063 * 2
def baseEnd_1080063 : Nat := 369727637424741988163591

theorem tailTrace_1080063 : CollatzResearch.WordTrace tailWord_1080063 prefixEnd_1080063 369727637424741988163591 := by
  unfold tailWord_1080063
  simp only [CollatzResearch.WordTrace]
  refine ⟨39393133886123685919892843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26262089257415790613261895 39393133886123685919892843)
  ·
    refine ⟨59089700829185528879839265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39393133886123685919892843 59089700829185528879839265)
    ·
      refine ⟨44317275621889146659879449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59089700829185528879839265 44317275621889146659879449)
      ·
        refine ⟨33237956716416859994909587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44317275621889146659879449 33237956716416859994909587)
        ·
          refine ⟨49856935074625289992364381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33237956716416859994909587 49856935074625289992364381)
          ·
            refine ⟨18696350652984483747136643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49856935074625289992364381 18696350652984483747136643)
            ·
              refine ⟨28044525979476725620704965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18696350652984483747136643 28044525979476725620704965)
              ·
                refine ⟨5258348621151886053882181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28044525979476725620704965 5258348621151886053882181)
                ·
                  refine ⟨985940366465978635102909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5258348621151886053882181 985940366465978635102909)
                  ·
                    refine ⟨369727637424741988163591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985940366465978635102909 369727637424741988163591)
                    ·
                      rfl

theorem cell22_1080063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_1080063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080063 prefixEnd_1080063 := by exact prefixLift 1080063
  have htrace : WordTrace (prefixWord ++ tailWord_1080063) baseStart_1080063 baseEnd_1080063 := by
    simpa [prefixWord, tailWord_1080063, baseEnd_1080063] using wordTrace_append hprefix tailTrace_1080063
  have hstable : (prefixWord ++ tailWord_1080063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080063).length < 2 ^ (prefixWord ++ tailWord_1080063).sum := by decide
  have hdescent : baseEnd_1080063 < baseStart_1080063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080078 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_1080078 : Nat := 118140960795 + 1080078 * 2 ^ 59
def prefixEnd_1080078 : Nat := 4983230072969 + 3 ^ 40 * 1080078 * 2
def baseEnd_1080078 : Nat := 369732772231286949038545

theorem tailTrace_1080078 : CollatzResearch.WordTrace tailWord_1080078 prefixEnd_1080078 369732772231286949038545 := by
  unfold tailWord_1080078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924210122633667935211111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26262453987379562321125925 4924210122633667935211111)
  ·
    refine ⟨7386315183950501902816667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4924210122633667935211111 7386315183950501902816667)
    ·
      refine ⟨11079472775925752854225001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7386315183950501902816667 11079472775925752854225001)
      ·
        refine ⟨8309604581944314640668751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11079472775925752854225001 8309604581944314640668751)
        ·
          refine ⟨12464406872916471961003127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309604581944314640668751 12464406872916471961003127)
          ·
            refine ⟨18696610309374707941504691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12464406872916471961003127 18696610309374707941504691)
            ·
              refine ⟨28044915464062061912257037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18696610309374707941504691 28044915464062061912257037)
              ·
                refine ⟨10516843299023273217096389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28044915464062061912257037 10516843299023273217096389)
                ·
                  refine ⟨1971908118566863728205573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10516843299023273217096389 1971908118566863728205573)
                  ·
                    refine ⟨369732772231286949038545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971908118566863728205573 369732772231286949038545)
                    ·
                      rfl

theorem cell22_1080078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_1080078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080078 prefixEnd_1080078 := by exact prefixLift 1080078
  have htrace : WordTrace (prefixWord ++ tailWord_1080078) baseStart_1080078 baseEnd_1080078 := by
    simpa [prefixWord, tailWord_1080078, baseEnd_1080078] using wordTrace_append hprefix tailTrace_1080078
  have hstable : (prefixWord ++ tailWord_1080078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080078).length < 2 ^ (prefixWord ++ tailWord_1080078).sum := by decide
  have hdescent : baseEnd_1080078 < baseStart_1080078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080082 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1080082 : Nat := 118140960795 + 1080082 * 2 ^ 59
def prefixEnd_1080082 : Nat := 4983230072969 + 3 ^ 40 * 1080082 * 2
def baseEnd_1080082 : Nat := 123244713837677423979511

theorem tailTrace_1080082 : CollatzResearch.WordTrace tailWord_1080082 prefixEnd_1080082 123244713837677423979511 := by
  unfold tailWord_1080082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9848456718263713041208625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26262551248703234776556333 9848456718263713041208625)
  ·
    refine ⟨7386342538697784780906469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9848456718263713041208625 7386342538697784780906469)
    ·
      refine ⟨1384939226005834646419963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7386342538697784780906469 1384939226005834646419963)
      ·
        refine ⟨2077408839008751969629945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384939226005834646419963 2077408839008751969629945)
        ·
          refine ⟨1558056629256563977222459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2077408839008751969629945 1558056629256563977222459)
          ·
            refine ⟨2337084943884845965833689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558056629256563977222459 2337084943884845965833689)
            ·
              refine ⟨1752813707913634474375267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337084943884845965833689 1752813707913634474375267)
              ·
                refine ⟨2629220561870451711562901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752813707913634474375267 2629220561870451711562901)
                ·
                  refine ⟨123244713837677423979511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2629220561870451711562901 123244713837677423979511)
                  ·
                    rfl

theorem cell22_1080082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1080082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080082 prefixEnd_1080082 := by exact prefixLift 1080082
  have htrace : WordTrace (prefixWord ++ tailWord_1080082) baseStart_1080082 baseEnd_1080082 := by
    simpa [prefixWord, tailWord_1080082, baseEnd_1080082] using wordTrace_append hprefix tailTrace_1080082
  have hstable : (prefixWord ++ tailWord_1080082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080082).length < 2 ^ (prefixWord ++ tailWord_1080082).sum := by decide
  have hdescent : baseEnd_1080082 < baseStart_1080082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080091 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 4, 7]
def baseStart_1080091 : Nat := 118140960795 + 1080091 * 2 ^ 59
def prefixEnd_1080091 : Nat := 4983230072969 + 3 ^ 40 * 1080091 * 2
def baseEnd_1080091 : Nat := 369737222396959248463505

theorem tailTrace_1080091 : CollatzResearch.WordTrace tailWord_1080091 prefixEnd_1080091 369737222396959248463505 := by
  unfold tailWord_1080091
  simp only [CollatzResearch.WordTrace]
  refine ⟨39394155130022246701912127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26262770086681497801274751 39394155130022246701912127)
  ·
    refine ⟨59091232695033370052868191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39394155130022246701912127 59091232695033370052868191)
    ·
      refine ⟨88636849042550055079302287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59091232695033370052868191 88636849042550055079302287)
      ·
        refine ⟨132955273563825082618953431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88636849042550055079302287 132955273563825082618953431)
        ·
          refine ⟨199432910345737623928430147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132955273563825082618953431 199432910345737623928430147)
          ·
            refine ⟨299149365518606435892645221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199432910345737623928430147 299149365518606435892645221)
            ·
              refine ⟨56090506034738706729870979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299149365518606435892645221 56090506034738706729870979)
              ·
                refine ⟨84135759052108060094806469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56090506034738706729870979 84135759052108060094806469)
                ·
                  refine ⟨15775454822270261267776213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84135759052108060094806469 15775454822270261267776213)
                  ·
                    refine ⟨369737222396959248463505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15775454822270261267776213 369737222396959248463505)
                    ·
                      rfl

theorem cell22_1080091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_1080091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080091 prefixEnd_1080091 := by exact prefixLift 1080091
  have htrace : WordTrace (prefixWord ++ tailWord_1080091) baseStart_1080091 baseEnd_1080091 := by
    simpa [prefixWord, tailWord_1080091, baseEnd_1080091] using wordTrace_append hprefix tailTrace_1080091
  have hstable : (prefixWord ++ tailWord_1080091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080091).length < 2 ^ (prefixWord ++ tailWord_1080091).sum := by decide
  have hdescent : baseEnd_1080091 < baseStart_1080091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080097 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 2, 3]
def baseStart_1080097 : Nat := 118140960795 + 1080097 * 2 ^ 59
def prefixEnd_1080097 : Nat := 4983230072969 + 3 ^ 40 * 1080097 * 2
def baseEnd_1080097 : Nat := 369739276319577232813487

theorem tailTrace_1080097 : CollatzResearch.WordTrace tailWord_1080097 prefixEnd_1080097 369739276319577232813487 := by
  unfold tailWord_1080097
  simp only [CollatzResearch.WordTrace]
  refine ⟨39394373968000509726630545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26262915978667006484420363 39394373968000509726630545)
  ·
    refine ⟨29545780476000382294972909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39394373968000509726630545 29545780476000382294972909)
    ·
      refine ⟨11079667678500143360614841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29545780476000382294972909 11079667678500143360614841)
      ·
        refine ⟨8309750758875107520461131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11079667678500143360614841 8309750758875107520461131)
        ·
          refine ⟨12464626138312661280691697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309750758875107520461131 12464626138312661280691697)
          ·
            refine ⟨9348469603734495960518773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12464626138312661280691697 9348469603734495960518773)
            ·
              refine ⟨876419025350108996298635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9348469603734495960518773 876419025350108996298635)
              ·
                refine ⟨1314628538025163494447953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876419025350108996298635 1314628538025163494447953)
                ·
                  refine ⟨985971403518872620835965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1314628538025163494447953 985971403518872620835965)
                  ·
                    refine ⟨369739276319577232813487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985971403518872620835965 369739276319577232813487)
                    ·
                      rfl

theorem cell22_1080097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_1080097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080097 prefixEnd_1080097 := by exact prefixLift 1080097
  have htrace : WordTrace (prefixWord ++ tailWord_1080097) baseStart_1080097 baseEnd_1080097 := by
    simpa [prefixWord, tailWord_1080097, baseEnd_1080097] using wordTrace_append hprefix tailTrace_1080097
  have hstable : (prefixWord ++ tailWord_1080097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080097).length < 2 ^ (prefixWord ++ tailWord_1080097).sum := by decide
  have hdescent : baseEnd_1080097 < baseStart_1080097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080110 : List Nat := [4, 1, 3, 2, 1, 2, 1, 8]
def baseStart_1080110 : Nat := 118140960795 + 1080110 * 2 ^ 59
def prefixEnd_1080110 : Nat := 4983230072969 + 3 ^ 40 * 1080110 * 2
def baseEnd_1080110 : Nat := 41082636276138836915383

theorem tailTrace_1080110 : CollatzResearch.WordTrace tailWord_1080110 prefixEnd_1080110 41082636276138836915383 := by
  unfold tailWord_1080110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924356014619176618356723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26263232077968941964569189 4924356014619176618356723)
  ·
    refine ⟨7386534021928764927535085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4924356014619176618356723 7386534021928764927535085)
    ·
      refine ⟨2769950258223286847825657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7386534021928764927535085 2769950258223286847825657)
      ·
        refine ⟨2077462693667465135869243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2769950258223286847825657 2077462693667465135869243)
        ·
          refine ⟨3116194040501197703803865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077462693667465135869243 3116194040501197703803865)
          ·
            refine ⟨2337145530375898277852899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3116194040501197703803865 2337145530375898277852899)
            ·
              refine ⟨3505718295563847416779349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337145530375898277852899 3505718295563847416779349)
              ·
                refine ⟨41082636276138836915383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3505718295563847416779349 41082636276138836915383)
                ·
                  rfl

theorem cell22_1080110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_1080110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080110 prefixEnd_1080110 := by exact prefixLift 1080110
  have htrace : WordTrace (prefixWord ++ tailWord_1080110) baseStart_1080110 baseEnd_1080110 := by
    simpa [prefixWord, tailWord_1080110, baseEnd_1080110] using wordTrace_append hprefix tailTrace_1080110
  have hstable : (prefixWord ++ tailWord_1080110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080110).length < 2 ^ (prefixWord ++ tailWord_1080110).sum := by decide
  have hdescent : baseEnd_1080110 < baseStart_1080110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080116 : List Nat := [2, 5, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1080116 : Nat := 118140960795 + 1080116 * 2 ^ 59
def prefixEnd_1080116 : Nat := 4983230072969 + 3 ^ 40 * 1080116 * 2
def baseEnd_1080116 : Nat := 123248593469289172196143

theorem tailTrace_1080116 : CollatzResearch.WordTrace tailWord_1080116 prefixEnd_1080116 123248593469289172196143 := by
  unfold tailWord_1080116
  simp only [CollatzResearch.WordTrace]
  refine ⟨19697533477465837985786101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26263377969954450647714801 19697533477465837985786101)
  ·
    refine ⟨1846643763512422311167447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19697533477465837985786101 1846643763512422311167447)
    ·
      refine ⟨2769965645268633466751171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846643763512422311167447 2769965645268633466751171)
      ·
        refine ⟨4154948467902950200126757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2769965645268633466751171 4154948467902950200126757)
        ·
          refine ⟨779052837731803162523767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4154948467902950200126757 779052837731803162523767)
          ·
            refine ⟨1168579256597704743785651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779052837731803162523767 1168579256597704743785651)
            ·
              refine ⟨1752868884896557115678477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168579256597704743785651 1752868884896557115678477)
              ·
                refine ⟨657325831836208918379429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1752868884896557115678477 657325831836208918379429)
                ·
                  refine ⟨123248593469289172196143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 657325831836208918379429 123248593469289172196143)
                  ·
                    rfl

theorem cell22_1080116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1080116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080116 prefixEnd_1080116 := by exact prefixLift 1080116
  have htrace : WordTrace (prefixWord ++ tailWord_1080116) baseStart_1080116 baseEnd_1080116 := by
    simpa [prefixWord, tailWord_1080116, baseEnd_1080116] using wordTrace_append hprefix tailTrace_1080116
  have hstable : (prefixWord ++ tailWord_1080116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080116).length < 2 ^ (prefixWord ++ tailWord_1080116).sum := by decide
  have hdescent : baseEnd_1080116 < baseStart_1080116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080142 : List Nat := [4, 1, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_1080142 : Nat := 118140960795 + 1080142 * 2 ^ 59
def prefixEnd_1080142 : Nat := 4983230072969 + 3 ^ 40 * 1080142 * 2
def baseEnd_1080142 : Nat := 369754680739212115438349

theorem tailTrace_1080142 : CollatzResearch.WordTrace tailWord_1080142 prefixEnd_1080142 369754680739212115438349 := by
  unfold tailWord_1080142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924501906604685301502335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26264010168558321608012453 4924501906604685301502335)
  ·
    refine ⟨7386752859907027952253503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4924501906604685301502335 7386752859907027952253503)
    ·
      refine ⟨11080129289860541928380255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7386752859907027952253503 11080129289860541928380255)
      ·
        refine ⟨16620193934790812892570383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11080129289860541928380255 16620193934790812892570383)
        ·
          refine ⟨24930290902186219338855575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16620193934790812892570383 24930290902186219338855575)
          ·
            refine ⟨37395436353279329008283363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24930290902186219338855575 37395436353279329008283363)
            ·
              refine ⟨56093154529918993512425045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37395436353279329008283363 56093154529918993512425045)
              ·
                refine ⟨657341654647488205223731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 56093154529918993512425045 657341654647488205223731)
                ·
                  refine ⟨986012481971232307835597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657341654647488205223731 986012481971232307835597)
                  ·
                    refine ⟨369754680739212115438349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986012481971232307835597 369754680739212115438349)
                    ·
                      rfl

theorem cell22_1080142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_1080142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080142 prefixEnd_1080142 := by exact prefixLift 1080142
  have htrace : WordTrace (prefixWord ++ tailWord_1080142) baseStart_1080142 baseEnd_1080142 := by
    simpa [prefixWord, tailWord_1080142, baseEnd_1080142] using wordTrace_append hprefix tailTrace_1080142
  have hstable : (prefixWord ++ tailWord_1080142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080142).length < 2 ^ (prefixWord ++ tailWord_1080142).sum := by decide
  have hdescent : baseEnd_1080142 < baseStart_1080142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080215 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 1, 5]
def baseStart_1080215 : Nat := 118140960795 + 1080215 * 2 ^ 59
def prefixEnd_1080215 : Nat := 4983230072969 + 3 ^ 40 * 1080215 * 2
def baseEnd_1080215 : Nat := 369779670131064258363125

theorem tailTrace_1080215 : CollatzResearch.WordTrace tailWord_1080215 prefixEnd_1080215 369779670131064258363125 := by
  unfold tailWord_1080215
  simp only [CollatzResearch.WordTrace]
  refine ⟨39398677781573015879426099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26265785187715343919617399 39398677781573015879426099)
  ·
    refine ⟨59098016672359523819139149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39398677781573015879426099 59098016672359523819139149)
    ·
      refine ⟨22161756252134821432177181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59098016672359523819139149 22161756252134821432177181)
      ·
        refine ⟨8310658594550558037066443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22161756252134821432177181 8310658594550558037066443)
        ·
          refine ⟨12465987891825837055599665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8310658594550558037066443 12465987891825837055599665)
          ·
            refine ⟨9349490918869377791699749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12465987891825837055599665 9349490918869377791699749)
            ·
              refine ⟨1753029547288008335943703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9349490918869377791699749 1753029547288008335943703)
              ·
                refine ⟨2629544320932012503915555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753029547288008335943703 2629544320932012503915555)
                ·
                  refine ⟨3944316481398018755873333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629544320932012503915555 3944316481398018755873333)
                  ·
                    refine ⟨369779670131064258363125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3944316481398018755873333 369779670131064258363125)
                    ·
                      rfl

theorem cell22_1080215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_1080215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080215 prefixEnd_1080215 := by exact prefixLift 1080215
  have htrace : WordTrace (prefixWord ++ tailWord_1080215) baseStart_1080215 baseEnd_1080215 := by
    simpa [prefixWord, tailWord_1080215, baseEnd_1080215] using wordTrace_append hprefix tailTrace_1080215
  have hstable : (prefixWord ++ tailWord_1080215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080215).length < 2 ^ (prefixWord ++ tailWord_1080215).sum := by decide
  have hdescent : baseEnd_1080215 < baseStart_1080215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080249 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 2, 3]
def baseStart_1080249 : Nat := 118140960795 + 1080249 * 2 ^ 59
def prefixEnd_1080249 : Nat := 4983230072969 + 3 ^ 40 * 1080249 * 2
def baseEnd_1080249 : Nat := 369791309025899503013021

theorem tailTrace_1080249 : CollatzResearch.WordTrace tailWord_1080249 prefixEnd_1080249 369791309025899503013021 := by
  unfold tailWord_1080249
  simp only [CollatzResearch.WordTrace]
  refine ⟨39399917863449839686163801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26266611908966559790775867 39399917863449839686163801)
  ·
    refine ⟨29549938397587379764622851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39399917863449839686163801 29549938397587379764622851)
    ·
      refine ⟨44324907596381069646934277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29549938397587379764622851 44324907596381069646934277)
      ·
        refine ⟨8310920174321450558800177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44324907596381069646934277 8310920174321450558800177)
        ·
          refine ⟨6233190130741087919100133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8310920174321450558800177 6233190130741087919100133)
          ·
            refine ⟨1168723149513953984831275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6233190130741087919100133 1168723149513953984831275)
            ·
              refine ⟨1753084724270930977246913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168723149513953984831275 1753084724270930977246913)
              ·
                refine ⟨1314813543203198232935185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753084724270930977246913 1314813543203198232935185)
                ·
                  refine ⟨986110157402398674701389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1314813543203198232935185 986110157402398674701389)
                  ·
                    refine ⟨369791309025899503013021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986110157402398674701389 369791309025899503013021)
                    ·
                      rfl

theorem cell22_1080249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_1080249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080249 prefixEnd_1080249 := by exact prefixLift 1080249
  have htrace : WordTrace (prefixWord ++ tailWord_1080249) baseStart_1080249 baseEnd_1080249 := by
    simpa [prefixWord, tailWord_1080249, baseEnd_1080249] using wordTrace_append hprefix tailTrace_1080249
  have hstable : (prefixWord ++ tailWord_1080249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080249).length < 2 ^ (prefixWord ++ tailWord_1080249).sum := by decide
  have hdescent : baseEnd_1080249 < baseStart_1080249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080410 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_1080410 : Nat := 118140960795 + 1080410 * 2 ^ 59
def prefixEnd_1080410 : Nat := 4983230072969 + 3 ^ 40 * 1080410 * 2
def baseEnd_1080410 : Nat := 369846422616148749737527

theorem tailTrace_1080410 : CollatzResearch.WordTrace tailWord_1080410 prefixEnd_1080410 369846422616148749737527 := by
  unfold tailWord_1080410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851447503966641045693671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26270526677244376121849789 9851447503966641045693671)
  ·
    refine ⟨14777171255949961568540507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9851447503966641045693671 14777171255949961568540507)
    ·
      refine ⟨22165756883924942352810761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14777171255949961568540507 22165756883924942352810761)
      ·
        refine ⟨16624317662943706764608071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22165756883924942352810761 16624317662943706764608071)
        ·
          refine ⟨24936476494415560146912107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16624317662943706764608071 24936476494415560146912107)
          ·
            refine ⟨37404714741623340220368161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24936476494415560146912107 37404714741623340220368161)
            ·
              refine ⟨28053536056217505165276121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37404714741623340220368161 28053536056217505165276121)
              ·
                refine ⟨21040152042163128873957091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28053536056217505165276121 21040152042163128873957091)
                ·
                  refine ⟨31560228063244693310935637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21040152042163128873957091 31560228063244693310935637)
                  ·
                    refine ⟨369846422616148749737527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31560228063244693310935637 369846422616148749737527)
                    ·
                      rfl

theorem cell22_1080410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_1080410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080410 prefixEnd_1080410 := by exact prefixLift 1080410
  have htrace : WordTrace (prefixWord ++ tailWord_1080410) baseStart_1080410 baseEnd_1080410 := by
    simpa [prefixWord, tailWord_1080410, baseEnd_1080410] using wordTrace_append hprefix tailTrace_1080410
  have hstable : (prefixWord ++ tailWord_1080410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080410).length < 2 ^ (prefixWord ++ tailWord_1080410).sum := by decide
  have hdescent : baseEnd_1080410 < baseStart_1080410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080418 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1080418 : Nat := 118140960795 + 1080418 * 2 ^ 59
def prefixEnd_1080418 : Nat := 4983230072969 + 3 ^ 40 * 1080418 * 2
def baseEnd_1080418 : Nat := 369849161179639395537503

theorem tailTrace_1080418 : CollatzResearch.WordTrace tailWord_1080418 prefixEnd_1080418 369849161179639395537503 := by
  unfold tailWord_1080418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851520449959395387266477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26270721199891721032710605 9851520449959395387266477)
  ·
    refine ⟨3694320168734773270224929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9851520449959395387266477 3694320168734773270224929)
    ·
      refine ⟨2770740126551079952668697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3694320168734773270224929 2770740126551079952668697)
      ·
        refine ⟨2078055094913309964501523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2770740126551079952668697 2078055094913309964501523)
        ·
          refine ⟨3117082642369964946752285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078055094913309964501523 3117082642369964946752285)
          ·
            refine ⟨1168905990888736855032107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3117082642369964946752285 1168905990888736855032107)
            ·
              refine ⟨1753358986333105282548161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168905990888736855032107 1753358986333105282548161)
              ·
                refine ⟨1315019239749828961911121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753358986333105282548161 1315019239749828961911121)
                ·
                  refine ⟨986264429812371721433341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1315019239749828961911121 986264429812371721433341)
                  ·
                    refine ⟨369849161179639395537503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986264429812371721433341 369849161179639395537503)
                    ·
                      rfl

theorem cell22_1080418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1080418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080418 prefixEnd_1080418 := by exact prefixLift 1080418
  have htrace : WordTrace (prefixWord ++ tailWord_1080418) baseStart_1080418 baseEnd_1080418 := by
    simpa [prefixWord, tailWord_1080418, baseEnd_1080418] using wordTrace_append hprefix tailTrace_1080418
  have hstable : (prefixWord ++ tailWord_1080418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080418).length < 2 ^ (prefixWord ++ tailWord_1080418).sum := by decide
  have hdescent : baseEnd_1080418 < baseStart_1080418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080429 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_1080429 : Nat := 118140960795 + 1080429 * 2 ^ 59
def prefixEnd_1080429 : Nat := 4983230072969 + 3 ^ 40 * 1080429 * 2
def baseEnd_1080429 : Nat := 369852926704439033512469

theorem tailTrace_1080429 : CollatzResearch.WordTrace tailWord_1080429 prefixEnd_1080429 369852926704439033512469 := by
  unfold tailWord_1080429
  simp only [CollatzResearch.WordTrace]
  refine ⟨39406483002797730427716341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26270988668531820285144227 39406483002797730427716341)
  ·
    refine ⟨3694357781512287227598407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39406483002797730427716341 3694357781512287227598407)
    ·
      refine ⟨5541536672268430841397611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694357781512287227598407 5541536672268430841397611)
      ·
        refine ⟨8312305008402646262096417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5541536672268430841397611 8312305008402646262096417)
        ·
          refine ⟨6234228756301984696572313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8312305008402646262096417 6234228756301984696572313)
          ·
            refine ⟨4675671567226488522429235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6234228756301984696572313 4675671567226488522429235)
            ·
              refine ⟨7013507350839732783643853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4675671567226488522429235 7013507350839732783643853)
              ·
                refine ⟨2630065256564899793866445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7013507350839732783643853 2630065256564899793866445)
                ·
                  refine ⟨986274471211837422699917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2630065256564899793866445 986274471211837422699917)
                  ·
                    refine ⟨369852926704439033512469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986274471211837422699917 369852926704439033512469)
                    ·
                      rfl

theorem cell22_1080429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_1080429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080429 prefixEnd_1080429 := by exact prefixLift 1080429
  have htrace : WordTrace (prefixWord ++ tailWord_1080429) baseStart_1080429 baseEnd_1080429 := by
    simpa [prefixWord, tailWord_1080429, baseEnd_1080429] using wordTrace_append hprefix tailTrace_1080429
  have hstable : (prefixWord ++ tailWord_1080429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080429).length < 2 ^ (prefixWord ++ tailWord_1080429).sum := by decide
  have hdescent : baseEnd_1080429 < baseStart_1080429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080493 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1080493 : Nat := 118140960795 + 1080493 * 2 ^ 59
def prefixEnd_1080493 : Nat := 4983230072969 + 3 ^ 40 * 1080493 * 2
def baseEnd_1080493 : Nat := 123291611737454733304091

theorem tailTrace_1080493 : CollatzResearch.WordTrace tailWord_1080493 prefixEnd_1080493 123291611737454733304091 := by
  unfold tailWord_1080493
  simp only [CollatzResearch.WordTrace]
  refine ⟨39408817274565869358046133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26272544849710579572030755 39408817274565869358046133)
  ·
    refine ⟨3694576619490550252316825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39408817274565869358046133 3694576619490550252316825)
    ·
      refine ⟨2770932464617912689237619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3694576619490550252316825 2770932464617912689237619)
      ·
        refine ⟨4156398696926869033856429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2770932464617912689237619 4156398696926869033856429)
        ·
          refine ⟨1558649511347575887696161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4156398696926869033856429 1558649511347575887696161)
          ·
            refine ⟨1168987133510681915772121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558649511347575887696161 1168987133510681915772121)
            ·
              refine ⟨876740350133011436829091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168987133510681915772121 876740350133011436829091)
              ·
                refine ⟨1315110525199517155243637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876740350133011436829091 1315110525199517155243637)
                ·
                  refine ⟨123291611737454733304091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1315110525199517155243637 123291611737454733304091)
                  ·
                    rfl

theorem cell22_1080493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1080493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080493 prefixEnd_1080493 := by exact prefixLift 1080493
  have htrace : WordTrace (prefixWord ++ tailWord_1080493) baseStart_1080493 baseEnd_1080493 := by
    simpa [prefixWord, tailWord_1080493, baseEnd_1080493] using wordTrace_append hprefix tailTrace_1080493
  have hstable : (prefixWord ++ tailWord_1080493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080493).length < 2 ^ (prefixWord ++ tailWord_1080493).sum := by decide
  have hdescent : baseEnd_1080493 < baseStart_1080493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080611 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 5]
def baseStart_1080611 : Nat := 118140960795 + 1080611 * 2 ^ 59
def prefixEnd_1080611 : Nat := 4983230072969 + 3 ^ 40 * 1080611 * 2
def baseEnd_1080611 : Nat := 123305076341283741820637

theorem tailTrace_1080611 : CollatzResearch.WordTrace tailWord_1080611 prefixEnd_1080611 123305076341283741820637 := by
  unfold tailWord_1080611
  simp only [CollatzResearch.WordTrace]
  refine ⟨39413121088138375510841687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26275414058758917007227791 39413121088138375510841687)
  ·
    refine ⟨59119681632207563266262531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39413121088138375510841687 59119681632207563266262531)
    ·
      refine ⟨88679522448311344899393797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59119681632207563266262531 88679522448311344899393797)
      ·
        refine ⟨16627410459058377168636337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88679522448311344899393797 16627410459058377168636337)
        ·
          refine ⟨12470557844293782876477253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16627410459058377168636337 12470557844293782876477253)
          ·
            refine ⟨2338229595805084289339485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12470557844293782876477253 2338229595805084289339485)
            ·
              refine ⟨876836098426906608502307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2338229595805084289339485 876836098426906608502307)
              ·
                refine ⟨1315254147640359912753461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876836098426906608502307 1315254147640359912753461)
                ·
                  refine ⟨123305076341283741820637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1315254147640359912753461 123305076341283741820637)
                  ·
                    rfl

theorem cell22_1080611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 5].length) (baseStart_1080611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080611 prefixEnd_1080611 := by exact prefixLift 1080611
  have htrace : WordTrace (prefixWord ++ tailWord_1080611) baseStart_1080611 baseEnd_1080611 := by
    simpa [prefixWord, tailWord_1080611, baseEnd_1080611] using wordTrace_append hprefix tailTrace_1080611
  have hstable : (prefixWord ++ tailWord_1080611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080611).length < 2 ^ (prefixWord ++ tailWord_1080611).sum := by decide
  have hdescent : baseEnd_1080611 < baseStart_1080611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080662 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1080662 : Nat := 118140960795 + 1080662 * 2 ^ 59
def prefixEnd_1080662 : Nat := 4983230072969 + 3 ^ 40 * 1080662 * 2
def baseEnd_1080662 : Nat := 123310895788701364145585

theorem tailTrace_1080662 : CollatzResearch.WordTrace tailWord_1080662 prefixEnd_1080662 123310895788701364145585 := by
  unfold tailWord_1080662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463436325684600701309265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26276654140635740813965493 2463436325684600701309265)
  ·
    refine ⟨1847577244263450525981949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2463436325684600701309265 1847577244263450525981949)
    ·
      refine ⟨692841466598793947243231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1847577244263450525981949 692841466598793947243231)
      ·
        refine ⟨1039262199898190920864847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692841466598793947243231 1039262199898190920864847)
        ·
          refine ⟨1558893299847286381297271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039262199898190920864847 1558893299847286381297271)
          ·
            refine ⟨2338339949770929571945907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558893299847286381297271 2338339949770929571945907)
            ·
              refine ⟨3507509924656394357918861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338339949770929571945907 3507509924656394357918861)
              ·
                refine ⟨1315316221746147884219573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3507509924656394357918861 1315316221746147884219573)
                ·
                  refine ⟨123310895788701364145585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1315316221746147884219573 123310895788701364145585)
                  ·
                    rfl

theorem cell22_1080662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1080662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080662 prefixEnd_1080662 := by exact prefixLift 1080662
  have htrace : WordTrace (prefixWord ++ tailWord_1080662) baseStart_1080662 baseEnd_1080662 := by
    simpa [prefixWord, tailWord_1080662, baseEnd_1080662] using wordTrace_append hprefix tailTrace_1080662
  have hstable : (prefixWord ++ tailWord_1080662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080662).length < 2 ^ (prefixWord ++ tailWord_1080662).sum := by decide
  have hdescent : baseEnd_1080662 < baseStart_1080662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080684 : List Nat := [2, 2, 1, 1, 5, 1, 2, 8]
def baseStart_1080684 : Nat := 118140960795 + 1080684 * 2 ^ 59
def prefixEnd_1080684 : Nat := 4983230072969 + 3 ^ 40 * 1080684 * 2
def baseEnd_1080684 : Nat := 41104468712855929820743

theorem tailTrace_1080684 : CollatzResearch.WordTrace tailWord_1080684 prefixEnd_1080684 41104468712855929820743 := by
  unfold tailWord_1080684
  simp only [CollatzResearch.WordTrace]
  refine ⟨19707891808436954489124553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26277189077915939318832737 19707891808436954489124553)
  ·
    refine ⟨14780918856327715866843415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19707891808436954489124553 14780918856327715866843415)
    ·
      refine ⟨22171378284491573800265123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14780918856327715866843415 22171378284491573800265123)
      ·
        refine ⟨33257067426737360700397685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22171378284491573800265123 33257067426737360700397685)
        ·
          refine ⟨3117850071256627565662283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33257067426737360700397685 3117850071256627565662283)
          ·
            refine ⟨4676775106884941348493425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117850071256627565662283 4676775106884941348493425)
            ·
              refine ⟨3507581330163706011370069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4676775106884941348493425 3507581330163706011370069)
              ·
                refine ⟨41104468712855929820743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3507581330163706011370069 41104468712855929820743)
                ·
                  rfl

theorem cell22_1080684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 8].length) (baseStart_1080684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080684 prefixEnd_1080684 := by exact prefixLift 1080684
  have htrace : WordTrace (prefixWord ++ tailWord_1080684) baseStart_1080684 baseEnd_1080684 := by
    simpa [prefixWord, tailWord_1080684, baseEnd_1080684] using wordTrace_append hprefix tailTrace_1080684
  have hstable : (prefixWord ++ tailWord_1080684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080684).length < 2 ^ (prefixWord ++ tailWord_1080684).sum := by decide
  have hdescent : baseEnd_1080684 < baseStart_1080684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080705 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1080705 : Nat := 118140960795 + 1080705 * 2 ^ 59
def prefixEnd_1080705 : Nat := 4983230072969 + 3 ^ 40 * 1080705 * 2
def baseEnd_1080705 : Nat := 369947407144866313611623

theorem tailTrace_1080705 : CollatzResearch.WordTrace tailWord_1080705 prefixEnd_1080705 369947407144866313611623 := by
  unfold tailWord_1080705
  simp only [CollatzResearch.WordTrace]
  refine ⟨39416549549797829564763569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26277699699865219709842379 39416549549797829564763569)
  ·
    refine ⟨29562412162348372173572677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39416549549797829564763569 29562412162348372173572677)
    ·
      refine ⟨5542952280440319782544877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29562412162348372173572677 5542952280440319782544877)
      ·
        refine ⟨2078607105165119918454329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5542952280440319782544877 2078607105165119918454329)
        ·
          refine ⟨1558955328873839938840747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2078607105165119918454329 1558955328873839938840747)
          ·
            refine ⟨2338432993310759908261121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558955328873839938840747 2338432993310759908261121)
            ·
              refine ⟨1753824744983069931195841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2338432993310759908261121 1753824744983069931195841)
              ·
                refine ⟨1315368558737302448396881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753824744983069931195841 1315368558737302448396881)
                ·
                  refine ⟨986526419052976836297661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1315368558737302448396881 986526419052976836297661)
                  ·
                    refine ⟨369947407144866313611623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986526419052976836297661 369947407144866313611623)
                    ·
                      rfl

theorem cell22_1080705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1080705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080705 prefixEnd_1080705 := by exact prefixLift 1080705
  have htrace : WordTrace (prefixWord ++ tailWord_1080705) baseStart_1080705 baseEnd_1080705 := by
    simpa [prefixWord, tailWord_1080705, baseEnd_1080705] using wordTrace_append hprefix tailTrace_1080705
  have hstable : (prefixWord ++ tailWord_1080705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080705).length < 2 ^ (prefixWord ++ tailWord_1080705).sum := by decide
  have hdescent : baseEnd_1080705 < baseStart_1080705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080716 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_1080716 : Nat := 118140960795 + 1080716 * 2 ^ 59
def prefixEnd_1080716 : Nat := 4983230072969 + 3 ^ 40 * 1080716 * 2
def baseEnd_1080716 : Nat := 369951172669665951586589

theorem tailTrace_1080716 : CollatzResearch.WordTrace tailWord_1080716 prefixEnd_1080716 369951172669665951586589 := by
  unfold tailWord_1080716
  simp only [CollatzResearch.WordTrace]
  refine ⟨19708475376378989221707001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26277967168505318962276001 19708475376378989221707001)
  ·
    refine ⟨14781356532284241916280251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19708475376378989221707001 14781356532284241916280251)
    ·
      refine ⟨22172034798426362874420377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14781356532284241916280251 22172034798426362874420377)
      ·
        refine ⟨16629026098819772155815283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22172034798426362874420377 16629026098819772155815283)
        ·
          refine ⟨24943539148229658233722925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16629026098819772155815283 24943539148229658233722925)
          ·
            refine ⟨9353827180586121837646097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24943539148229658233722925 9353827180586121837646097)
            ·
              refine ⟨7015370385439591378234573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9353827180586121837646097 7015370385439591378234573)
              ·
                refine ⟨2630763894539846766837965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7015370385439591378234573 2630763894539846766837965)
                ·
                  refine ⟨986536460452442537564237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2630763894539846766837965 986536460452442537564237)
                  ·
                    refine ⟨369951172669665951586589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986536460452442537564237 369951172669665951586589)
                    ·
                      rfl

theorem cell22_1080716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_1080716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080716 prefixEnd_1080716 := by exact prefixLift 1080716
  have htrace : WordTrace (prefixWord ++ tailWord_1080716) baseStart_1080716 baseEnd_1080716 := by
    simpa [prefixWord, tailWord_1080716, baseEnd_1080716] using wordTrace_append hprefix tailTrace_1080716
  have hstable : (prefixWord ++ tailWord_1080716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080716).length < 2 ^ (prefixWord ++ tailWord_1080716).sum := by decide
  have hdescent : baseEnd_1080716 < baseStart_1080716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080718 : List Nat := [4, 1, 1, 4, 2, 2, 1, 7]
def baseStart_1080718 : Nat := 118140960795 + 1080718 * 2 ^ 59
def prefixEnd_1080718 : Nat := 4983230072969 + 3 ^ 40 * 1080718 * 2
def baseEnd_1080718 : Nat := 41105761923393179226287

theorem tailTrace_1080718 : CollatzResearch.WordTrace tailWord_1080718 prefixEnd_1080718 41105761923393179226287 := by
  unfold tailWord_1080718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927127962343841598123351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26278015799167155189991205 4927127962343841598123351)
  ·
    refine ⟨7390691943515762397185027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4927127962343841598123351 7390691943515762397185027)
    ·
      refine ⟨11086037915273643595777541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7390691943515762397185027 11086037915273643595777541)
      ·
        refine ⟨2078632109113808174208289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11086037915273643595777541 2078632109113808174208289)
        ·
          refine ⟨1558974081835356130656217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2078632109113808174208289 1558974081835356130656217)
          ·
            refine ⟨1169230561376517097992163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558974081835356130656217 1169230561376517097992163)
            ·
              refine ⟨1753845842064775646988245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169230561376517097992163 1753845842064775646988245)
              ·
                refine ⟨41105761923393179226287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1753845842064775646988245 41105761923393179226287)
                ·
                  rfl

theorem cell22_1080718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_1080718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080718 prefixEnd_1080718 := by exact prefixLift 1080718
  have htrace : WordTrace (prefixWord ++ tailWord_1080718) baseStart_1080718 baseEnd_1080718 := by
    simpa [prefixWord, tailWord_1080718, baseEnd_1080718] using wordTrace_append hprefix tailTrace_1080718
  have hstable : (prefixWord ++ tailWord_1080718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080718).length < 2 ^ (prefixWord ++ tailWord_1080718).sum := by decide
  have hdescent : baseEnd_1080718 < baseStart_1080718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080733 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1080733 : Nat := 118140960795 + 1080733 * 2 ^ 59
def prefixEnd_1080733 : Nat := 4983230072969 + 3 ^ 40 * 1080733 * 2
def baseEnd_1080733 : Nat := 369956992117083573911537

theorem tailTrace_1080733 : CollatzResearch.WordTrace tailWord_1080733 prefixEnd_1080733 369956992117083573911537 := by
  unfold tailWord_1080733
  simp only [CollatzResearch.WordTrace]
  refine ⟨39417570793696390346782853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26278380529130926897855235 39417570793696390346782853)
  ·
    refine ⟨7390794523818073190021785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39417570793696390346782853 7390794523818073190021785)
    ·
      refine ⟨5543095892863554892516339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7390794523818073190021785 5543095892863554892516339)
      ·
        refine ⟨8314643839295332338774509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5543095892863554892516339 8314643839295332338774509)
        ·
          refine ⟨3117991439735749627040441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8314643839295332338774509 3117991439735749627040441)
          ·
            refine ⟨2338493579801812220280331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3117991439735749627040441 2338493579801812220280331)
            ·
              refine ⟨3507740369702718330420497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338493579801812220280331 3507740369702718330420497)
              ·
                refine ⟨2630805277277038747815373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507740369702718330420497 2630805277277038747815373)
                ·
                  refine ⟨986551978978889530430765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2630805277277038747815373 986551978978889530430765)
                  ·
                    refine ⟨369956992117083573911537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986551978978889530430765 369956992117083573911537)
                    ·
                      rfl

theorem cell22_1080733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1080733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080733 prefixEnd_1080733 := by exact prefixLift 1080733
  have htrace : WordTrace (prefixWord ++ tailWord_1080733) baseStart_1080733 baseEnd_1080733 := by
    simpa [prefixWord, tailWord_1080733, baseEnd_1080733] using wordTrace_append hprefix tailTrace_1080733
  have hstable : (prefixWord ++ tailWord_1080733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080733).length < 2 ^ (prefixWord ++ tailWord_1080733).sum := by decide
  have hdescent : baseEnd_1080733 < baseStart_1080733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080793 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_1080793 : Nat := 118140960795 + 1080793 * 2 ^ 59
def prefixEnd_1080793 : Nat := 4983230072969 + 3 ^ 40 * 1080793 * 2
def baseEnd_1080793 : Nat := 369977531343263417411353

theorem tailTrace_1080793 : CollatzResearch.WordTrace tailWord_1080793 prefixEnd_1080793 369977531343263417411353 := by
  unfold tailWord_1080793
  simp only [CollatzResearch.WordTrace]
  refine ⟨39419759173479020593967033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26279839448986013729311355 39419759173479020593967033)
  ·
    refine ⟨29564819380109265445475275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39419759173479020593967033 29564819380109265445475275)
    ·
      refine ⟨44347229070163898168212913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29564819380109265445475275 44347229070163898168212913)
      ·
        refine ⟨33260421802622923626159685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44347229070163898168212913 33260421802622923626159685)
        ·
          refine ⟨6236329087991798179904941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33260421802622923626159685 6236329087991798179904941)
          ·
            refine ⟨2338623407996924317464353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6236329087991798179904941 2338623407996924317464353)
            ·
              refine ⟨1753967555997693238098265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2338623407996924317464353 1753967555997693238098265)
              ·
                refine ⟨1315475666998269928573699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753967555997693238098265 1315475666998269928573699)
                ·
                  refine ⟨1973213500497404892860549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315475666998269928573699 1973213500497404892860549)
                  ·
                    refine ⟨369977531343263417411353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1973213500497404892860549 369977531343263417411353)
                    ·
                      rfl

theorem cell22_1080793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_1080793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080793 prefixEnd_1080793 := by exact prefixLift 1080793
  have htrace : WordTrace (prefixWord ++ tailWord_1080793) baseStart_1080793 baseEnd_1080793 := by
    simpa [prefixWord, tailWord_1080793, baseEnd_1080793] using wordTrace_append hprefix tailTrace_1080793
  have hstable : (prefixWord ++ tailWord_1080793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080793).length < 2 ^ (prefixWord ++ tailWord_1080793).sum := by decide
  have hdescent : baseEnd_1080793 < baseStart_1080793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080840 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 2, 3]
def baseStart_1080840 : Nat := 118140960795 + 1080840 * 2 ^ 59
def prefixEnd_1080840 : Nat := 4983230072969 + 3 ^ 40 * 1080840 * 2
def baseEnd_1080840 : Nat := 369993620403770961486209

theorem tailTrace_1080840 : CollatzResearch.WordTrace tailWord_1080840 prefixEnd_1080840 369993620403770961486209 := by
  unfold tailWord_1080840
  simp only [CollatzResearch.WordTrace]
  refine ⟨19710736702154373810463987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26280982269539165080618649 19710736702154373810463987)
  ·
    refine ⟨29566105053231560715695981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19710736702154373810463987 29566105053231560715695981)
    ·
      refine ⟨11087289394961835268385993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29566105053231560715695981 11087289394961835268385993)
      ·
        refine ⟨8315467046221376451289495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11087289394961835268385993 8315467046221376451289495)
        ·
          refine ⟨12473200569332064676934243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8315467046221376451289495 12473200569332064676934243)
          ·
            refine ⟨18709800853998097015401365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12473200569332064676934243 18709800853998097015401365)
            ·
              refine ⟨877021915031160797596939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18709800853998097015401365 877021915031160797596939)
              ·
                refine ⟨1315532872546741196395409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877021915031160797596939 1315532872546741196395409)
                ·
                  refine ⟨986649654410055897296557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1315532872546741196395409 986649654410055897296557)
                  ·
                    refine ⟨369993620403770961486209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986649654410055897296557 369993620403770961486209)
                    ·
                      rfl

theorem cell22_1080840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_1080840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080840 prefixEnd_1080840 := by exact prefixLift 1080840
  have htrace : WordTrace (prefixWord ++ tailWord_1080840) baseStart_1080840 baseEnd_1080840 := by
    simpa [prefixWord, tailWord_1080840, baseEnd_1080840] using wordTrace_append hprefix tailTrace_1080840
  have hstable : (prefixWord ++ tailWord_1080840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080840).length < 2 ^ (prefixWord ++ tailWord_1080840).sum := by decide
  have hdescent : baseEnd_1080840 < baseStart_1080840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080971 : List Nat := [1, 1, 1, 1, 4, 1, 5, 8]
def baseStart_1080971 : Nat := 118140960795 + 1080971 * 2 ^ 59
def prefixEnd_1080971 : Nat := 4983230072969 + 3 ^ 40 * 1080971 * 2
def baseEnd_1080971 : Nat := 41115384931214476273423

theorem tailTrace_1080971 : CollatzResearch.WordTrace tailWord_1080971 prefixEnd_1080971 41115384931214476273423 := by
  unfold tailWord_1080971
  simp only [CollatzResearch.WordTrace]
  refine ⟨39426251366834156993946767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26284167577889437995964511 39426251366834156993946767)
  ·
    refine ⟨59139377050251235490920151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39426251366834156993946767 59139377050251235490920151)
    ·
      refine ⟨88709065575376853236380227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59139377050251235490920151 88709065575376853236380227)
      ·
        refine ⟨133063598363065279854570341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88709065575376853236380227 133063598363065279854570341)
        ·
          refine ⟨24949424693074739972731939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133063598363065279854570341 24949424693074739972731939)
          ·
            refine ⟨37424137039612109959097909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24949424693074739972731939 37424137039612109959097909)
            ·
              refine ⟨3508512847463635308665429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37424137039612109959097909 3508512847463635308665429)
              ·
                refine ⟨41115384931214476273423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3508512847463635308665429 41115384931214476273423)
                ·
                  rfl

theorem cell22_1080971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 8].length) (baseStart_1080971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080971 prefixEnd_1080971 := by exact prefixLift 1080971
  have htrace : WordTrace (prefixWord ++ tailWord_1080971) baseStart_1080971 baseEnd_1080971 := by
    simpa [prefixWord, tailWord_1080971, baseEnd_1080971] using wordTrace_append hprefix tailTrace_1080971
  have hstable : (prefixWord ++ tailWord_1080971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080971).length < 2 ^ (prefixWord ++ tailWord_1080971).sum := by decide
  have hdescent : baseEnd_1080971 < baseStart_1080971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080990 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1080990 : Nat := 118140960795 + 1080990 * 2 ^ 59
def prefixEnd_1080990 : Nat := 4983230072969 + 3 ^ 40 * 1080990 * 2
def baseEnd_1080990 : Nat := 370044968469220570235749

theorem tailTrace_1080990 : CollatzResearch.WordTrace tailWord_1080990 prefixEnd_1080990 370044968469220570235749 := by
  unfold tailWord_1080990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4928368044220665404861053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26284629569176882159258949 4928368044220665404861053)
  ·
    refine ⟨1848138016582749526822895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4928368044220665404861053 1848138016582749526822895)
    ·
      refine ⟨2772207024874124290234343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848138016582749526822895 2772207024874124290234343)
      ·
        refine ⟨4158310537311186435351515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772207024874124290234343 4158310537311186435351515)
        ·
          refine ⟨6237465805966779653027273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4158310537311186435351515 6237465805966779653027273)
          ·
            refine ⟨4678099354475084739770455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6237465805966779653027273 4678099354475084739770455)
            ·
              refine ⟨7017149031712627109655683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678099354475084739770455 7017149031712627109655683)
              ·
                refine ⟨10525723547568940664483525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7017149031712627109655683 10525723547568940664483525)
                ·
                  refine ⟨1973573165169176374590661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10525723547568940664483525 1973573165169176374590661)
                  ·
                    refine ⟨370044968469220570235749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1973573165169176374590661 370044968469220570235749)
                    ·
                      rfl

theorem cell22_1080990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1080990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080990 prefixEnd_1080990 := by exact prefixLift 1080990
  have htrace : WordTrace (prefixWord ++ tailWord_1080990) baseStart_1080990 baseEnd_1080990 := by
    simpa [prefixWord, tailWord_1080990, baseEnd_1080990] using wordTrace_append hprefix tailTrace_1080990
  have hstable : (prefixWord ++ tailWord_1080990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080990).length < 2 ^ (prefixWord ++ tailWord_1080990).sum := by decide
  have hdescent : baseEnd_1080990 < baseStart_1080990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080994 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1080994 : Nat := 118140960795 + 1080994 * 2 ^ 59
def prefixEnd_1080994 : Nat := 4983230072969 + 3 ^ 40 * 1080994 * 2
def baseEnd_1080994 : Nat := 123348779250321964378579

theorem tailTrace_1080994 : CollatzResearch.WordTrace tailWord_1080994 prefixEnd_1080994 123348779250321964378579 := by
  unfold tailWord_1080994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9856772561437707980508509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26284726830500554614689357 9856772561437707980508509)
  ·
    refine ⟨3696289710539140492690691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9856772561437707980508509 3696289710539140492690691)
    ·
      refine ⟨5544434565808710739036037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3696289710539140492690691 5544434565808710739036037)
      ·
        refine ⟨1039581481089133263569257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5544434565808710739036037 1039581481089133263569257)
        ·
          refine ⟨779686110816849947676943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1039581481089133263569257 779686110816849947676943)
          ·
            refine ⟨1169529166225274921515415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779686110816849947676943 1169529166225274921515415)
            ·
              refine ⟨1754293749337912382273123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169529166225274921515415 1754293749337912382273123)
              ·
                refine ⟨2631440624006868573409685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754293749337912382273123 2631440624006868573409685)
                ·
                  refine ⟨123348779250321964378579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2631440624006868573409685 123348779250321964378579)
                  ·
                    rfl

theorem cell22_1080994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1080994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1080994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1080994 prefixEnd_1080994 := by exact prefixLift 1080994
  have htrace : WordTrace (prefixWord ++ tailWord_1080994) baseStart_1080994 baseEnd_1080994 := by
    simpa [prefixWord, tailWord_1080994, baseEnd_1080994] using wordTrace_append hprefix tailTrace_1080994
  have hstable : (prefixWord ++ tailWord_1080994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080994).length < 2 ^ (prefixWord ++ tailWord_1080994).sum := by decide
  have hdescent : baseEnd_1080994 < baseStart_1080994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081048 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1081048 : Nat := 118140960795 + 1081048 * 2 ^ 59
def prefixEnd_1081048 : Nat := 4983230072969 + 3 ^ 40 * 1081048 * 2
def baseEnd_1081048 : Nat := 370064823054527752285571

theorem tailTrace_1081048 : CollatzResearch.WordTrace tailWord_1081048 prefixEnd_1081048 370064823054527752285571 := by
  unfold tailWord_1081048
  simp only [CollatzResearch.WordTrace]
  refine ⟨19714529893777599572249899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26286039858370132762999865 19714529893777599572249899)
  ·
    refine ⟨29571794840666399358374849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19714529893777599572249899 29571794840666399358374849)
    ·
      refine ⟨22178846130499799518781137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29571794840666399358374849 22178846130499799518781137)
      ·
        refine ⟨16634134597874849639085853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22178846130499799518781137 16634134597874849639085853)
        ·
          refine ⟨6237800474203068614657195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16634134597874849639085853 6237800474203068614657195)
          ·
            refine ⟨9356700711304602921985793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6237800474203068614657195 9356700711304602921985793)
            ·
              refine ⟨7017525533478452191489345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9356700711304602921985793 7017525533478452191489345)
              ·
                refine ⟨5263144150108839143617009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7017525533478452191489345 5263144150108839143617009)
                ·
                  refine ⟨3947358112581629357712757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5263144150108839143617009 3947358112581629357712757)
                  ·
                    refine ⟨370064823054527752285571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3947358112581629357712757 370064823054527752285571)
                    ·
                      rfl

theorem cell22_1081048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1081048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081048 prefixEnd_1081048 := by exact prefixLift 1081048
  have htrace : WordTrace (prefixWord ++ tailWord_1081048) baseStart_1081048 baseEnd_1081048 := by
    simpa [prefixWord, tailWord_1081048, baseEnd_1081048] using wordTrace_append hprefix tailTrace_1081048
  have hstable : (prefixWord ++ tailWord_1081048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081048).length < 2 ^ (prefixWord ++ tailWord_1081048).sum := by decide
  have hdescent : baseEnd_1081048 < baseStart_1081048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081050 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_1081050 : Nat := 118140960795 + 1081050 * 2 ^ 59
def prefixEnd_1081050 : Nat := 4983230072969 + 3 ^ 40 * 1081050 * 2
def baseEnd_1081050 : Nat := 123355169231800137911855

theorem tailTrace_1081050 : CollatzResearch.WordTrace tailWord_1081050 prefixEnd_1081050 123355169231800137911855 := by
  unfold tailWord_1081050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9857283183386988371518151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26286088489031968990715069 9857283183386988371518151)
  ·
    refine ⟨14785924775080482557277227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9857283183386988371518151 14785924775080482557277227)
    ·
      refine ⟨22178887162620723835915841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14785924775080482557277227 22178887162620723835915841)
      ·
        refine ⟨16634165371965542876936881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22178887162620723835915841 16634165371965542876936881)
        ·
          refine ⟨12475624028974157157702661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16634165371965542876936881 12475624028974157157702661)
          ·
            refine ⟨2339179505432654467069249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12475624028974157157702661 2339179505432654467069249)
            ·
              refine ⟨1754384629074490850301937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2339179505432654467069249 1754384629074490850301937)
              ·
                refine ⟨1315788471805868137726453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1754384629074490850301937 1315788471805868137726453)
                ·
                  refine ⟨123355169231800137911855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1315788471805868137726453 123355169231800137911855)
                  ·
                    rfl

theorem cell22_1081050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_1081050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081050 prefixEnd_1081050 := by exact prefixLift 1081050
  have htrace : WordTrace (prefixWord ++ tailWord_1081050) baseStart_1081050 baseEnd_1081050 := by
    simpa [prefixWord, tailWord_1081050, baseEnd_1081050] using wordTrace_append hprefix tailTrace_1081050
  have hstable : (prefixWord ++ tailWord_1081050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081050).length < 2 ^ (prefixWord ++ tailWord_1081050).sum := by decide
  have hdescent : baseEnd_1081050 < baseStart_1081050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081101 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1081101 : Nat := 118140960795 + 1081101 * 2 ^ 59
def prefixEnd_1081101 : Nat := 4983230072969 + 3 ^ 40 * 1081101 * 2
def baseEnd_1081101 : Nat := 123360988679217760236803

theorem tailTrace_1081101 : CollatzResearch.WordTrace tailWord_1081101 prefixEnd_1081101 123360988679217760236803 := by
  unfold tailWord_1081101
  simp only [CollatzResearch.WordTrace]
  refine ⟨39430992856363189196179157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26287328570908792797452771 39430992856363189196179157)
  ·
    refine ⟨924163895071012246785449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39430992856363189196179157 924163895071012246785449)
    ·
      refine ⟨693122921303259185089087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 924163895071012246785449 693122921303259185089087)
      ·
        refine ⟨1039684381954888777633631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693122921303259185089087 1039684381954888777633631)
        ·
          refine ⟨1559526572932333166450447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039684381954888777633631 1559526572932333166450447)
          ·
            refine ⟨2339289859398499749675671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559526572932333166450447 2339289859398499749675671)
            ·
              refine ⟨3508934789097749624513507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339289859398499749675671 3508934789097749624513507)
              ·
                refine ⟨5263402183646624436770261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508934789097749624513507 5263402183646624436770261)
                ·
                  refine ⟨123360988679217760236803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5263402183646624436770261 123360988679217760236803)
                  ·
                    rfl

theorem cell22_1081101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1081101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081101 prefixEnd_1081101 := by exact prefixLift 1081101
  have htrace : WordTrace (prefixWord ++ tailWord_1081101) baseStart_1081101 baseEnd_1081101 := by
    simpa [prefixWord, tailWord_1081101, baseEnd_1081101] using wordTrace_append hprefix tailTrace_1081101
  have hstable : (prefixWord ++ tailWord_1081101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081101).length < 2 ^ (prefixWord ++ tailWord_1081101).sum := by decide
  have hdescent : baseEnd_1081101 < baseStart_1081101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081142 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1081142 : Nat := 118140960795 + 1081142 * 2 ^ 59
def prefixEnd_1081142 : Nat := 4983230072969 + 3 ^ 40 * 1081142 * 2
def baseEnd_1081142 : Nat := 370097001175542840435283

theorem tailTrace_1081142 : CollatzResearch.WordTrace tailWord_1081142 prefixEnd_1081142 370097001175542840435283 := by
  unfold tailWord_1081142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464530515575915824901355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26288325499476435465614453 2464530515575915824901355)
  ·
    refine ⟨3696795773363873737352033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2464530515575915824901355 3696795773363873737352033)
    ·
      refine ⟨2772596830022905303014025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3696795773363873737352033 2772596830022905303014025)
      ·
        refine ⟨2079447622517178977260519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2772596830022905303014025 2079447622517178977260519)
        ·
          refine ⟨3119171433775768465890779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079447622517178977260519 3119171433775768465890779)
          ·
            refine ⟨4678757150663652698836169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119171433775768465890779 4678757150663652698836169)
            ·
              refine ⟨3509067862997739524127127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4678757150663652698836169 3509067862997739524127127)
              ·
                refine ⟨5263601794496609286190691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509067862997739524127127 5263601794496609286190691)
                ·
                  refine ⟨7895402691744913929286037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263601794496609286190691 7895402691744913929286037)
                  ·
                    refine ⟨370097001175542840435283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7895402691744913929286037 370097001175542840435283)
                    ·
                      rfl

theorem cell22_1081142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1081142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081142 prefixEnd_1081142 := by exact prefixLift 1081142
  have htrace : WordTrace (prefixWord ++ tailWord_1081142) baseStart_1081142 baseEnd_1081142 := by
    simpa [prefixWord, tailWord_1081142, baseEnd_1081142] using wordTrace_append hprefix tailTrace_1081142
  have hstable : (prefixWord ++ tailWord_1081142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081142).length < 2 ^ (prefixWord ++ tailWord_1081142).sum := by decide
  have hdescent : baseEnd_1081142 < baseStart_1081142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081185 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 5]
def baseStart_1081185 : Nat := 118140960795 + 1081185 * 2 ^ 59
def prefixEnd_1081185 : Nat := 4983230072969 + 3 ^ 40 * 1081185 * 2
def baseEnd_1081185 : Nat := 123370573651435020536717

theorem tailTrace_1081185 : CollatzResearch.WordTrace tailWord_1081185 prefixEnd_1081185 123370573651435020536717 := by
  unfold tailWord_1081185
  simp only [CollatzResearch.WordTrace]
  refine ⟨39434056588058871542237009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26289371058705914361491339 39434056588058871542237009)
  ·
    refine ⟨29575542441044153656677757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39434056588058871542237009 29575542441044153656677757)
    ·
      refine ⟨11090828415391557621254159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29575542441044153656677757 11090828415391557621254159)
      ·
        refine ⟨16636242623087336431881239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11090828415391557621254159 16636242623087336431881239)
        ·
          refine ⟨24954363934631004647821859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16636242623087336431881239 24954363934631004647821859)
          ·
            refine ⟨37431545901946506971732789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24954363934631004647821859 37431545901946506971732789)
            ·
              refine ⟨3509207428307485028599949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37431545901946506971732789 3509207428307485028599949)
              ·
                refine ⟨1315952785615306885724981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3509207428307485028599949 1315952785615306885724981)
                ·
                  refine ⟨123370573651435020536717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1315952785615306885724981 123370573651435020536717)
                  ·
                    rfl

theorem cell22_1081185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_1081185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081185 prefixEnd_1081185 := by exact prefixLift 1081185
  have htrace : WordTrace (prefixWord ++ tailWord_1081185) baseStart_1081185 baseEnd_1081185 := by
    simpa [prefixWord, tailWord_1081185, baseEnd_1081185] using wordTrace_append hprefix tailTrace_1081185
  have hstable : (prefixWord ++ tailWord_1081185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081185).length < 2 ^ (prefixWord ++ tailWord_1081185).sum := by decide
  have hdescent : baseEnd_1081185 < baseStart_1081185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081223 : List Nat := [1, 1, 4, 2, 4, 2, 2, 2, 1, 3]
def baseStart_1081223 : Nat := 118140960795 + 1081223 * 2 ^ 59
def prefixEnd_1081223 : Nat := 4983230072969 + 3 ^ 40 * 1081223 * 2
def baseEnd_1081223 : Nat := 370124729130885629160035

theorem tailTrace_1081223 : CollatzResearch.WordTrace tailWord_1081223 prefixEnd_1081223 370124729130885629160035 := by
  unfold tailWord_1081223
  simp only [CollatzResearch.WordTrace]
  refine ⟨39435442561921204032120323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26290295041280802688080215 39435442561921204032120323)
  ·
    refine ⟨59153163842881806048180485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39435442561921204032120323 59153163842881806048180485)
    ·
      refine ⟨11091218220540338634033841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59153163842881806048180485 11091218220540338634033841)
      ·
        refine ⟨8318413665405253975525381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11091218220540338634033841 8318413665405253975525381)
        ·
          refine ⟨1559702562263485120411009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8318413665405253975525381 1559702562263485120411009)
          ·
            refine ⟨1169776921697613840308257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1559702562263485120411009 1169776921697613840308257)
            ·
              refine ⟨877332691273210380231193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169776921697613840308257 877332691273210380231193)
              ·
                refine ⟨657999518454907785173395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877332691273210380231193 657999518454907785173395)
                ·
                  refine ⟨986999277682361677760093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657999518454907785173395 986999277682361677760093)
                  ·
                    refine ⟨370124729130885629160035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 986999277682361677760093 370124729130885629160035)
                    ·
                      rfl

theorem cell22_1081223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_1081223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081223 prefixEnd_1081223 := by exact prefixLift 1081223
  have htrace : WordTrace (prefixWord ++ tailWord_1081223) baseStart_1081223 baseEnd_1081223 := by
    simpa [prefixWord, tailWord_1081223, baseEnd_1081223] using wordTrace_append hprefix tailTrace_1081223
  have hstable : (prefixWord ++ tailWord_1081223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081223).length < 2 ^ (prefixWord ++ tailWord_1081223).sum := by decide
  have hdescent : baseEnd_1081223 < baseStart_1081223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081247 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 6]
def baseStart_1081247 : Nat := 118140960795 + 1081247 * 2 ^ 59
def prefixEnd_1081247 : Nat := 4983230072969 + 3 ^ 40 * 1081247 * 2
def baseEnd_1081247 : Nat := 123377648273785855519987

theorem tailTrace_1081247 : CollatzResearch.WordTrace tailWord_1081247 prefixEnd_1081247 123377648273785855519987 := by
  unfold tailWord_1081247
  simp only [CollatzResearch.WordTrace]
  refine ⟨39436317913834256130993995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26290878609222837420662663 39436317913834256130993995)
  ·
    refine ⟨59154476870751384196490993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39436317913834256130993995 59154476870751384196490993)
    ·
      refine ⟨44365857653063538147368245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59154476870751384196490993 44365857653063538147368245)
      ·
        refine ⟨4159299154974706701315773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44365857653063538147368245 4159299154974706701315773)
        ·
          refine ⟨1559737183115515012993415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4159299154974706701315773 1559737183115515012993415)
          ·
            refine ⟨2339605774673272519490123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559737183115515012993415 2339605774673272519490123)
            ·
              refine ⟨3509408662009908779235185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339605774673272519490123 3509408662009908779235185)
              ·
                refine ⟨2632056496507431584426389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3509408662009908779235185 2632056496507431584426389)
                ·
                  refine ⟨123377648273785855519987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2632056496507431584426389 123377648273785855519987)
                  ·
                    rfl

theorem cell22_1081247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 6].length) (baseStart_1081247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081247 prefixEnd_1081247 := by exact prefixLift 1081247
  have htrace : WordTrace (prefixWord ++ tailWord_1081247) baseStart_1081247 baseEnd_1081247 := by
    simpa [prefixWord, tailWord_1081247, baseEnd_1081247] using wordTrace_append hprefix tailTrace_1081247
  have hstable : (prefixWord ++ tailWord_1081247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081247).length < 2 ^ (prefixWord ++ tailWord_1081247).sum := by decide
  have hdescent : baseEnd_1081247 < baseStart_1081247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081354 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_1081354 : Nat := 118140960795 + 1081354 * 2 ^ 59
def prefixEnd_1081354 : Nat := 4983230072969 + 3 ^ 40 * 1081354 * 2
def baseEnd_1081354 : Nat := 123389857702681651378211

theorem tailTrace_1081354 : CollatzResearch.WordTrace tailWord_1081354 prefixEnd_1081354 123389857702681651378211 := by
  unfold tailWord_1081354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860055131111653351284779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26293480349631075603426077 9860055131111653351284779)
  ·
    refine ⟨14790082696667480026927169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9860055131111653351284779 14790082696667480026927169)
    ·
      refine ⟨11092562022500610020195377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14790082696667480026927169 11092562022500610020195377)
      ·
        refine ⟨8319421516875457515146533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11092562022500610020195377 8319421516875457515146533)
        ·
          refine ⟨1559891534414148284089975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8319421516875457515146533 1559891534414148284089975)
          ·
            refine ⟨2339837301621222426134963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559891534414148284089975 2339837301621222426134963)
            ·
              refine ⟨3509755952431833639202445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339837301621222426134963 3509755952431833639202445)
              ·
                refine ⟨1316158482161937614700917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3509755952431833639202445 1316158482161937614700917)
                ·
                  refine ⟨123389857702681651378211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1316158482161937614700917 123389857702681651378211)
                  ·
                    rfl

theorem cell22_1081354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_1081354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081354 prefixEnd_1081354 := by exact prefixLift 1081354
  have htrace : WordTrace (prefixWord ++ tailWord_1081354) baseStart_1081354 baseEnd_1081354 := by
    simpa [prefixWord, tailWord_1081354, baseEnd_1081354] using wordTrace_append hprefix tailTrace_1081354
  have hstable : (prefixWord ++ tailWord_1081354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081354).length < 2 ^ (prefixWord ++ tailWord_1081354).sum := by decide
  have hdescent : baseEnd_1081354 < baseStart_1081354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081429 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1081429 : Nat := 118140960795 + 1081429 * 2 ^ 59
def prefixEnd_1081429 : Nat := 4983230072969 + 3 ^ 40 * 1081429 * 2
def baseEnd_1081429 : Nat := 370195247140769758509403

theorem tailTrace_1081429 : CollatzResearch.WordTrace tailWord_1081429 prefixEnd_1081429 370195247140769758509403 := by
  unfold tailWord_1081429
  simp only [CollatzResearch.WordTrace]
  refine ⟨39442955999174901214119341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26295303999449934142746227 39442955999174901214119341)
  ·
    refine ⟨14791108499690587955294753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39442955999174901214119341 14791108499690587955294753)
    ·
      refine ⟨11093331374767940966471065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14791108499690587955294753 11093331374767940966471065)
      ·
        refine ⟨8319998531075955724853299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11093331374767940966471065 8319998531075955724853299)
        ·
          refine ⟨12479997796613933587279949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8319998531075955724853299 12479997796613933587279949)
          ·
            refine ⟨4679999173730225095229981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12479997796613933587279949 4679999173730225095229981)
            ·
              refine ⟨1754999690148834410711243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4679999173730225095229981 1754999690148834410711243)
              ·
                refine ⟨2632499535223251616066865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754999690148834410711243 2632499535223251616066865)
                ·
                  refine ⟨1974374651417438712050149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2632499535223251616066865 1974374651417438712050149)
                  ·
                    refine ⟨370195247140769758509403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1974374651417438712050149 370195247140769758509403)
                    ·
                      rfl

theorem cell22_1081429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1081429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081429 prefixEnd_1081429 := by exact prefixLift 1081429
  have htrace : WordTrace (prefixWord ++ tailWord_1081429) baseStart_1081429 baseEnd_1081429 := by
    simpa [prefixWord, tailWord_1081429, baseEnd_1081429] using wordTrace_append hprefix tailTrace_1081429
  have hstable : (prefixWord ++ tailWord_1081429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081429).length < 2 ^ (prefixWord ++ tailWord_1081429).sum := by decide
  have hdescent : baseEnd_1081429 < baseStart_1081429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081536 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_1081536 : Nat := 118140960795 + 1081536 * 2 ^ 59
def prefixEnd_1081536 : Nat := 4983230072969 + 3 ^ 40 * 1081536 * 2
def baseEnd_1081536 : Nat := 370231875427457146084075

theorem tailTrace_1081536 : CollatzResearch.WordTrace tailWord_1081536 prefixEnd_1081536 370231875427457146084075 := by
  unfold tailWord_1081536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19723429304893629244132231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26297905739858172325509641 19723429304893629244132231)
  ·
    refine ⟨29585143957340443866198347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19723429304893629244132231 29585143957340443866198347)
    ·
      refine ⟨44377715936010665799297521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29585143957340443866198347 44377715936010665799297521)
      ·
        refine ⟨33283286952007999349473141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44377715936010665799297521 33283286952007999349473141)
        ·
          refine ⟨3120308151750749939013107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33283286952007999349473141 3120308151750749939013107)
          ·
            refine ⟨4680462227626124908519661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120308151750749939013107 4680462227626124908519661)
            ·
              refine ⟨1755173335359796840694873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4680462227626124908519661 1755173335359796840694873)
              ·
                refine ⟨1316380001519847630521155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1755173335359796840694873 1316380001519847630521155)
                ·
                  refine ⟨1974570002279771445781733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316380001519847630521155 1974570002279771445781733)
                  ·
                    refine ⟨370231875427457146084075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1974570002279771445781733 370231875427457146084075)
                    ·
                      rfl

theorem cell22_1081536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_1081536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081536 prefixEnd_1081536 := by exact prefixLift 1081536
  have htrace : WordTrace (prefixWord ++ tailWord_1081536) baseStart_1081536 baseEnd_1081536 := by
    simpa [prefixWord, tailWord_1081536, baseEnd_1081536] using wordTrace_append hprefix tailTrace_1081536
  have hstable : (prefixWord ++ tailWord_1081536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081536).length < 2 ^ (prefixWord ++ tailWord_1081536).sum := by decide
  have hdescent : baseEnd_1081536 < baseStart_1081536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081596 : List Nat := [2, 2, 2, 1, 4, 2, 3, 6]
def baseStart_1081596 : Nat := 118140960795 + 1081596 * 2 ^ 59
def prefixEnd_1081596 : Nat := 4983230072969 + 3 ^ 40 * 1081596 * 2
def baseEnd_1081596 : Nat := 41139157183737443287099

theorem tailTrace_1081596 : CollatzResearch.WordTrace tailWord_1081596 prefixEnd_1081596 41139157183737443287099 := by
  unfold tailWord_1081596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19724523494784944367724321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26299364659713259156965761 19724523494784944367724321)
  ·
    refine ⟨14793392621088708275793241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19724523494784944367724321 14793392621088708275793241)
    ·
      refine ⟨11095044465816531206844931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14793392621088708275793241 11095044465816531206844931)
      ·
        refine ⟨16642566698724796810267397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11095044465816531206844931 16642566698724796810267397)
        ·
          refine ⟨3120481256010899401925137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16642566698724796810267397 3120481256010899401925137)
          ·
            refine ⟨2340360942008174551443853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3120481256010899401925137 2340360942008174551443853)
            ·
              refine ⟨877635353253065456791445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2340360942008174551443853 877635353253065456791445)
              ·
                refine ⟨41139157183737443287099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 877635353253065456791445 41139157183737443287099)
                ·
                  rfl

theorem cell22_1081596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 6].length) (baseStart_1081596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081596 prefixEnd_1081596 := by exact prefixLift 1081596
  have htrace : WordTrace (prefixWord ++ tailWord_1081596) baseStart_1081596 baseEnd_1081596 := by
    simpa [prefixWord, tailWord_1081596, baseEnd_1081596] using wordTrace_append hprefix tailTrace_1081596
  have hstable : (prefixWord ++ tailWord_1081596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081596).length < 2 ^ (prefixWord ++ tailWord_1081596).sum := by decide
  have hdescent : baseEnd_1081596 < baseStart_1081596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081624 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 7]
def baseStart_1081624 : Nat := 118140960795 + 1081624 * 2 ^ 59
def prefixEnd_1081624 : Nat := 4983230072969 + 3 ^ 40 * 1081624 * 2
def baseEnd_1081624 : Nat := 123420666541951416627935

theorem tailTrace_1081624 : CollatzResearch.WordTrace tailWord_1081624 prefixEnd_1081624 123420666541951416627935 := by
  unfold tailWord_1081624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19725034116734224758733963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26300045488978966344978617 19725034116734224758733963)
  ·
    refine ⟨29587551175101337138100945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19725034116734224758733963 29587551175101337138100945)
    ·
      refine ⟨22190663381326002853575709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29587551175101337138100945 22190663381326002853575709)
      ·
        refine ⟨8321498767997251070090891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22190663381326002853575709 8321498767997251070090891)
        ·
          refine ⟨12482248151995876605136337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8321498767997251070090891 12482248151995876605136337)
          ·
            refine ⟨9361686113996907453852253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12482248151995876605136337 9361686113996907453852253)
            ·
              refine ⟨3510632292748840295194595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9361686113996907453852253 3510632292748840295194595)
              ·
                refine ⟨5265948439123260442791893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510632292748840295194595 5265948439123260442791893)
                ·
                  refine ⟨123420666541951416627935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5265948439123260442791893 123420666541951416627935)
                  ·
                    rfl

theorem cell22_1081624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_1081624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081624 prefixEnd_1081624 := by exact prefixLift 1081624
  have htrace : WordTrace (prefixWord ++ tailWord_1081624) baseStart_1081624 baseEnd_1081624 := by
    simpa [prefixWord, tailWord_1081624, baseEnd_1081624] using wordTrace_append hprefix tailTrace_1081624
  have hstable : (prefixWord ++ tailWord_1081624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081624).length < 2 ^ (prefixWord ++ tailWord_1081624).sum := by decide
  have hdescent : baseEnd_1081624 < baseStart_1081624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081662 : List Nat := [4, 2, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_1081662 : Nat := 118140960795 + 1081662 * 2 ^ 59
def prefixEnd_1081662 : Nat := 4983230072969 + 3 ^ 40 * 1081662 * 2
def baseEnd_1081662 : Nat := 370275007802434817433689

theorem tailTrace_1081662 : CollatzResearch.WordTrace tailWord_1081662 prefixEnd_1081662 370275007802434817433689 := by
  unfold tailWord_1081662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931431775916347750918905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26300969471553854671567493 4931431775916347750918905)
  ·
    refine ⟨3698573831937260813189179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4931431775916347750918905 3698573831937260813189179)
    ·
      refine ⟨5547860747905891219783769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3698573831937260813189179 5547860747905891219783769)
      ·
        refine ⟨4160895560929418414837827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5547860747905891219783769 4160895560929418414837827)
        ·
          refine ⟨6241343341394127622256741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4160895560929418414837827 6241343341394127622256741)
          ·
            refine ⟨1170251876511398929173139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6241343341394127622256741 1170251876511398929173139)
            ·
              refine ⟨1755377814767098393759709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170251876511398929173139 1755377814767098393759709)
              ·
                refine ⟨658266680537661897659891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755377814767098393759709 658266680537661897659891)
                ·
                  refine ⟨987400020806492846489837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658266680537661897659891 987400020806492846489837)
                  ·
                    refine ⟨370275007802434817433689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 987400020806492846489837 370275007802434817433689)
                    ·
                      rfl

theorem cell22_1081662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_1081662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081662 prefixEnd_1081662 := by exact prefixLift 1081662
  have htrace : WordTrace (prefixWord ++ tailWord_1081662) baseStart_1081662 baseEnd_1081662 := by
    simpa [prefixWord, tailWord_1081662, baseEnd_1081662] using wordTrace_append hprefix tailTrace_1081662
  have hstable : (prefixWord ++ tailWord_1081662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081662).length < 2 ^ (prefixWord ++ tailWord_1081662).sum := by decide
  have hdescent : baseEnd_1081662 < baseStart_1081662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081671 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 1, 4]
def baseStart_1081671 : Nat := 118140960795 + 1081671 * 2 ^ 59
def prefixEnd_1081671 : Nat := 4983230072969 + 3 ^ 40 * 1081671 * 2
def baseEnd_1081671 : Nat := 370278088686361793958661

theorem tailTrace_1081671 : CollatzResearch.WordTrace tailWord_1081671 prefixEnd_1081671 370278088686361793958661 := by
  unfold tailWord_1081671
  simp only [CollatzResearch.WordTrace]
  refine ⟨39451782464298176544428867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26301188309532117696285911 39451782464298176544428867)
  ·
    refine ⟨59177673696447264816643301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39451782464298176544428867 59177673696447264816643301)
    ·
      refine ⟨11095813818083862153120619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59177673696447264816643301 11095813818083862153120619)
      ·
        refine ⟨16643720727125793229680929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11095813818083862153120619 16643720727125793229680929)
        ·
          refine ⟨12482790545344344922260697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16643720727125793229680929 12482790545344344922260697)
          ·
            refine ⟨9362092909008258691695523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12482790545344344922260697 9362092909008258691695523)
            ·
              refine ⟨14043139363512388037543285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9362092909008258691695523 14043139363512388037543285)
              ·
                refine ⟨1316544315329286378519683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14043139363512388037543285 1316544315329286378519683)
                ·
                  refine ⟨1974816472993929567779525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316544315329286378519683 1974816472993929567779525)
                  ·
                    refine ⟨370278088686361793958661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1974816472993929567779525 370278088686361793958661)
                    ·
                      rfl

theorem cell22_1081671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_1081671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081671 prefixEnd_1081671 := by exact prefixLift 1081671
  have htrace : WordTrace (prefixWord ++ tailWord_1081671) baseStart_1081671 baseEnd_1081671 := by
    simpa [prefixWord, tailWord_1081671, baseEnd_1081671] using wordTrace_append hprefix tailTrace_1081671
  have hstable : (prefixWord ++ tailWord_1081671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081671).length < 2 ^ (prefixWord ++ tailWord_1081671).sum := by decide
  have hdescent : baseEnd_1081671 < baseStart_1081671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081692 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 5]
def baseStart_1081692 : Nat := 118140960795 + 1081692 * 2 ^ 59
def prefixEnd_1081692 : Nat := 4983230072969 + 3 ^ 40 * 1081692 * 2
def baseEnd_1081692 : Nat := 123428425805174913061199

theorem tailTrace_1081692 : CollatzResearch.WordTrace tailWord_1081692 prefixEnd_1081692 123428425805174913061199 := by
  unfold tailWord_1081692
  simp only [CollatzResearch.WordTrace]
  refine ⟨19726274198611048565471665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26301698931481398087295553 19726274198611048565471665)
  ·
    refine ⟨14794705648958286424103749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19726274198611048565471665 14794705648958286424103749)
    ·
      refine ⟨2774007309179678704519453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14794705648958286424103749 2774007309179678704519453)
      ·
        refine ⟨1040252740942379514194795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2774007309179678704519453 1040252740942379514194795)
        ·
          refine ⟨1560379111413569271292193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040252740942379514194795 1560379111413569271292193)
          ·
            refine ⟨1170284333560176953469145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1560379111413569271292193 1170284333560176953469145)
            ·
              refine ⟨877713250170132715101859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170284333560176953469145 877713250170132715101859)
              ·
                refine ⟨1316569875255199072652789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877713250170132715101859 1316569875255199072652789)
                ·
                  refine ⟨123428425805174913061199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1316569875255199072652789 123428425805174913061199)
                  ·
                    rfl

theorem cell22_1081692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_1081692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081692 prefixEnd_1081692 := by exact prefixLift 1081692
  have htrace : WordTrace (prefixWord ++ tailWord_1081692) baseStart_1081692 baseEnd_1081692 := by
    simpa [prefixWord, tailWord_1081692, baseEnd_1081692] using wordTrace_append hprefix tailTrace_1081692
  have hstable : (prefixWord ++ tailWord_1081692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081692).length < 2 ^ (prefixWord ++ tailWord_1081692).sum := by decide
  have hdescent : baseEnd_1081692 < baseStart_1081692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081731 : List Nat := [1, 1, 1, 3, 7, 9]
def baseStart_1081731 : Nat := 118140960795 + 1081731 * 2 ^ 59
def prefixEnd_1081731 : Nat := 4983230072969 + 3 ^ 40 * 1081731 * 2
def baseEnd_1081731 : Nat := 4571587998920267129117

theorem tailTrace_1081731 : CollatzResearch.WordTrace tailWord_1081731 prefixEnd_1081731 4571587998920267129117 := by
  unfold tailWord_1081731
  simp only [CollatzResearch.WordTrace]
  refine ⟨39453970844080806791613047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26302647229387204527742031 39453970844080806791613047)
  ·
    refine ⟨59180956266121210187419571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39453970844080806791613047 59180956266121210187419571)
    ·
      refine ⟨88771434399181815281129357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59180956266121210187419571 88771434399181815281129357)
      ·
        refine ⟨33289287899693180730423509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88771434399181815281129357 33289287899693180730423509)
        ·
          refine ⟨780217685149058923369301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33289287899693180730423509 780217685149058923369301)
          ·
            refine ⟨4571587998920267129117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 780217685149058923369301 4571587998920267129117)
            ·
              rfl

theorem cell22_1081731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 9].length) (baseStart_1081731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081731 prefixEnd_1081731 := by exact prefixLift 1081731
  have htrace : WordTrace (prefixWord ++ tailWord_1081731) baseStart_1081731 baseEnd_1081731 := by
    simpa [prefixWord, tailWord_1081731, baseEnd_1081731] using wordTrace_append hprefix tailTrace_1081731
  have hstable : (prefixWord ++ tailWord_1081731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081731).length < 2 ^ (prefixWord ++ tailWord_1081731).sum := by decide
  have hdescent : baseEnd_1081731 < baseStart_1081731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081763 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 3, 3]
def baseStart_1081763 : Nat := 118140960795 + 1081763 * 2 ^ 59
def prefixEnd_1081763 : Nat := 4983230072969 + 3 ^ 40 * 1081763 * 2
def baseEnd_1081763 : Nat := 370309582166504220658379

theorem tailTrace_1081763 : CollatzResearch.WordTrace tailWord_1081763 prefixEnd_1081763 370309582166504220658379 := by
  unfold tailWord_1081763
  simp only [CollatzResearch.WordTrace]
  refine ⟨39455137979964876256777943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26303425319976584171185295 39455137979964876256777943)
  ·
    refine ⟨59182706969947314385166915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39455137979964876256777943 59182706969947314385166915)
    ·
      refine ⟨88774060454920971577750373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59182706969947314385166915 88774060454920971577750373)
      ·
        refine ⟨16645136335297682170828195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88774060454920971577750373 16645136335297682170828195)
        ·
          refine ⟨24967704502946523256242293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16645136335297682170828195 24967704502946523256242293)
          ·
            refine ⟨2340722297151236555272715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24967704502946523256242293 2340722297151236555272715)
            ·
              refine ⟨3511083445726854832909073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340722297151236555272715 3511083445726854832909073)
              ·
                refine ⟨2633312584295141124681805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3511083445726854832909073 2633312584295141124681805)
                ·
                  refine ⟨987492219110677921755677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2633312584295141124681805 987492219110677921755677)
                  ·
                    refine ⟨370309582166504220658379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 987492219110677921755677 370309582166504220658379)
                    ·
                      rfl

theorem cell22_1081763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 3].length) (baseStart_1081763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081763 prefixEnd_1081763 := by exact prefixLift 1081763
  have htrace : WordTrace (prefixWord ++ tailWord_1081763) baseStart_1081763 baseEnd_1081763 := by
    simpa [prefixWord, tailWord_1081763, baseEnd_1081763] using wordTrace_append hprefix tailTrace_1081763
  have hstable : (prefixWord ++ tailWord_1081763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081763).length < 2 ^ (prefixWord ++ tailWord_1081763).sum := by decide
  have hdescent : baseEnd_1081763 < baseStart_1081763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081823 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 1, 4]
def baseStart_1081823 : Nat := 118140960795 + 1081823 * 2 ^ 59
def prefixEnd_1081823 : Nat := 4983230072969 + 3 ^ 40 * 1081823 * 2
def baseEnd_1081823 : Nat := 370330121392684064158195

theorem tailTrace_1081823 : CollatzResearch.WordTrace tailWord_1081823 prefixEnd_1081823 370330121392684064158195 := by
  unfold tailWord_1081823
  simp only [CollatzResearch.WordTrace]
  refine ⟨39457326359747506503962123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26304884239831671002641415 39457326359747506503962123)
  ·
    refine ⟨59185989539621259755943185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39457326359747506503962123 59185989539621259755943185)
    ·
      refine ⟨44389492154715944816957389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59185989539621259755943185 44389492154715944816957389)
      ·
        refine ⟨16646059558018479306359021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44389492154715944816957389 16646059558018479306359021)
        ·
          refine ⟨6242272334256929739884633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16646059558018479306359021 6242272334256929739884633)
          ·
            refine ⟨4681704250692697304913475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6242272334256929739884633 4681704250692697304913475)
            ·
              refine ⟨7022556376039045957370213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681704250692697304913475 7022556376039045957370213)
              ·
                refine ⟨1316729320507321117006915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7022556376039045957370213 1316729320507321117006915)
                ·
                  refine ⟨1975093980760981675510373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316729320507321117006915 1975093980760981675510373)
                  ·
                    refine ⟨370330121392684064158195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975093980760981675510373 370330121392684064158195)
                    ·
                      rfl

theorem cell22_1081823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_1081823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081823 prefixEnd_1081823 := by exact prefixLift 1081823
  have htrace : WordTrace (prefixWord ++ tailWord_1081823) baseStart_1081823 baseEnd_1081823 := by
    simpa [prefixWord, tailWord_1081823, baseEnd_1081823] using wordTrace_append hprefix tailTrace_1081823
  have hstable : (prefixWord ++ tailWord_1081823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081823).length < 2 ^ (prefixWord ++ tailWord_1081823).sum := by decide
  have hdescent : baseEnd_1081823 < baseStart_1081823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081836 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_1081836 : Nat := 118140960795 + 1081836 * 2 ^ 59
def prefixEnd_1081836 : Nat := 4983230072969 + 3 ^ 40 * 1081836 * 2
def baseEnd_1081836 : Nat := 370334571558356363583155

theorem tailTrace_1081836 : CollatzResearch.WordTrace tailWord_1081836 prefixEnd_1081836 370334571558356363583155 := by
  unfold tailWord_1081836
  simp only [CollatzResearch.WordTrace]
  refine ⟨19728900254350204862092681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26305200339133606482790241 19728900254350204862092681)
  ·
    refine ⟨14796675190762653646569511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19728900254350204862092681 14796675190762653646569511)
    ·
      refine ⟨22195012786143980469854267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14796675190762653646569511 22195012786143980469854267)
      ·
        refine ⟨33292519179215970704781401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22195012786143980469854267 33292519179215970704781401)
        ·
          refine ⟨24969389384411978028586051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33292519179215970704781401 24969389384411978028586051)
          ·
            refine ⟨37454084076617967042879077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24969389384411978028586051 37454084076617967042879077)
            ·
              refine ⟨7022640764365868820539827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37454084076617967042879077 7022640764365868820539827)
              ·
                refine ⟨10533961146548803230809741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7022640764365868820539827 10533961146548803230809741)
                ·
                  refine ⟨3950235429955801211553653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10533961146548803230809741 3950235429955801211553653)
                  ·
                    refine ⟨370334571558356363583155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3950235429955801211553653 370334571558356363583155)
                    ·
                      rfl

theorem cell22_1081836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_1081836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081836 prefixEnd_1081836 := by exact prefixLift 1081836
  have htrace : WordTrace (prefixWord ++ tailWord_1081836) baseStart_1081836 baseEnd_1081836 := by
    simpa [prefixWord, tailWord_1081836, baseEnd_1081836] using wordTrace_append hprefix tailTrace_1081836
  have hstable : (prefixWord ++ tailWord_1081836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081836).length < 2 ^ (prefixWord ++ tailWord_1081836).sum := by decide
  have hdescent : baseEnd_1081836 < baseStart_1081836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081853 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_1081853 : Nat := 118140960795 + 1081853 * 2 ^ 59
def prefixEnd_1081853 : Nat := 4983230072969 + 3 ^ 40 * 1081853 * 2
def baseEnd_1081853 : Nat := 370340391005773985908103

theorem tailTrace_1081853 : CollatzResearch.WordTrace tailWord_1081853 prefixEnd_1081853 370340391005773985908103 := by
  unfold tailWord_1081853
  simp only [CollatzResearch.WordTrace]
  refine ⟨39458420549638821627554213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26305613699759214418369475 39458420549638821627554213)
  ·
    refine ⟨7398453853057279055166415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39458420549638821627554213 7398453853057279055166415)
    ·
      refine ⟨11097680779585918582749623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7398453853057279055166415 11097680779585918582749623)
      ·
        refine ⟨16646521169378877874124435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11097680779585918582749623 16646521169378877874124435)
        ·
          refine ⟨24969781754068316811186653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16646521169378877874124435 24969781754068316811186653)
          ·
            refine ⟨9363668157775618804194995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24969781754068316811186653 9363668157775618804194995)
            ·
              refine ⟨14045502236663428206292493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9363668157775618804194995 14045502236663428206292493)
              ·
                refine ⟨5267063338748785577359685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14045502236663428206292493 5267063338748785577359685)
                ·
                  refine ⟨987574376015397295754941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5267063338748785577359685 987574376015397295754941)
                  ·
                    refine ⟨370340391005773985908103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 987574376015397295754941 370340391005773985908103)
                    ·
                      rfl

theorem cell22_1081853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_1081853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081853 prefixEnd_1081853 := by exact prefixLift 1081853
  have htrace : WordTrace (prefixWord ++ tailWord_1081853) baseStart_1081853 baseEnd_1081853 := by
    simpa [prefixWord, tailWord_1081853, baseEnd_1081853] using wordTrace_append hprefix tailTrace_1081853
  have hstable : (prefixWord ++ tailWord_1081853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081853).length < 2 ^ (prefixWord ++ tailWord_1081853).sum := by decide
  have hdescent : baseEnd_1081853 < baseStart_1081853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081855 : List Nat := [1, 1, 2, 2, 1, 2, 7, 2, 4]
def baseStart_1081855 : Nat := 118140960795 + 1081855 * 2 ^ 59
def prefixEnd_1081855 : Nat := 4983230072969 + 3 ^ 40 * 1081855 * 2
def baseEnd_1081855 : Nat := 123447025215548882452699

theorem tailTrace_1081855 : CollatzResearch.WordTrace tailWord_1081855 prefixEnd_1081855 123447025215548882452699 := by
  unfold tailWord_1081855
  simp only [CollatzResearch.WordTrace]
  refine ⟨39458493495631575969127019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26305662330421050646084679 39458493495631575969127019)
  ·
    refine ⟨59187740243447363953690529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39458493495631575969127019 59187740243447363953690529)
    ·
      refine ⟨44390805182585522965267897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59187740243447363953690529 44390805182585522965267897)
      ·
        refine ⟨33293103886939142223950923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44390805182585522965267897 33293103886939142223950923)
        ·
          refine ⟨49939655830408713335926385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33293103886939142223950923 49939655830408713335926385)
          ·
            refine ⟨37454741872806535001944789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49939655830408713335926385 37454741872806535001944789)
            ·
              refine ⟨877845512643903164108081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37454741872806535001944789 877845512643903164108081)
              ·
                refine ⟨658384134482927373081061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877845512643903164108081 658384134482927373081061)
                ·
                  refine ⟨123447025215548882452699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658384134482927373081061 123447025215548882452699)
                  ·
                    rfl

theorem cell22_1081855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 4].length) (baseStart_1081855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081855 prefixEnd_1081855 := by exact prefixLift 1081855
  have htrace : WordTrace (prefixWord ++ tailWord_1081855) baseStart_1081855 baseEnd_1081855 := by
    simpa [prefixWord, tailWord_1081855, baseEnd_1081855] using wordTrace_append hprefix tailTrace_1081855
  have hstable : (prefixWord ++ tailWord_1081855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081855).length < 2 ^ (prefixWord ++ tailWord_1081855).sum := by decide
  have hdescent : baseEnd_1081855 < baseStart_1081855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081885 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1081885 : Nat := 118140960795 + 1081885 * 2 ^ 59
def prefixEnd_1081885 : Nat := 4983230072969 + 3 ^ 40 * 1081885 * 2
def baseEnd_1081885 : Nat := 370351345259736569108005

theorem tailTrace_1081885 : CollatzResearch.WordTrace tailWord_1081885 prefixEnd_1081885 370351345259736569108005 := by
  unfold tailWord_1081885
  simp only [CollatzResearch.WordTrace]
  refine ⟨39459587685522891092719109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26306391790348594061812739 39459587685522891092719109)
  ·
    refine ⟨7398672691035542079884833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39459587685522891092719109 7398672691035542079884833)
    ·
      refine ⟨5549004518276656559913625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7398672691035542079884833 5549004518276656559913625)
      ·
        refine ⟨4161753388707492419935219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5549004518276656559913625 4161753388707492419935219)
        ·
          refine ⟨6242630083061238629902829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161753388707492419935219 6242630083061238629902829)
          ·
            refine ⟨2340986281147964486213561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6242630083061238629902829 2340986281147964486213561)
            ·
              refine ⟨1755739710860973364660171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340986281147964486213561 1755739710860973364660171)
              ·
                refine ⟨2633609566291460046990257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755739710860973364660171 2633609566291460046990257)
                ·
                  refine ⟨1975207174718595035242693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633609566291460046990257 1975207174718595035242693)
                  ·
                    refine ⟨370351345259736569108005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975207174718595035242693 370351345259736569108005)
                    ·
                      rfl

theorem cell22_1081885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1081885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1081885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1081885 prefixEnd_1081885 := by exact prefixLift 1081885
  have htrace : WordTrace (prefixWord ++ tailWord_1081885) baseStart_1081885 baseEnd_1081885 := by
    simpa [prefixWord, tailWord_1081885, baseEnd_1081885] using wordTrace_append hprefix tailTrace_1081885
  have hstable : (prefixWord ++ tailWord_1081885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081885).length < 2 ^ (prefixWord ++ tailWord_1081885).sum := by decide
  have hdescent : baseEnd_1081885 < baseStart_1081885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082020 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1082020 : Nat := 118140960795 + 1082020 * 2 ^ 59
def prefixEnd_1082020 : Nat := 4983230072969 + 3 ^ 40 * 1082020 * 2
def baseEnd_1082020 : Nat := 370397558518641216982591

theorem tailTrace_1082020 : CollatzResearch.WordTrace tailWord_1082020 prefixEnd_1082020 370397558518641216982591 := by
  unfold tailWord_1082020
  simp only [CollatzResearch.WordTrace]
  refine ⟨19732255770016904574441757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26309674360022539432589009 19732255770016904574441757)
  ·
    refine ⟨7399595913756339215415659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19732255770016904574441757 7399595913756339215415659)
    ·
      refine ⟨11099393870634508823123489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7399595913756339215415659 11099393870634508823123489)
      ·
        refine ⟨8324545402975881617342617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11099393870634508823123489 8324545402975881617342617)
        ·
          refine ⟨6243409052231911213006963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8324545402975881617342617 6243409052231911213006963)
          ·
            refine ⟨9365113578347866819510445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243409052231911213006963 9365113578347866819510445)
            ·
              refine ⟨3511917591880450057316417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9365113578347866819510445 3511917591880450057316417)
              ·
                refine ⟨2633938193910337542987313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3511917591880450057316417 2633938193910337542987313)
                ·
                  refine ⟨1975453645432753157240485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633938193910337542987313 1975453645432753157240485)
                  ·
                    refine ⟨370397558518641216982591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975453645432753157240485 370397558518641216982591)
                    ·
                      rfl

theorem cell22_1082020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1082020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082020 prefixEnd_1082020 := by exact prefixLift 1082020
  have htrace : WordTrace (prefixWord ++ tailWord_1082020) baseStart_1082020 baseEnd_1082020 := by
    simpa [prefixWord, tailWord_1082020, baseEnd_1082020] using wordTrace_append hprefix tailTrace_1082020
  have hstable : (prefixWord ++ tailWord_1082020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082020).length < 2 ^ (prefixWord ++ tailWord_1082020).sum := by decide
  have hdescent : baseEnd_1082020 < baseStart_1082020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082084 : List Nat := [2, 3, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_1082084 : Nat := 118140960795 + 1082084 * 2 ^ 59
def prefixEnd_1082084 : Nat := 4983230072969 + 3 ^ 40 * 1082084 * 2
def baseEnd_1082084 : Nat := 370419467026566383382395

theorem tailTrace_1082084 : CollatzResearch.WordTrace tailWord_1082084 prefixEnd_1082084 370419467026566383382395 := by
  unfold tailWord_1082084
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733422905900974039606653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26311230541201298719475537 19733422905900974039606653)
  ·
    refine ⟨7400033589712865264852495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19733422905900974039606653 7400033589712865264852495)
    ·
      refine ⟨11100050384569297897278743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7400033589712865264852495 11100050384569297897278743)
      ·
        refine ⟨16650075576853946845918115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11100050384569297897278743 16650075576853946845918115)
        ·
          refine ⟨24975113365280920268877173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16650075576853946845918115 24975113365280920268877173)
          ·
            refine ⟨2341416877995086275207235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24975113365280920268877173 2341416877995086275207235)
            ·
              refine ⟨3512125316992629412810853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341416877995086275207235 3512125316992629412810853)
              ·
                refine ⟨658523496936118014902035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3512125316992629412810853 658523496936118014902035)
                ·
                  refine ⟨987785245404177022353053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658523496936118014902035 987785245404177022353053)
                  ·
                    refine ⟨370419467026566383382395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 987785245404177022353053 370419467026566383382395)
                    ·
                      rfl

theorem cell22_1082084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_1082084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082084 prefixEnd_1082084 := by exact prefixLift 1082084
  have htrace : WordTrace (prefixWord ++ tailWord_1082084) baseStart_1082084 baseEnd_1082084 := by
    simpa [prefixWord, tailWord_1082084, baseEnd_1082084] using wordTrace_append hprefix tailTrace_1082084
  have hstable : (prefixWord ++ tailWord_1082084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082084).length < 2 ^ (prefixWord ++ tailWord_1082084).sum := by decide
  have hdescent : baseEnd_1082084 < baseStart_1082084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082095 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 2, 5]
def baseStart_1082095 : Nat := 118140960795 + 1082095 * 2 ^ 59
def prefixEnd_1082095 : Nat := 4983230072969 + 3 ^ 40 * 1082095 * 2
def baseEnd_1082095 : Nat := 370423232551366021357361

theorem tailTrace_1082095 : CollatzResearch.WordTrace tailWord_1082095 prefixEnd_1082095 370423232551366021357361 := by
  unfold tailWord_1082095
  simp only [CollatzResearch.WordTrace]
  refine ⟨39467247014762096957863739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26311498009841397971909159 39467247014762096957863739)
  ·
    refine ⟨59200870522143145436795609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39467247014762096957863739 59200870522143145436795609)
    ·
      refine ⟨44400652891607359077596707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59200870522143145436795609 44400652891607359077596707)
      ·
        refine ⟨66600979337411038616395061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44400652891607359077596707 66600979337411038616395061)
        ·
          refine ⟨6243841812882284870287037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66600979337411038616395061 6243841812882284870287037)
          ·
            refine ⟨2341440679830856826357639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6243841812882284870287037 2341440679830856826357639)
            ·
              refine ⟨3512161019746285239536459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341440679830856826357639 3512161019746285239536459)
              ·
                refine ⟨5268241529619427859304689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512161019746285239536459 5268241529619427859304689)
                ·
                  refine ⟨3951181147214570894478517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5268241529619427859304689 3951181147214570894478517)
                  ·
                    refine ⟨370423232551366021357361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3951181147214570894478517 370423232551366021357361)
                    ·
                      rfl

theorem cell22_1082095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_1082095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082095 prefixEnd_1082095 := by exact prefixLift 1082095
  have htrace : WordTrace (prefixWord ++ tailWord_1082095) baseStart_1082095 baseEnd_1082095 := by
    simpa [prefixWord, tailWord_1082095, baseEnd_1082095] using wordTrace_append hprefix tailTrace_1082095
  have hstable : (prefixWord ++ tailWord_1082095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082095).length < 2 ^ (prefixWord ++ tailWord_1082095).sum := by decide
  have hdescent : baseEnd_1082095 < baseStart_1082095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082296 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 1, 4]
def baseStart_1082296 : Nat := 118140960795 + 1082296 * 2 ^ 59
def prefixEnd_1082296 : Nat := 4983230072969 + 3 ^ 40 * 1082296 * 2
def baseEnd_1082296 : Nat := 370492038959068497081745

theorem tailTrace_1082296 : CollatzResearch.WordTrace tailWord_1082296 prefixEnd_1082296 370492038959068497081745 := by
  unfold tailWord_1082296
  simp only [CollatzResearch.WordTrace]
  refine ⟨19737289043516954142965371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26316385391355938857287161 19737289043516954142965371)
  ·
    refine ⟨29605933565275431214448057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19737289043516954142965371 29605933565275431214448057)
    ·
      refine ⟨22204450173956573410836043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29605933565275431214448057 22204450173956573410836043)
      ·
        refine ⟨33306675260934860116254065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22204450173956573410836043 33306675260934860116254065)
        ·
          refine ⟨24980006445701145087190549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33306675260934860116254065 24980006445701145087190549)
          ·
            refine ⟨1170937802142241175962057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24980006445701145087190549 1170937802142241175962057)
            ·
              refine ⟨878203351606680881971543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170937802142241175962057 878203351606680881971543)
              ·
                refine ⟨1317305027410021322957315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878203351606680881971543 1317305027410021322957315)
                ·
                  refine ⟨1975957541115031984435973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317305027410021322957315 1975957541115031984435973)
                  ·
                    refine ⟨370492038959068497081745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975957541115031984435973 370492038959068497081745)
                    ·
                      rfl

theorem cell22_1082296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_1082296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082296 prefixEnd_1082296 := by exact prefixLift 1082296
  have htrace : WordTrace (prefixWord ++ tailWord_1082296) baseStart_1082296 baseEnd_1082296 := by
    simpa [prefixWord, tailWord_1082296, baseEnd_1082296] using wordTrace_append hprefix tailTrace_1082296
  have hstable : (prefixWord ++ tailWord_1082296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082296).length < 2 ^ (prefixWord ++ tailWord_1082296).sum := by decide
  have hdescent : baseEnd_1082296 < baseStart_1082296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082326 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1082326 : Nat := 118140960795 + 1082326 * 2 ^ 59
def prefixEnd_1082326 : Nat := 4983230072969 + 3 ^ 40 * 1082326 * 2
def baseEnd_1082326 : Nat := 370502308572158418831653

theorem tailTrace_1082326 : CollatzResearch.WordTrace tailWord_1082326 prefixEnd_1082326 370502308572158418831653 := by
  unfold tailWord_1082326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467229517307826463095177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26317114851283482273015221 2467229517307826463095177)
  ·
    refine ⟨1850422137980869847321383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2467229517307826463095177 1850422137980869847321383)
    ·
      refine ⟨2775633206971304770982075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850422137980869847321383 2775633206971304770982075)
      ·
        refine ⟨4163449810456957156473113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775633206971304770982075 4163449810456957156473113)
        ·
          refine ⟨3122587357842717867354835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4163449810456957156473113 3122587357842717867354835)
          ·
            refine ⟨4683881036764076801032253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122587357842717867354835 4683881036764076801032253)
            ·
              refine ⟨1756455388786528800387095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4683881036764076801032253 1756455388786528800387095)
              ·
                refine ⟨2634683083179793200580643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756455388786528800387095 2634683083179793200580643)
                ·
                  refine ⟨3952024624769689800870965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634683083179793200580643 3952024624769689800870965)
                  ·
                    refine ⟨370502308572158418831653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3952024624769689800870965 370502308572158418831653)
                    ·
                      rfl

theorem cell22_1082326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1082326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082326 prefixEnd_1082326 := by exact prefixLift 1082326
  have htrace : WordTrace (prefixWord ++ tailWord_1082326) baseStart_1082326 baseEnd_1082326 := by
    simpa [prefixWord, tailWord_1082326, baseEnd_1082326] using wordTrace_append hprefix tailTrace_1082326
  have hstable : (prefixWord ++ tailWord_1082326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082326).length < 2 ^ (prefixWord ++ tailWord_1082326).sum := by decide
  have hdescent : baseEnd_1082326 < baseStart_1082326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082422 : List Nat := [5, 1, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1082422 : Nat := 118140960795 + 1082422 * 2 ^ 59
def prefixEnd_1082422 : Nat := 4983230072969 + 3 ^ 40 * 1082422 * 2
def baseEnd_1082422 : Nat := 370535171334046168431359

theorem tailTrace_1082422 : CollatzResearch.WordTrace tailWord_1082422 prefixEnd_1082422 370535171334046168431359 := by
  unfold tailWord_1082422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467448355286089487813595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26319449123051621203345013 2467448355286089487813595)
  ·
    refine ⟨3701172532929134231720393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2467448355286089487813595 3701172532929134231720393)
    ·
      refine ⟨2775879399696850673790295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3701172532929134231720393 2775879399696850673790295)
      ·
        refine ⟨4163819099545276010685443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775879399696850673790295 4163819099545276010685443)
        ·
          refine ⟨6245728649317914016028165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163819099545276010685443 6245728649317914016028165)
          ·
            refine ⟨1171074121747108878005281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6245728649317914016028165 1171074121747108878005281)
            ·
              refine ⟨878305591310331658503961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171074121747108878005281 878305591310331658503961)
              ·
                refine ⟨658729193482748743877971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878305591310331658503961 658729193482748743877971)
                ·
                  refine ⟨988093790224123115816957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658729193482748743877971 988093790224123115816957)
                  ·
                    refine ⟨370535171334046168431359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988093790224123115816957 370535171334046168431359)
                    ·
                      rfl

theorem cell22_1082422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1082422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082422 prefixEnd_1082422 := by exact prefixLift 1082422
  have htrace : WordTrace (prefixWord ++ tailWord_1082422) baseStart_1082422 baseEnd_1082422 := by
    simpa [prefixWord, tailWord_1082422, baseEnd_1082422] using wordTrace_append hprefix tailTrace_1082422
  have hstable : (prefixWord ++ tailWord_1082422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082422).length < 2 ^ (prefixWord ++ tailWord_1082422).sum := by decide
  have hdescent : baseEnd_1082422 < baseStart_1082422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082444 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_1082444 : Nat := 118140960795 + 1082444 * 2 ^ 59
def prefixEnd_1082444 : Nat := 4983230072969 + 3 ^ 40 * 1082444 * 2
def baseEnd_1082444 : Nat := 370542702383645444381291

theorem tailTrace_1082444 : CollatzResearch.WordTrace tailWord_1082444 prefixEnd_1082444 370542702383645444381291 := by
  unfold tailWord_1082444
  simp only [CollatzResearch.WordTrace]
  refine ⟨19739988045248864781159193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26319984060331819708212257 19739988045248864781159193)
  ·
    refine ⟨14804991033936648585869395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19739988045248864781159193 14804991033936648585869395)
    ·
      refine ⟨22207486550904972878804093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14804991033936648585869395 22207486550904972878804093)
      ·
        refine ⟨8327807456589364829551535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22207486550904972878804093 8327807456589364829551535)
        ·
          refine ⟨12491711184884047244327303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8327807456589364829551535 12491711184884047244327303)
          ·
            refine ⟨18737566777326070866490955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12491711184884047244327303 18737566777326070866490955)
            ·
              refine ⟨28106350165989106299736433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18737566777326070866490955 28106350165989106299736433)
              ·
                refine ⟨21079762624491829724802325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28106350165989106299736433 21079762624491829724802325)
                ·
                  refine ⟨988113873023054518350109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21079762624491829724802325 988113873023054518350109)
                  ·
                    refine ⟨370542702383645444381291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988113873023054518350109 370542702383645444381291)
                    ·
                      rfl

theorem cell22_1082444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_1082444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082444 prefixEnd_1082444 := by exact prefixLift 1082444
  have htrace : WordTrace (prefixWord ++ tailWord_1082444) baseStart_1082444 baseEnd_1082444 := by
    simpa [prefixWord, tailWord_1082444, baseEnd_1082444] using wordTrace_append hprefix tailTrace_1082444
  have hstable : (prefixWord ++ tailWord_1082444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082444).length < 2 ^ (prefixWord ++ tailWord_1082444).sum := by decide
  have hdescent : baseEnd_1082444 < baseStart_1082444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082474 : List Nat := [3, 1, 3, 2, 2, 2, 9]
def baseStart_1082474 : Nat := 118140960795 + 1082474 * 2 ^ 59
def prefixEnd_1082474 : Nat := 4983230072969 + 3 ^ 40 * 1082474 * 2
def baseEnd_1082474 : Nat := 13724184148027235782637

theorem tailTrace_1082474 : CollatzResearch.WordTrace tailWord_1082474 prefixEnd_1082474 13724184148027235782637 := by
  unfold tailWord_1082474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9870267570097261171477619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26320713520259363123940317 9870267570097261171477619)
  ·
    refine ⟨14805401355145891757216429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9870267570097261171477619 14805401355145891757216429)
    ·
      refine ⟨5552025508179709408956161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14805401355145891757216429 5552025508179709408956161)
      ·
        refine ⟨4164019131134782056717121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5552025508179709408956161 4164019131134782056717121)
        ·
          refine ⟨3123014348351086542537841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4164019131134782056717121 3123014348351086542537841)
          ·
            refine ⟨2342260761263314906903381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3123014348351086542537841 2342260761263314906903381)
            ·
              refine ⟨13724184148027235782637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2342260761263314906903381 13724184148027235782637)
              ·
                rfl

theorem cell22_1082474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 9].length) (baseStart_1082474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082474 prefixEnd_1082474 := by exact prefixLift 1082474
  have htrace : WordTrace (prefixWord ++ tailWord_1082474) baseStart_1082474 baseEnd_1082474 := by
    simpa [prefixWord, tailWord_1082474, baseEnd_1082474] using wordTrace_append hprefix tailTrace_1082474
  have hstable : (prefixWord ++ tailWord_1082474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082474).length < 2 ^ (prefixWord ++ tailWord_1082474).sum := by decide
  have hdescent : baseEnd_1082474 < baseStart_1082474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082478 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_1082478 : Nat := 118140960795 + 1082478 * 2 ^ 59
def prefixEnd_1082478 : Nat := 4983230072969 + 3 ^ 40 * 1082478 * 2
def baseEnd_1082478 : Nat := 370554341278480689031187

theorem tailTrace_1082478 : CollatzResearch.WordTrace tailWord_1082478 prefixEnd_1082478 370554341278480689031187 := by
  unfold tailWord_1082478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935152021546819171132011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26320810781583035579370725 4935152021546819171132011)
  ·
    refine ⟨7402728032320228756698017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4935152021546819171132011 7402728032320228756698017)
    ·
      refine ⟨5552046024240171567523513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7402728032320228756698017 5552046024240171567523513)
      ·
        refine ⟨4164034518180128675642635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5552046024240171567523513 4164034518180128675642635)
        ·
          refine ⟨6246051777270193013463953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164034518180128675642635 6246051777270193013463953)
          ·
            refine ⟨4684538832952644760097965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6246051777270193013463953 4684538832952644760097965)
            ·
              refine ⟨1756702062357241785036737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4684538832952644760097965 1756702062357241785036737)
              ·
                refine ⟨1317526546767931338777553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1756702062357241785036737 1317526546767931338777553)
                ·
                  refine ⟨988144910075948504083165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1317526546767931338777553 988144910075948504083165)
                  ·
                    refine ⟨370554341278480689031187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988144910075948504083165 370554341278480689031187)
                    ·
                      rfl

theorem cell22_1082478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_1082478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082478 prefixEnd_1082478 := by exact prefixLift 1082478
  have htrace : WordTrace (prefixWord ++ tailWord_1082478) baseStart_1082478 baseEnd_1082478 := by
    simpa [prefixWord, tailWord_1082478, baseEnd_1082478] using wordTrace_append hprefix tailTrace_1082478
  have hstable : (prefixWord ++ tailWord_1082478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082478).length < 2 ^ (prefixWord ++ tailWord_1082478).sum := by decide
  have hdescent : baseEnd_1082478 < baseStart_1082478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082506 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_1082506 : Nat := 118140960795 + 1082506 * 2 ^ 59
def prefixEnd_1082506 : Nat := 4983230072969 + 3 ^ 40 * 1082506 * 2
def baseEnd_1082506 : Nat := 370563926250697949331101

theorem tailTrace_1082506 : CollatzResearch.WordTrace tailWord_1082506 prefixEnd_1082506 370563926250697949331101 := by
  unfold tailWord_1082506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9870559354068278537768843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26321491610848742767383581 9870559354068278537768843)
  ·
    refine ⟨14805839031102417806653265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9870559354068278537768843 14805839031102417806653265)
    ·
      refine ⟨11104379273326813354989949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14805839031102417806653265 11104379273326813354989949)
      ·
        refine ⟨4164142227497555008121231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11104379273326813354989949 4164142227497555008121231)
        ·
          refine ⟨6246213341246332512181847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164142227497555008121231 6246213341246332512181847)
          ·
            refine ⟨9369320011869498768272771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246213341246332512181847 9369320011869498768272771)
            ·
              refine ⟨14053980017804248152409157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9369320011869498768272771 14053980017804248152409157)
              ·
                refine ⟨2635121253338296528576717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14053980017804248152409157 2635121253338296528576717)
                ·
                  refine ⟨988170470001861198216269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2635121253338296528576717 988170470001861198216269)
                  ·
                    refine ⟨370563926250697949331101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988170470001861198216269 370563926250697949331101)
                    ·
                      rfl

theorem cell22_1082506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_1082506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082506 prefixEnd_1082506 := by exact prefixLift 1082506
  have htrace : WordTrace (prefixWord ++ tailWord_1082506) baseStart_1082506 baseEnd_1082506 := by
    simpa [prefixWord, tailWord_1082506, baseEnd_1082506] using wordTrace_append hprefix tailTrace_1082506
  have hstable : (prefixWord ++ tailWord_1082506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082506).length < 2 ^ (prefixWord ++ tailWord_1082506).sum := by decide
  have hdescent : baseEnd_1082506 < baseStart_1082506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082519 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 7]
def baseStart_1082519 : Nat := 118140960795 + 1082519 * 2 ^ 59
def prefixEnd_1082519 : Nat := 4983230072969 + 3 ^ 40 * 1082519 * 2
def baseEnd_1082519 : Nat := 123522792138790082918687

theorem tailTrace_1082519 : CollatzResearch.WordTrace tailWord_1082519 prefixEnd_1082519 123522792138790082918687 := by
  unfold tailWord_1082519
  simp only [CollatzResearch.WordTrace]
  refine ⟨39482711565226017371298611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26321807710150678247532407 39482711565226017371298611)
  ·
    refine ⟨59224067347839026056947917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39482711565226017371298611 59224067347839026056947917)
    ·
      refine ⟨22209025255439634771355469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59224067347839026056947917 22209025255439634771355469)
      ·
        refine ⟨8328384470789863039258301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22209025255439634771355469 8328384470789863039258301)
        ·
          refine ⟨3123144176546198639721863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8328384470789863039258301 3123144176546198639721863)
          ·
            refine ⟨4684716264819297959582795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123144176546198639721863 4684716264819297959582795)
            ·
              refine ⟨7027074397228946939374193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684716264819297959582795 7027074397228946939374193)
              ·
                refine ⟨5270305797921710204530645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7027074397228946939374193 5270305797921710204530645)
                ·
                  refine ⟨123522792138790082918687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5270305797921710204530645 123522792138790082918687)
                  ·
                    rfl

theorem cell22_1082519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 7].length) (baseStart_1082519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082519 prefixEnd_1082519 := by exact prefixLift 1082519
  have htrace : WordTrace (prefixWord ++ tailWord_1082519) baseStart_1082519 baseEnd_1082519 := by
    simpa [prefixWord, tailWord_1082519, baseEnd_1082519] using wordTrace_append hprefix tailTrace_1082519
  have hstable : (prefixWord ++ tailWord_1082519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082519).length < 2 ^ (prefixWord ++ tailWord_1082519).sum := by decide
  have hdescent : baseEnd_1082519 < baseStart_1082519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082553 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 5]
def baseStart_1082553 : Nat := 118140960795 + 1082553 * 2 ^ 59
def prefixEnd_1082553 : Nat := 4983230072969 + 3 ^ 40 * 1082553 * 2
def baseEnd_1082553 : Nat := 123526671770401831135319

theorem tailTrace_1082553 : CollatzResearch.WordTrace tailWord_1082553 prefixEnd_1082553 123526671770401831135319 := by
  unfold tailWord_1082553
  simp only [CollatzResearch.WordTrace]
  refine ⟨39483951647102841178036313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26322634431401894118690875 39483951647102841178036313)
  ·
    refine ⟨29612963735327130883527235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39483951647102841178036313 29612963735327130883527235)
    ·
      refine ⟨44419445602990696325290853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29612963735327130883527235 44419445602990696325290853)
      ·
        refine ⟨8328646050560755560992035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44419445602990696325290853 8328646050560755560992035)
        ·
          refine ⟨12492969075841133341488053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8328646050560755560992035 12492969075841133341488053)
          ·
            refine ⟨1171215850860106250764505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12492969075841133341488053 1171215850860106250764505)
            ·
              refine ⟨878411888145079688073379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171215850860106250764505 878411888145079688073379)
              ·
                refine ⟨1317617832217619532110069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878411888145079688073379 1317617832217619532110069)
                ·
                  refine ⟨123526671770401831135319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1317617832217619532110069 123526671770401831135319)
                  ·
                    rfl

theorem cell22_1082553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_1082553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082553 prefixEnd_1082553 := by exact prefixLift 1082553
  have htrace : WordTrace (prefixWord ++ tailWord_1082553) baseStart_1082553 baseEnd_1082553 := by
    simpa [prefixWord, tailWord_1082553, baseEnd_1082553] using wordTrace_append hprefix tailTrace_1082553
  have hstable : (prefixWord ++ tailWord_1082553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082553).length < 2 ^ (prefixWord ++ tailWord_1082553).sum := by decide
  have hdescent : baseEnd_1082553 < baseStart_1082553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082579 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 1, 5]
def baseStart_1082579 : Nat := 118140960795 + 1082579 * 2 ^ 59
def prefixEnd_1082579 : Nat := 4983230072969 + 3 ^ 40 * 1082579 * 2
def baseEnd_1082579 : Nat := 370588915642550092255877

theorem tailTrace_1082579 : CollatzResearch.WordTrace tailWord_1082579 prefixEnd_1082579 370588915642550092255877 := by
  unfold tailWord_1082579
  simp only [CollatzResearch.WordTrace]
  refine ⟨39484899945008647618482791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26323266630005765078988527 39484899945008647618482791)
  ·
    refine ⟨59227349917512971427724187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39484899945008647618482791 59227349917512971427724187)
    ·
      refine ⟨88841024876269457141586281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59227349917512971427724187 88841024876269457141586281)
      ·
        refine ⟨66630768657202092856189711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88841024876269457141586281 66630768657202092856189711)
        ·
          refine ⟨99946152985803139284284567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66630768657202092856189711 99946152985803139284284567)
          ·
            refine ⟨149919229478704708926426851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99946152985803139284284567 149919229478704708926426851)
            ·
              refine ⟨224878844218057063389640277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149919229478704708926426851 224878844218057063389640277)
              ·
                refine ⟨2635298955680356211597347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 224878844218057063389640277 2635298955680356211597347)
                ·
                  refine ⟨3952948433520534317396021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635298955680356211597347 3952948433520534317396021)
                  ·
                    refine ⟨370588915642550092255877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3952948433520534317396021 370588915642550092255877)
                    ·
                      rfl

theorem cell22_1082579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_1082579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082579 prefixEnd_1082579 := by exact prefixLift 1082579
  have htrace : WordTrace (prefixWord ++ tailWord_1082579) baseStart_1082579 baseEnd_1082579 := by
    simpa [prefixWord, tailWord_1082579, baseEnd_1082579] using wordTrace_append hprefix tailTrace_1082579
  have hstable : (prefixWord ++ tailWord_1082579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082579).length < 2 ^ (prefixWord ++ tailWord_1082579).sum := by decide
  have hdescent : baseEnd_1082579 < baseStart_1082579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082596 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_1082596 : Nat := 118140960795 + 1082596 * 2 ^ 59
def prefixEnd_1082596 : Nat := 4983230072969 + 3 ^ 40 * 1082596 * 2
def baseEnd_1082596 : Nat := 370594735089967714580825

theorem tailTrace_1082596 : CollatzResearch.WordTrace tailWord_1082596 prefixEnd_1082596 370594735089967714580825 := by
  unfold tailWord_1082596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19742759992973529760925821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26323679990631373014567761 19742759992973529760925821)
  ·
    refine ⟨7403534997365073660347183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19742759992973529760925821 7403534997365073660347183)
    ·
      refine ⟨11105302496047610490520775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7403534997365073660347183 11105302496047610490520775)
      ·
        refine ⟨16657953744071415735781163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11105302496047610490520775 16657953744071415735781163)
        ·
          refine ⟨24986930616107123603671745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16657953744071415735781163 24986930616107123603671745)
          ·
            refine ⟨18740197962080342702753809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24986930616107123603671745 18740197962080342702753809)
            ·
              refine ⟨14055148471560257027065357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18740197962080342702753809 14055148471560257027065357)
              ·
                refine ⟨5270680676835096385149509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14055148471560257027065357 5270680676835096385149509)
                ·
                  refine ⟨988252626906580572215533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5270680676835096385149509 988252626906580572215533)
                  ·
                    refine ⟨370594735089967714580825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988252626906580572215533 370594735089967714580825)
                    ·
                      rfl

theorem cell22_1082596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_1082596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082596 prefixEnd_1082596 := by exact prefixLift 1082596
  have htrace : WordTrace (prefixWord ++ tailWord_1082596) baseStart_1082596 baseEnd_1082596 := by
    simpa [prefixWord, tailWord_1082596, baseEnd_1082596] using wordTrace_append hprefix tailTrace_1082596
  have hstable : (prefixWord ++ tailWord_1082596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082596).length < 2 ^ (prefixWord ++ tailWord_1082596).sum := by decide
  have hdescent : baseEnd_1082596 < baseStart_1082596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082628 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1082628 : Nat := 118140960795 + 1082628 * 2 ^ 59
def prefixEnd_1082628 : Nat := 4983230072969 + 3 ^ 40 * 1082628 * 2
def baseEnd_1082628 : Nat := 370605689343930297780727

theorem tailTrace_1082628 : CollatzResearch.WordTrace tailWord_1082628 prefixEnd_1082628 370605689343930297780727 := by
  unfold tailWord_1082628
  simp only [CollatzResearch.WordTrace]
  refine ⟨19743343560915564493508269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26324458081220752658011025 19743343560915564493508269)
  ·
    refine ⟨7403753835343336685065601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19743343560915564493508269 7403753835343336685065601)
    ·
      refine ⟨5552815376507502513799201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7403753835343336685065601 5552815376507502513799201)
      ·
        refine ⟨4164611532380626885349401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5552815376507502513799201 4164611532380626885349401)
        ·
          refine ⟨3123458649285470164012051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4164611532380626885349401 3123458649285470164012051)
          ·
            refine ⟨4685187973928205246018077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123458649285470164012051 4685187973928205246018077)
            ·
              refine ⟨1756945490223076967256779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4685187973928205246018077 1756945490223076967256779)
              ·
                refine ⟨2635418235334615450885169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756945490223076967256779 2635418235334615450885169)
                ·
                  refine ⟨1976563676500961588163877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635418235334615450885169 1976563676500961588163877)
                  ·
                    refine ⟨370605689343930297780727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976563676500961588163877 370605689343930297780727)
                    ·
                      rfl

theorem cell22_1082628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1082628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082628 prefixEnd_1082628 := by exact prefixLift 1082628
  have htrace : WordTrace (prefixWord ++ tailWord_1082628) baseStart_1082628 baseEnd_1082628 := by
    simpa [prefixWord, tailWord_1082628, baseEnd_1082628] using wordTrace_append hprefix tailTrace_1082628
  have hstable : (prefixWord ++ tailWord_1082628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082628).length < 2 ^ (prefixWord ++ tailWord_1082628).sum := by decide
  have hdescent : baseEnd_1082628 < baseStart_1082628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082641 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 5, 3]
def baseStart_1082641 : Nat := 118140960795 + 1082641 * 2 ^ 59
def prefixEnd_1082641 : Nat := 4983230072969 + 3 ^ 40 * 1082641 * 2
def baseEnd_1082641 : Nat := 370610139509602597205687

theorem tailTrace_1082641 : CollatzResearch.WordTrace tailWord_1082641 prefixEnd_1082641 370610139509602597205687 := by
  unfold tailWord_1082641
  simp only [CollatzResearch.WordTrace]
  refine ⟨39487161270784032207239777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26324774180522688138159851 39487161270784032207239777)
  ·
    refine ⟨29615370953088024155429833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39487161270784032207239777 29615370953088024155429833)
    ·
      refine ⟨22211528214816018116572375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29615370953088024155429833 22211528214816018116572375)
      ·
        refine ⟨33317292322224027174858563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22211528214816018116572375 33317292322224027174858563)
        ·
          refine ⟨49975938483336040762287845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33317292322224027174858563 49975938483336040762287845)
          ·
            refine ⟨9370488465625507642928971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49975938483336040762287845 9370488465625507642928971)
            ·
              refine ⟨14055732698438261464393457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9370488465625507642928971 14055732698438261464393457)
              ·
                refine ⟨10541799523828696098295093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14055732698438261464393457 10541799523828696098295093)
                ·
                  refine ⟨988293705358940259215165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10541799523828696098295093 988293705358940259215165)
                  ·
                    refine ⟨370610139509602597205687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988293705358940259215165 370610139509602597205687)
                    ·
                      rfl

theorem cell22_1082641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_1082641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082641 prefixEnd_1082641 := by exact prefixLift 1082641
  have htrace : WordTrace (prefixWord ++ tailWord_1082641) baseStart_1082641 baseEnd_1082641 := by
    simpa [prefixWord, tailWord_1082641, baseEnd_1082641] using wordTrace_append hprefix tailTrace_1082641
  have hstable : (prefixWord ++ tailWord_1082641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082641).length < 2 ^ (prefixWord ++ tailWord_1082641).sum := by decide
  have hdescent : baseEnd_1082641 < baseStart_1082641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082746 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_1082746 : Nat := 118140960795 + 1082746 * 2 ^ 59
def prefixEnd_1082746 : Nat := 4983230072969 + 3 ^ 40 * 1082746 * 2
def baseEnd_1082746 : Nat := 370646083155417323330365

theorem tailTrace_1082746 : CollatzResearch.WordTrace tailWord_1082746 prefixEnd_1082746 370646083155417323330365 := by
  unfold tailWord_1082746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9872747733850908784953023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26327327290269090093208061 9872747733850908784953023)
  ·
    refine ⟨14809121600776363177429535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9872747733850908784953023 14809121600776363177429535)
    ·
      refine ⟨22213682401164544766144303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14809121600776363177429535 22213682401164544766144303)
      ·
        refine ⟨33320523601746817149216455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22213682401164544766144303 33320523601746817149216455)
        ·
          refine ⟨49980785402620225723824683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33320523601746817149216455 49980785402620225723824683)
          ·
            refine ⟨74971178103930338585737025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49980785402620225723824683 74971178103930338585737025)
            ·
              refine ⟨56228383577947753939302769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74971178103930338585737025 56228383577947753939302769)
              ·
                refine ⟨42171287683460815454477077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56228383577947753939302769 42171287683460815454477077)
                ·
                  refine ⟨1976779110162225724428613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42171287683460815454477077 1976779110162225724428613)
                  ·
                    refine ⟨370646083155417323330365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976779110162225724428613 370646083155417323330365)
                    ·
                      rfl

theorem cell22_1082746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_1082746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082746 prefixEnd_1082746 := by exact prefixLift 1082746
  have htrace : WordTrace (prefixWord ++ tailWord_1082746) baseStart_1082746 baseEnd_1082746 := by
    simpa [prefixWord, tailWord_1082746, baseEnd_1082746] using wordTrace_append hprefix tailTrace_1082746
  have hstable : (prefixWord ++ tailWord_1082746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082746).length < 2 ^ (prefixWord ++ tailWord_1082746).sum := by decide
  have hdescent : baseEnd_1082746 < baseStart_1082746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082761 : List Nat := [1, 2, 1, 1, 7, 10]
def baseStart_1082761 : Nat := 118140960795 + 1082761 * 2 ^ 59
def prefixEnd_1082761 : Nat := 4983230072969 + 3 ^ 40 * 1082761 * 2
def baseEnd_1082761 : Nat := 4575940962493361533399

theorem tailTrace_1082761 : CollatzResearch.WordTrace tailWord_1082761 prefixEnd_1082761 4575940962493361533399 := by
  unfold tailWord_1082761
  simp only [CollatzResearch.WordTrace]
  refine ⟨39491538030349292701608137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26327692020232861801072091 39491538030349292701608137)
  ·
    refine ⟨29618653522761969526206103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39491538030349292701608137 29618653522761969526206103)
    ·
      refine ⟨44427980284142954289309155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29618653522761969526206103 44427980284142954289309155)
      ·
        refine ⟨66641970426214431433963733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44427980284142954289309155 66641970426214431433963733)
        ·
          refine ⟨1561921181864400736733525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66641970426214431433963733 1561921181864400736733525)
          ·
            refine ⟨4575940962493361533399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1561921181864400736733525 4575940962493361533399)
            ·
              rfl

theorem cell22_1082761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 10].length) (baseStart_1082761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082761 prefixEnd_1082761 := by exact prefixLift 1082761
  have htrace : WordTrace (prefixWord ++ tailWord_1082761) baseStart_1082761 baseEnd_1082761 := by
    simpa [prefixWord, tailWord_1082761, baseEnd_1082761] using wordTrace_append hprefix tailTrace_1082761
  have hstable : (prefixWord ++ tailWord_1082761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082761).length < 2 ^ (prefixWord ++ tailWord_1082761).sum := by decide
  have hdescent : baseEnd_1082761 < baseStart_1082761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082782 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1082782 : Nat := 118140960795 + 1082782 * 2 ^ 59
def prefixEnd_1082782 : Nat := 4983230072969 + 3 ^ 40 * 1082782 * 2
def baseEnd_1082782 : Nat := 370658406691125229430255

theorem tailTrace_1082782 : CollatzResearch.WordTrace tailWord_1082782 prefixEnd_1082782 370658406691125229430255 := by
  unfold tailWord_1082782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936537995409151661015325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26328202642182142192081733 4936537995409151661015325)
  ·
    refine ⟨1851201748278431872880747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4936537995409151661015325 1851201748278431872880747)
    ·
      refine ⟨2776802622417647809321121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851201748278431872880747 2776802622417647809321121)
      ·
        refine ⟨2082601966813235856990841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2776802622417647809321121 2082601966813235856990841)
        ·
          refine ⟨1561951475109926892743131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2082601966813235856990841 1561951475109926892743131)
          ·
            refine ⟨2342927212664890339114697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561951475109926892743131 2342927212664890339114697)
            ·
              refine ⟨1757195409498667754336023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2342927212664890339114697 1757195409498667754336023)
              ·
                refine ⟨2635793114248001631504035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757195409498667754336023 2635793114248001631504035)
                ·
                  refine ⟨3953689671372002447256053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635793114248001631504035 3953689671372002447256053)
                  ·
                    refine ⟨370658406691125229430255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3953689671372002447256053 370658406691125229430255)
                    ·
                      rfl

theorem cell22_1082782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1082782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082782 prefixEnd_1082782 := by exact prefixLift 1082782
  have htrace : WordTrace (prefixWord ++ tailWord_1082782) baseStart_1082782 baseEnd_1082782 := by
    simpa [prefixWord, tailWord_1082782, baseEnd_1082782] using wordTrace_append hprefix tailTrace_1082782
  have hstable : (prefixWord ++ tailWord_1082782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082782).length < 2 ^ (prefixWord ++ tailWord_1082782).sum := by decide
  have hdescent : baseEnd_1082782 < baseStart_1082782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082797 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1082797 : Nat := 118140960795 + 1082797 * 2 ^ 59
def prefixEnd_1082797 : Nat := 4983230072969 + 3 ^ 40 * 1082797 * 2
def baseEnd_1082797 : Nat := 370663541497670190305209

theorem tailTrace_1082797 : CollatzResearch.WordTrace tailWord_1082797 prefixEnd_1082797 370663541497670190305209 := by
  unfold tailWord_1082797
  simp only [CollatzResearch.WordTrace]
  refine ⟨39492851058218870849918645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26328567372145913899945763 39492851058218870849918645)
  ·
    refine ⟨3702454786708019142179873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39492851058218870849918645 3702454786708019142179873)
    ·
      refine ⟨2776841090031014356634905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3702454786708019142179873 2776841090031014356634905)
      ·
        refine ⟨2082630817523260767476179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2776841090031014356634905 2082630817523260767476179)
        ·
          refine ⟨3123946226284891151214269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082630817523260767476179 3123946226284891151214269)
          ·
            refine ⟨1171479834856834181705351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3123946226284891151214269 1171479834856834181705351)
            ·
              refine ⟨1757219752285251272558027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171479834856834181705351 1757219752285251272558027)
              ·
                refine ⟨2635829628427876908837041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757219752285251272558027 2635829628427876908837041)
                ·
                  refine ⟨1976872221320907681627781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635829628427876908837041 1976872221320907681627781)
                  ·
                    refine ⟨370663541497670190305209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976872221320907681627781 370663541497670190305209)
                    ·
                      rfl

theorem cell22_1082797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1082797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082797 prefixEnd_1082797 := by exact prefixLift 1082797
  have htrace : WordTrace (prefixWord ++ tailWord_1082797) baseStart_1082797 baseEnd_1082797 := by
    simpa [prefixWord, tailWord_1082797, baseEnd_1082797] using wordTrace_append hprefix tailTrace_1082797
  have hstable : (prefixWord ++ tailWord_1082797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082797).length < 2 ^ (prefixWord ++ tailWord_1082797).sum := by decide
  have hdescent : baseEnd_1082797 < baseStart_1082797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082861 : List Nat := [1, 5, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_1082861 : Nat := 118140960795 + 1082861 * 2 ^ 59
def prefixEnd_1082861 : Nat := 4983230072969 + 3 ^ 40 * 1082861 * 2
def baseEnd_1082861 : Nat := 370685450005595356705013

theorem tailTrace_1082861 : CollatzResearch.WordTrace tailWord_1082861 prefixEnd_1082861 370685450005595356705013 := by
  unfold tailWord_1082861
  simp only [CollatzResearch.WordTrace]
  refine ⟨39495185329987009780248437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26330123553324673186832291 39495185329987009780248437)
  ·
    refine ⟨3702673624686282166898291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39495185329987009780248437 3702673624686282166898291)
    ·
      refine ⟨5554010437029423250347437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3702673624686282166898291 5554010437029423250347437)
      ·
        refine ⟨2082753913886033718880289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5554010437029423250347437 2082753913886033718880289)
        ·
          refine ⟨1562065435414525289160217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2082753913886033718880289 1562065435414525289160217)
          ·
            refine ⟨1171549076560893966870163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562065435414525289160217 1171549076560893966870163)
            ·
              refine ⟨1757323614841340950305245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171549076560893966870163 1757323614841340950305245)
              ·
                refine ⟨658996355565502856364467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1757323614841340950305245 658996355565502856364467)
                ·
                  refine ⟨988494533348254284546701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658996355565502856364467 988494533348254284546701)
                  ·
                    refine ⟨370685450005595356705013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988494533348254284546701 370685450005595356705013)
                    ·
                      rfl

theorem cell22_1082861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_1082861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082861 prefixEnd_1082861 := by exact prefixLift 1082861
  have htrace : WordTrace (prefixWord ++ tailWord_1082861) baseStart_1082861 baseEnd_1082861 := by
    simpa [prefixWord, tailWord_1082861, baseEnd_1082861] using wordTrace_append hprefix tailTrace_1082861
  have hstable : (prefixWord ++ tailWord_1082861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082861).length < 2 ^ (prefixWord ++ tailWord_1082861).sum := by decide
  have hdescent : baseEnd_1082861 < baseStart_1082861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082878 : List Nat := [4, 2, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1082878 : Nat := 118140960795 + 1082878 * 2 ^ 59
def prefixEnd_1082878 : Nat := 4983230072969 + 3 ^ 40 * 1082878 * 2
def baseEnd_1082878 : Nat := 370691269453012979029961

theorem tailTrace_1082878 : CollatzResearch.WordTrace tailWord_1082878 prefixEnd_1082878 370691269453012979029961 := by
  unfold tailWord_1082878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936975671365677710452161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26330536913950281122411525 4936975671365677710452161)
  ·
    refine ⟨3702731753524258282839121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4936975671365677710452161 3702731753524258282839121)
    ·
      refine ⟨2777048815143193712129341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3702731753524258282839121 2777048815143193712129341)
      ·
        refine ⟨1041393305678697642048503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2777048815143193712129341 1041393305678697642048503)
        ·
          refine ⟨1562089958518046463072755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041393305678697642048503 1562089958518046463072755)
          ·
            refine ⟨2343134937777069694609133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562089958518046463072755 2343134937777069694609133)
            ·
              refine ⟨878675601666401135478425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2343134937777069694609133 878675601666401135478425)
              ·
                refine ⟨659006701249800851608819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878675601666401135478425 659006701249800851608819)
                ·
                  refine ⟨988510051874701277413229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659006701249800851608819 988510051874701277413229)
                  ·
                    refine ⟨370691269453012979029961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988510051874701277413229 370691269453012979029961)
                    ·
                      rfl

theorem cell22_1082878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1082878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082878 prefixEnd_1082878 := by exact prefixLift 1082878
  have htrace : WordTrace (prefixWord ++ tailWord_1082878) baseStart_1082878 baseEnd_1082878 := by
    simpa [prefixWord, tailWord_1082878, baseEnd_1082878] using wordTrace_append hprefix tailTrace_1082878
  have hstable : (prefixWord ++ tailWord_1082878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082878).length < 2 ^ (prefixWord ++ tailWord_1082878).sum := by decide
  have hdescent : baseEnd_1082878 < baseStart_1082878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082904 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 1, 4]
def baseStart_1082904 : Nat := 118140960795 + 1082904 * 2 ^ 59
def prefixEnd_1082904 : Nat := 4983230072969 + 3 ^ 40 * 1082904 * 2
def baseEnd_1082904 : Nat := 370700169784357577879881

theorem tailTrace_1082904 : CollatzResearch.WordTrace tailWord_1082904 prefixEnd_1082904 370700169784357577879881 := by
  unfold tailWord_1082904
  simp only [CollatzResearch.WordTrace]
  refine ⟨19748376834415614062031883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26331169112554152082709177 19748376834415614062031883)
  ·
    refine ⟨29622565251623421093047825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19748376834415614062031883 29622565251623421093047825)
    ·
      refine ⟨22216923938717565819785869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29622565251623421093047825 22216923938717565819785869)
      ·
        refine ⟨8331346477019087182419701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22216923938717565819785869 8331346477019087182419701)
        ·
          refine ⟨781063732220539423351847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8331346477019087182419701 781063732220539423351847)
          ·
            refine ⟨1171595598330809135027771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781063732220539423351847 1171595598330809135027771)
            ·
              refine ⟨1757393397496213702541657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171595598330809135027771 1757393397496213702541657)
              ·
                refine ⟨1318045048122160276906243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757393397496213702541657 1318045048122160276906243)
                ·
                  refine ⟨1977067572183240415359365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318045048122160276906243 1977067572183240415359365)
                  ·
                    refine ⟨370700169784357577879881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1977067572183240415359365 370700169784357577879881)
                    ·
                      rfl

theorem cell22_1082904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_1082904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082904 prefixEnd_1082904 := by exact prefixLift 1082904
  have htrace : WordTrace (prefixWord ++ tailWord_1082904) baseStart_1082904 baseEnd_1082904 := by
    simpa [prefixWord, tailWord_1082904, baseEnd_1082904] using wordTrace_append hprefix tailTrace_1082904
  have hstable : (prefixWord ++ tailWord_1082904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082904).length < 2 ^ (prefixWord ++ tailWord_1082904).sum := by decide
  have hdescent : baseEnd_1082904 < baseStart_1082904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082913 : List Nat := [1, 2, 3, 2, 2, 2, 2, 8]
def baseStart_1082913 : Nat := 118140960795 + 1082913 * 2 ^ 59
def prefixEnd_1082913 : Nat := 4983230072969 + 3 ^ 40 * 1082913 * 2
def baseEnd_1082913 : Nat := 41189250074253839378317

theorem tailTrace_1082913 : CollatzResearch.WordTrace tailWord_1082913 prefixEnd_1082913 41189250074253839378317 := by
  unfold tailWord_1082913
  simp only [CollatzResearch.WordTrace]
  refine ⟨39497081925798622661141393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26331387950532415107427595 39497081925798622661141393)
  ·
    refine ⟨29622811444348966995856045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39497081925798622661141393 29622811444348966995856045)
    ·
      refine ⟨11108554291630862623446017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29622811444348966995856045 11108554291630862623446017)
      ·
        refine ⟨8331415718723146967584513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11108554291630862623446017 8331415718723146967584513)
        ·
          refine ⟨6248561789042360225688385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8331415718723146967584513 6248561789042360225688385)
          ·
            refine ⟨4686421341781770169266289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6248561789042360225688385 4686421341781770169266289)
            ·
              refine ⟨3514816006336327626949717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4686421341781770169266289 3514816006336327626949717)
              ·
                refine ⟨41189250074253839378317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3514816006336327626949717 41189250074253839378317)
                ·
                  rfl

theorem cell22_1082913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 8].length) (baseStart_1082913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082913 prefixEnd_1082913 := by exact prefixLift 1082913
  have htrace : WordTrace (prefixWord ++ tailWord_1082913) baseStart_1082913 baseEnd_1082913 := by
    simpa [prefixWord, tailWord_1082913, baseEnd_1082913] using wordTrace_append hprefix tailTrace_1082913
  have hstable : (prefixWord ++ tailWord_1082913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082913).length < 2 ^ (prefixWord ++ tailWord_1082913).sum := by decide
  have hdescent : baseEnd_1082913 < baseStart_1082913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082943 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 2, 6]
def baseStart_1082943 : Nat := 118140960795 + 1082943 * 2 ^ 59
def prefixEnd_1082943 : Nat := 4983230072969 + 3 ^ 40 * 1082943 * 2
def baseEnd_1082943 : Nat := 370713520281374476154761

theorem tailTrace_1082943 : CollatzResearch.WordTrace tailWord_1082943 prefixEnd_1082943 370713520281374476154761 := by
  unfold tailWord_1082943
  simp only [CollatzResearch.WordTrace]
  refine ⟨39498176115689937784733483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26332117410459958523155655 39498176115689937784733483)
  ·
    refine ⟨59247264173534906677100225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39498176115689937784733483 59247264173534906677100225)
    ·
      refine ⟨44435448130151180007825169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59247264173534906677100225 44435448130151180007825169)
      ·
        refine ⟨33326586097613385005868877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44435448130151180007825169 33326586097613385005868877)
        ·
          refine ⟨12497469786605019377200829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33326586097613385005868877 12497469786605019377200829)
          ·
            refine ⟨4686551169976882266450311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12497469786605019377200829 4686551169976882266450311)
            ·
              refine ⟨7029826754965323399675467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686551169976882266450311 7029826754965323399675467)
              ·
                refine ⟨10544740132447985099513201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029826754965323399675467 10544740132447985099513201)
                ·
                  refine ⟨7908555099335988824634901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10544740132447985099513201 7908555099335988824634901)
                  ·
                    refine ⟨370713520281374476154761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7908555099335988824634901 370713520281374476154761)
                    ·
                      rfl

theorem cell22_1082943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_1082943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082943 prefixEnd_1082943 := by exact prefixLift 1082943
  have htrace : WordTrace (prefixWord ++ tailWord_1082943) baseStart_1082943 baseEnd_1082943 := by
    simpa [prefixWord, tailWord_1082943, baseEnd_1082943] using wordTrace_append hprefix tailTrace_1082943
  have hstable : (prefixWord ++ tailWord_1082943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082943).length < 2 ^ (prefixWord ++ tailWord_1082943).sum := by decide
  have hdescent : baseEnd_1082943 < baseStart_1082943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082958 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_1082958 : Nat := 118140960795 + 1082958 * 2 ^ 59
def prefixEnd_1082958 : Nat := 4983230072969 + 3 ^ 40 * 1082958 * 2
def baseEnd_1082958 : Nat := 123572885029306479009905

theorem tailTrace_1082958 : CollatzResearch.WordTrace tailWord_1082958 prefixEnd_1082958 123572885029306479009905 := by
  unfold tailWord_1082958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937340401329449418316191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26332482140423730231019685 4937340401329449418316191)
  ·
    refine ⟨7406010601994174127474287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4937340401329449418316191 7406010601994174127474287)
    ·
      refine ⟨11109015902991261191211431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406010601994174127474287 11109015902991261191211431)
      ·
        refine ⟨16663523854486891786817147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11109015902991261191211431 16663523854486891786817147)
        ·
          refine ⟨24995285781730337680225721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16663523854486891786817147 24995285781730337680225721)
          ·
            refine ⟨18746464336297753260169291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24995285781730337680225721 18746464336297753260169291)
            ·
              refine ⟨28119696504446629890253937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18746464336297753260169291 28119696504446629890253937)
              ·
                refine ⟨21089772378334972417690453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28119696504446629890253937 21089772378334972417690453)
                ·
                  refine ⟨123572885029306479009905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21089772378334972417690453 123572885029306479009905)
                  ·
                    rfl

theorem cell22_1082958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_1082958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082958 prefixEnd_1082958 := by exact prefixLift 1082958
  have htrace : WordTrace (prefixWord ++ tailWord_1082958) baseStart_1082958 baseEnd_1082958 := by
    simpa [prefixWord, tailWord_1082958, baseEnd_1082958] using wordTrace_append hprefix tailTrace_1082958
  have hstable : (prefixWord ++ tailWord_1082958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082958).length < 2 ^ (prefixWord ++ tailWord_1082958).sum := by decide
  have hdescent : baseEnd_1082958 < baseStart_1082958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082962 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1082962 : Nat := 118140960795 + 1082962 * 2 ^ 59
def prefixEnd_1082962 : Nat := 4983230072969 + 3 ^ 40 * 1082962 * 2
def baseEnd_1082962 : Nat := 370720024369664759929703

theorem tailTrace_1082962 : CollatzResearch.WordTrace tailWord_1082962 prefixEnd_1082962 370720024369664759929703 := by
  unfold tailWord_1082962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9874717275655276007418785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26332579401747402686450093 9874717275655276007418785)
  ·
    refine ⟨7406037956741457005564089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9874717275655276007418785 7406037956741457005564089)
    ·
      refine ⟨5554528467556092754173067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7406037956741457005564089 5554528467556092754173067)
      ·
        refine ⟨8331792701334139131259601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554528467556092754173067 8331792701334139131259601)
        ·
          refine ⟨6248844526000604348444701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8331792701334139131259601 6248844526000604348444701)
          ·
            refine ⟨2343316697250226630666763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6248844526000604348444701 2343316697250226630666763)
            ·
              refine ⟨3514975045875339946000145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343316697250226630666763 3514975045875339946000145)
              ·
                refine ⟨2636231284406504959500109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514975045875339946000145 2636231284406504959500109)
                ·
                  refine ⟨988586731652439359812541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2636231284406504959500109 988586731652439359812541)
                  ·
                    refine ⟨370720024369664759929703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988586731652439359812541 370720024369664759929703)
                    ·
                      rfl

theorem cell22_1082962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1082962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1082962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1082962 prefixEnd_1082962 := by exact prefixLift 1082962
  have htrace : WordTrace (prefixWord ++ tailWord_1082962) baseStart_1082962 baseEnd_1082962 := by
    simpa [prefixWord, tailWord_1082962, baseEnd_1082962] using wordTrace_append hprefix tailTrace_1082962
  have hstable : (prefixWord ++ tailWord_1082962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082962).length < 2 ^ (prefixWord ++ tailWord_1082962).sum := by decide
  have hdescent : baseEnd_1082962 < baseStart_1082962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
