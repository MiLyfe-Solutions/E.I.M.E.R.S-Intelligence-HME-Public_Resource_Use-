import V185TrunkScan21Chunk130

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1595818 : List Nat := [3, 1, 6, 1, 2, 1, 2, 5]
def baseStart_1595818 : Nat := 118140960795 + 1595818 * 2 ^ 59
def prefixEnd_1595818 : Nat := 4983230072969 + 3 ^ 40 * 1595818 * 2
def baseEnd_1595818 : Nat := 121395803125443346434959

theorem tailTrace_1595818 : CollatzResearch.WordTrace tailWord_1595818 prefixEnd_1595818 121395803125443346434959 := by
  unfold tailWord_1595818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14551066033157851215293027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38802842755087603240781405 14551066033157851215293027)
  ·
    refine ⟨21826599049736776822939541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14551066033157851215293027 21826599049736776822939541)
    ·
      refine ⟨1023121830456411413575291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21826599049736776822939541 1023121830456411413575291)
      ·
        refine ⟨1534682745684617120362937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023121830456411413575291 1534682745684617120362937)
        ·
          refine ⟨1151012059263462840272203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534682745684617120362937 1151012059263462840272203)
          ·
            refine ⟨1726518088895194260408305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151012059263462840272203 1726518088895194260408305)
            ·
              refine ⟨1294888566671395695306229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726518088895194260408305 1294888566671395695306229)
              ·
                refine ⟨121395803125443346434959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1294888566671395695306229 121395803125443346434959)
                ·
                  rfl

theorem cell21_1595818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_1595818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595818 prefixEnd_1595818 := by exact prefixLift 1595818
  have htrace : WordTrace (prefixWord ++ tailWord_1595818) baseStart_1595818 baseEnd_1595818 := by
    simpa [prefixWord, tailWord_1595818, baseEnd_1595818] using wordTrace_append hprefix tailTrace_1595818
  have hstable : (prefixWord ++ tailWord_1595818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595818).length < 2 ^ (prefixWord ++ tailWord_1595818).sum := by decide
  have hdescent : baseEnd_1595818 < baseStart_1595818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595871 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 4]
def baseStart_1595871 : Nat := 118140960795 + 1595871 * 2 ^ 59
def prefixEnd_1595871 : Nat := 4983230072969 + 3 ^ 40 * 1595871 * 2
def baseEnd_1595871 : Nat := 364199504698413724921435

theorem tailTrace_1595871 : CollatzResearch.WordTrace tailWord_1595871 prefixEnd_1595871 364199504698413724921435 := by
  unfold tailWord_1595871
  simp only [CollatzResearch.WordTrace]
  refine ⟨58206197201439394912851467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38804131467626263275234311 58206197201439394912851467)
  ·
    refine ⟨87309295802159092369277201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58206197201439394912851467 87309295802159092369277201)
    ·
      refine ⟨65481971851619319276957901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87309295802159092369277201 65481971851619319276957901)
      ·
        refine ⟨24555739444357244728859213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65481971851619319276957901 24555739444357244728859213)
        ·
          refine ⟨9208402291633966773322205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24555739444357244728859213 9208402291633966773322205)
          ·
            refine ⟨3453150859362737539995827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9208402291633966773322205 3453150859362737539995827)
            ·
              refine ⟨5179726289044106309993741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3453150859362737539995827 5179726289044106309993741)
              ·
                refine ⟨1942397358391539866247653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5179726289044106309993741 1942397358391539866247653)
                ·
                  refine ⟨364199504698413724921435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942397358391539866247653 364199504698413724921435)
                  ·
                    rfl

theorem cell21_1595871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_1595871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595871 prefixEnd_1595871 := by exact prefixLift 1595871
  have htrace : WordTrace (prefixWord ++ tailWord_1595871) baseStart_1595871 baseEnd_1595871 := by
    simpa [prefixWord, tailWord_1595871, baseEnd_1595871] using wordTrace_append hprefix tailTrace_1595871
  have hstable : (prefixWord ++ tailWord_1595871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595871).length < 2 ^ (prefixWord ++ tailWord_1595871).sum := by decide
  have hdescent : baseEnd_1595871 < baseStart_1595871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595964 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_1595964 : Nat := 118140960795 + 1595964 * 2 ^ 59
def prefixEnd_1595964 : Nat := 4983230072969 + 3 ^ 40 * 1595964 * 2
def baseEnd_1595964 : Nat := 364220728565466229871245

theorem tailTrace_1595964 : CollatzResearch.WordTrace tailWord_1595964 prefixEnd_1595964 364220728565466229871245 := by
  unfold tailWord_1595964
  simp only [CollatzResearch.WordTrace]
  refine ⟨29104794595051235897993473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38806392793401647863991297 29104794595051235897993473)
  ·
    refine ⟨21828595946288426923495105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29104794595051235897993473 21828595946288426923495105)
    ·
      refine ⟨16371446959716320192621329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21828595946288426923495105 16371446959716320192621329)
      ·
        refine ⟨12278585219787240144465997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16371446959716320192621329 12278585219787240144465997)
        ·
          refine ⟨4604469457420215054174749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12278585219787240144465997 4604469457420215054174749)
          ·
            refine ⟨1726676046532580645315531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4604469457420215054174749 1726676046532580645315531)
            ·
              refine ⟨2590014069798870967973297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726676046532580645315531 2590014069798870967973297)
              ·
                refine ⟨1942510552349153225979973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590014069798870967973297 1942510552349153225979973)
                ·
                  refine ⟨364220728565466229871245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942510552349153225979973 364220728565466229871245)
                  ·
                    rfl

theorem cell21_1595964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_1595964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595964 prefixEnd_1595964 := by exact prefixLift 1595964
  have htrace : WordTrace (prefixWord ++ tailWord_1595964) baseStart_1595964 baseEnd_1595964 := by
    simpa [prefixWord, tailWord_1595964, baseEnd_1595964] using wordTrace_append hprefix tailTrace_1595964
  have hstable : (prefixWord ++ tailWord_1595964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595964).length < 2 ^ (prefixWord ++ tailWord_1595964).sum := by decide
  have hdescent : baseEnd_1595964 < baseStart_1595964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595981 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1595981 : Nat := 118140960795 + 1595981 * 2 ^ 59
def prefixEnd_1595981 : Nat := 4983230072969 + 3 ^ 40 * 1595981 * 2
def baseEnd_1595981 : Nat := 364224608197077978087877

theorem tailTrace_1595981 : CollatzResearch.WordTrace tailWord_1595981 prefixEnd_1595981 364224608197077978087877 := by
  unfold tailWord_1595981
  simp only [CollatzResearch.WordTrace]
  refine ⟨58210209231040883699355797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38806806154027255799570531 58210209231040883699355797)
  ·
    refine ⟨2728603557705041423407303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58210209231040883699355797 2728603557705041423407303)
    ·
      refine ⟨4092905336557562135110955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728603557705041423407303 4092905336557562135110955)
      ·
        refine ⟨6139358004836343202666433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092905336557562135110955 6139358004836343202666433)
        ·
          refine ⟨4604518503627257401999825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6139358004836343202666433 4604518503627257401999825)
          ·
            refine ⟨3453388877720443051499869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4604518503627257401999825 3453388877720443051499869)
            ·
              refine ⟨1295020829145166144312451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3453388877720443051499869 1295020829145166144312451)
              ·
                refine ⟨1942531243717749216468677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295020829145166144312451 1942531243717749216468677)
                ·
                  refine ⟨364224608197077978087877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942531243717749216468677 364224608197077978087877)
                  ·
                    rfl

theorem cell21_1595981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1595981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1595981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1595981 prefixEnd_1595981 := by exact prefixLift 1595981
  have htrace : WordTrace (prefixWord ++ tailWord_1595981) baseStart_1595981 baseEnd_1595981 := by
    simpa [prefixWord, tailWord_1595981, baseEnd_1595981] using wordTrace_append hprefix tailTrace_1595981
  have hstable : (prefixWord ++ tailWord_1595981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595981).length < 2 ^ (prefixWord ++ tailWord_1595981).sum := by decide
  have hdescent : baseEnd_1595981 < baseStart_1595981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596037 : List Nat := [1, 3, 1, 1, 4, 3, 2, 6]
def baseStart_1596037 : Nat := 118140960795 + 1596037 * 2 ^ 59
def prefixEnd_1596037 : Nat := 4983230072969 + 3 ^ 40 * 1596037 * 2
def baseEnd_1596037 : Nat := 121412462720011441718143

theorem tailTrace_1596037 : CollatzResearch.WordTrace tailWord_1596037 prefixEnd_1596037 121412462720011441718143 := by
  unfold tailWord_1596037
  simp only [CollatzResearch.WordTrace]
  refine ⟨58212251718838005263394365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38808167812558670175596243 58212251718838005263394365)
  ·
    refine ⟨21829594394564251973772887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58212251718838005263394365 21829594394564251973772887)
    ·
      refine ⟨32744391591846377960659331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21829594394564251973772887 32744391591846377960659331)
      ·
        refine ⟨49116587387769566940988997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32744391591846377960659331 49116587387769566940988997)
        ·
          refine ⟨9209360135206793801435437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49116587387769566940988997 9209360135206793801435437)
          ·
            refine ⟨3453510050702547675538289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9209360135206793801435437 3453510050702547675538289)
            ·
              refine ⟨2590132538026910756653717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3453510050702547675538289 2590132538026910756653717)
              ·
                refine ⟨121412462720011441718143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2590132538026910756653717 121412462720011441718143)
                ·
                  rfl

theorem cell21_1596037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 6].length) (baseStart_1596037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596037 prefixEnd_1596037 := by exact prefixLift 1596037
  have htrace : WordTrace (prefixWord ++ tailWord_1596037) baseStart_1596037 baseEnd_1596037 := by
    simpa [prefixWord, tailWord_1596037, baseEnd_1596037] using wordTrace_append hprefix tailTrace_1596037
  have hstable : (prefixWord ++ tailWord_1596037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596037).length < 2 ^ (prefixWord ++ tailWord_1596037).sum := by decide
  have hdescent : baseEnd_1596037 < baseStart_1596037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596113 : List Nat := [1, 2, 2, 1, 2, 3, 5, 5]
def baseStart_1596113 : Nat := 118140960795 + 1596113 * 2 ^ 59
def prefixEnd_1596113 : Nat := 4983230072969 + 3 ^ 40 * 1596113 * 2
def baseEnd_1596113 : Nat := 121418244131825027295869

theorem tailTrace_1596113 : CollatzResearch.WordTrace tailWord_1596113 prefixEnd_1596113 121418244131825027295869 := by
  unfold tailWord_1596113
  simp only [CollatzResearch.WordTrace]
  refine ⟨58215023666562670243160993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38810015777708446828773995 58215023666562670243160993)
  ·
    refine ⟨43661267749922002682370745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58215023666562670243160993 43661267749922002682370745)
    ·
      refine ⟨32745950812441502011778059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43661267749922002682370745 32745950812441502011778059)
      ·
        refine ⟨49118926218662253017667089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32745950812441502011778059 49118926218662253017667089)
        ·
          refine ⟨36839194663996689763250317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49118926218662253017667089 36839194663996689763250317)
          ·
            refine ⟨13814697998998758661218869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36839194663996689763250317 13814697998998758661218869)
            ·
              refine ⟨1295127937406133624489269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13814697998998758661218869 1295127937406133624489269)
              ·
                refine ⟨121418244131825027295869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1295127937406133624489269 121418244131825027295869)
                ·
                  rfl

theorem cell21_1596113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 5].length) (baseStart_1596113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596113 prefixEnd_1596113 := by exact prefixLift 1596113
  have htrace : WordTrace (prefixWord ++ tailWord_1596113) baseStart_1596113 baseEnd_1596113 := by
    simpa [prefixWord, tailWord_1596113, baseEnd_1596113] using wordTrace_append hprefix tailTrace_1596113
  have hstable : (prefixWord ++ tailWord_1596113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596113).length < 2 ^ (prefixWord ++ tailWord_1596113).sum := by decide
  have hdescent : baseEnd_1596113 < baseStart_1596113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596144 : List Nat := [2, 1, 1, 1, 3, 1, 3, 6, 3]
def baseStart_1596144 : Nat := 118140960795 + 1596144 * 2 ^ 59
def prefixEnd_1596144 : Nat := 4983230072969 + 3 ^ 40 * 1596144 * 2
def baseEnd_1596144 : Nat := 364261807017825916870877

theorem tailTrace_1596144 : CollatzResearch.WordTrace tailWord_1596144 prefixEnd_1596144 364261807017825916870877 := by
  unfold tailWord_1596144
  simp only [CollatzResearch.WordTrace]
  refine ⟨29108077164725181268769743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38810769552966908358359657 29108077164725181268769743)
  ·
    refine ⟨43662115747087771903154615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29108077164725181268769743 43662115747087771903154615)
    ·
      refine ⟨65493173620631657854731923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43662115747087771903154615 65493173620631657854731923)
      ·
        refine ⟨98239760430947486782097885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65493173620631657854731923 98239760430947486782097885)
        ·
          refine ⟨36839910161605307543286707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98239760430947486782097885 36839910161605307543286707)
          ·
            refine ⟨55259865242407961314930061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36839910161605307543286707 55259865242407961314930061)
            ·
              refine ⟨20722449465902985493098773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55259865242407961314930061 20722449465902985493098773)
              ·
                refine ⟨971364818714202444989005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20722449465902985493098773 971364818714202444989005)
                ·
                  refine ⟨364261807017825916870877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971364818714202444989005 364261807017825916870877)
                  ·
                    rfl

theorem cell21_1596144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_1596144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596144 prefixEnd_1596144 := by exact prefixLift 1596144
  have htrace : WordTrace (prefixWord ++ tailWord_1596144) baseStart_1596144 baseEnd_1596144 := by
    simpa [prefixWord, tailWord_1596144, baseEnd_1596144] using wordTrace_append hprefix tailTrace_1596144
  have hstable : (prefixWord ++ tailWord_1596144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596144).length < 2 ^ (prefixWord ++ tailWord_1596144).sum := by decide
  have hdescent : baseEnd_1596144 < baseStart_1596144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596206 : List Nat := [4, 1, 3, 2, 1, 2, 2, 6]
def baseStart_1596206 : Nat := 118140960795 + 1596206 * 2 ^ 59
def prefixEnd_1596206 : Nat := 4983230072969 + 3 ^ 40 * 1596206 * 2
def baseEnd_1596206 : Nat := 121425318754175862279139

theorem tailTrace_1596206 : CollatzResearch.WordTrace tailWord_1596206 prefixEnd_1596206 121425318754175862279139 := by
  unfold tailWord_1596206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7277301956903218390787059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38812277103483831417530981 7277301956903218390787059)
  ·
    refine ⟨10915952935354827586180589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7277301956903218390787059 10915952935354827586180589)
    ·
      refine ⟨4093482350758060344817721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10915952935354827586180589 4093482350758060344817721)
      ·
        refine ⟨3070111763068545258613291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4093482350758060344817721 3070111763068545258613291)
        ·
          refine ⟨4605167644602817887919937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070111763068545258613291 4605167644602817887919937)
          ·
            refine ⟨3453875733452113415939953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4605167644602817887919937 3453875733452113415939953)
            ·
              refine ⟨2590406800089085061954965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3453875733452113415939953 2590406800089085061954965)
              ·
                refine ⟨121425318754175862279139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2590406800089085061954965 121425318754175862279139)
                ·
                  rfl

theorem cell21_1596206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_1596206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596206 prefixEnd_1596206 := by exact prefixLift 1596206
  have htrace : WordTrace (prefixWord ++ tailWord_1596206) baseStart_1596206 baseEnd_1596206 := by
    simpa [prefixWord, tailWord_1596206, baseEnd_1596206] using wordTrace_append hprefix tailTrace_1596206
  have hstable : (prefixWord ++ tailWord_1596206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596206).length < 2 ^ (prefixWord ++ tailWord_1596206).sum := by decide
  have hdescent : baseEnd_1596206 < baseStart_1596206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596324 : List Nat := [2, 3, 1, 2, 1, 2, 2, 8]
def baseStart_1596324 : Nat := 118140960795 + 1596324 * 2 ^ 59
def prefixEnd_1596324 : Nat := 4983230072969 + 3 ^ 40 * 1596324 * 2
def baseEnd_1596324 : Nat := 121434295156728534623503

theorem tailTrace_1596324 : CollatzResearch.WordTrace tailWord_1596324 prefixEnd_1596324 121434295156728534623503 := by
  unfold tailWord_1596324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29111359734399126639546013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38815146312532168852728017 29111359734399126639546013)
  ·
    refine ⟨10916759900399672489829755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29111359734399126639546013 10916759900399672489829755)
    ·
      refine ⟨16375139850599508734744633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10916759900399672489829755 16375139850599508734744633)
      ·
        refine ⟨12281354887949631551058475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16375139850599508734744633 12281354887949631551058475)
        ·
          refine ⟨18422032331924447326587713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12281354887949631551058475 18422032331924447326587713)
          ·
            refine ⟨13816524248943335494940785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18422032331924447326587713 13816524248943335494940785)
            ·
              refine ⟨10362393186707501621205589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13816524248943335494940785 10362393186707501621205589)
              ·
                refine ⟨121434295156728534623503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10362393186707501621205589 121434295156728534623503)
                ·
                  rfl

theorem cell21_1596324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_1596324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596324 prefixEnd_1596324 := by exact prefixLift 1596324
  have htrace : WordTrace (prefixWord ++ tailWord_1596324) baseStart_1596324 baseEnd_1596324 := by
    simpa [prefixWord, tailWord_1596324, baseEnd_1596324] using wordTrace_append hprefix tailTrace_1596324
  have hstable : (prefixWord ++ tailWord_1596324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596324).length < 2 ^ (prefixWord ++ tailWord_1596324).sum := by decide
  have hdescent : baseEnd_1596324 < baseStart_1596324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596369 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 6]
def baseStart_1596369 : Nat := 118140960795 + 1596369 * 2 ^ 59
def prefixEnd_1596369 : Nat := 4983230072969 + 3 ^ 40 * 1596369 * 2
def baseEnd_1596369 : Nat := 364313155083275525620417

theorem tailTrace_1596369 : CollatzResearch.WordTrace tailWord_1596369 prefixEnd_1596369 364313155083275525620417 := by
  unfold tailWord_1596369
  simp only [CollatzResearch.WordTrace]
  refine ⟨58224360753635225964480161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38816240502423483976320107 58224360753635225964480161)
  ·
    refine ⟨43668270565226419473360121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58224360753635225964480161 43668270565226419473360121)
    ·
      refine ⟨32751202923919814605020091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43668270565226419473360121 32751202923919814605020091)
      ·
        refine ⟨49126804385879721907530137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32751202923919814605020091 49126804385879721907530137)
        ·
          refine ⟨36845103289409791430647603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49126804385879721907530137 36845103289409791430647603)
          ·
            refine ⟨55267654934114687145971405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36845103289409791430647603 55267654934114687145971405)
            ·
              refine ⟨20725370600293007679739277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55267654934114687145971405 20725370600293007679739277)
              ·
                refine ⟨7772013975109877879902229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20725370600293007679739277 7772013975109877879902229)
                ·
                  refine ⟨364313155083275525620417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7772013975109877879902229 364313155083275525620417)
                  ·
                    rfl

theorem cell21_1596369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_1596369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596369 prefixEnd_1596369 := by exact prefixLift 1596369
  have htrace : WordTrace (prefixWord ++ tailWord_1596369) baseStart_1596369 baseEnd_1596369 := by
    simpa [prefixWord, tailWord_1596369, baseEnd_1596369] using wordTrace_append hprefix tailTrace_1596369
  have hstable : (prefixWord ++ tailWord_1596369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596369).length < 2 ^ (prefixWord ++ tailWord_1596369).sum := by decide
  have hdescent : baseEnd_1596369 < baseStart_1596369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596372 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1596372 : Nat := 118140960795 + 1596372 * 2 ^ 59
def prefixEnd_1596372 : Nat := 4983230072969 + 3 ^ 40 * 1596372 * 2
def baseEnd_1596372 : Nat := 364313839724148187070411

theorem tailTrace_1596372 : CollatzResearch.WordTrace tailWord_1596372 prefixEnd_1596372 364313839724148187070411 := by
  unfold tailWord_1596372
  simp only [CollatzResearch.WordTrace]
  refine ⟨29112235086312178738419685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38816313448416238317892913 29112235086312178738419685)
  ·
    refine ⟨5458544078683533513453691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29112235086312178738419685 5458544078683533513453691)
    ·
      refine ⟨8187816118025300270180537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5458544078683533513453691 8187816118025300270180537)
      ·
        refine ⟨6140862088518975202635403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8187816118025300270180537 6140862088518975202635403)
        ·
          refine ⟨9211293132778462803953105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6140862088518975202635403 9211293132778462803953105)
          ·
            refine ⟨6908469849583847102964829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9211293132778462803953105 6908469849583847102964829)
            ·
              refine ⟨2590676193593942663611811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6908469849583847102964829 2590676193593942663611811)
              ·
                refine ⟨3886014290390913995417717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590676193593942663611811 3886014290390913995417717)
                ·
                  refine ⟨364313839724148187070411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3886014290390913995417717 364313839724148187070411)
                  ·
                    rfl

theorem cell21_1596372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1596372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596372 prefixEnd_1596372 := by exact prefixLift 1596372
  have htrace : WordTrace (prefixWord ++ tailWord_1596372) baseStart_1596372 baseEnd_1596372 := by
    simpa [prefixWord, tailWord_1596372, baseEnd_1596372] using wordTrace_append hprefix tailTrace_1596372
  have hstable : (prefixWord ++ tailWord_1596372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596372).length < 2 ^ (prefixWord ++ tailWord_1596372).sum := by decide
  have hdescent : baseEnd_1596372 < baseStart_1596372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596462 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1596462 : Nat := 118140960795 + 1596462 * 2 ^ 59
def prefixEnd_1596462 : Nat := 4983230072969 + 3 ^ 40 * 1596462 * 2
def baseEnd_1596462 : Nat := 364334378950328030570227

theorem tailTrace_1596462 : CollatzResearch.WordTrace tailWord_1596462 prefixEnd_1596462 364334378950328030570227 := by
  unfold tailWord_1596462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7278469092787287855951955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38818501828198868565077093 7278469092787287855951955)
  ·
    refine ⟨10917703639180931783927933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7278469092787287855951955 10917703639180931783927933)
    ·
      refine ⟨4094138864692849418972975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10917703639180931783927933 4094138864692849418972975)
      ·
        refine ⟨6141208297039274128459463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094138864692849418972975 6141208297039274128459463)
        ·
          refine ⟨9211812445558911192689195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6141208297039274128459463 9211812445558911192689195)
          ·
            refine ⟨13817718668338366789033793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9211812445558911192689195 13817718668338366789033793)
            ·
              refine ⟨10363289001253775091775345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13817718668338366789033793 10363289001253775091775345)
              ·
                refine ⟨7772466750940331318831509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10363289001253775091775345 7772466750940331318831509)
                ·
                  refine ⟨364334378950328030570227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7772466750940331318831509 364334378950328030570227)
                  ·
                    rfl

theorem cell21_1596462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1596462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596462 prefixEnd_1596462 := by exact prefixLift 1596462
  have htrace : WordTrace (prefixWord ++ tailWord_1596462) baseStart_1596462 baseEnd_1596462 := by
    simpa [prefixWord, tailWord_1596462, baseEnd_1596462] using wordTrace_append hprefix tailTrace_1596462
  have hstable : (prefixWord ++ tailWord_1596462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596462).length < 2 ^ (prefixWord ++ tailWord_1596462).sum := by decide
  have hdescent : baseEnd_1596462 < baseStart_1596462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596476 : List Nat := [2, 2, 2, 2, 2, 3, 8]
def baseStart_1596476 : Nat := 118140960795 + 1596476 * 2 ^ 59
def prefixEnd_1596476 : Nat := 4983230072969 + 3 ^ 40 * 1596476 * 2
def baseEnd_1596476 : Nat := 40481952660118568592985

theorem tailTrace_1596476 : CollatzResearch.WordTrace tailWord_1596476 prefixEnd_1596476 40481952660118568592985 := by
  unfold tailWord_1596476
  simp only [CollatzResearch.WordTrace]
  refine ⟨29114131682123791619312641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38818842242831722159083521 29114131682123791619312641)
  ·
    refine ⟨21835598761592843714484481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29114131682123791619312641 21835598761592843714484481)
    ·
      refine ⟨16376699071194632785863361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21835598761592843714484481 16376699071194632785863361)
      ·
        refine ⟨12282524303395974589397521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16376699071194632785863361 12282524303395974589397521)
        ·
          refine ⟨9211893227546980942048141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12282524303395974589397521 9211893227546980942048141)
          ·
            refine ⟨3454459960330117853268053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9211893227546980942048141 3454459960330117853268053)
            ·
              refine ⟨40481952660118568592985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3454459960330117853268053 40481952660118568592985)
              ·
                rfl

theorem cell21_1596476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 8].length) (baseStart_1596476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596476 prefixEnd_1596476 := by exact prefixLift 1596476
  have htrace : WordTrace (prefixWord ++ tailWord_1596476) baseStart_1596476 baseEnd_1596476 := by
    simpa [prefixWord, tailWord_1596476, baseEnd_1596476] using wordTrace_append hprefix tailTrace_1596476
  have hstable : (prefixWord ++ tailWord_1596476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596476).length < 2 ^ (prefixWord ++ tailWord_1596476).sum := by decide
  have hdescent : baseEnd_1596476 < baseStart_1596476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596521 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 6]
def baseStart_1596521 : Nat := 118140960795 + 1596521 * 2 ^ 59
def prefixEnd_1596521 : Nat := 4983230072969 + 3 ^ 40 * 1596521 * 2
def baseEnd_1596521 : Nat := 364347843554157039086773

theorem tailTrace_1596521 : CollatzResearch.WordTrace tailWord_1596521 prefixEnd_1596521 364347843554157039086773 := by
  unfold tailWord_1596521
  simp only [CollatzResearch.WordTrace]
  refine ⟨58229904649084555924013417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38819936432723037282675611 58229904649084555924013417)
  ·
    refine ⟨43672428486813416943010063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58229904649084555924013417 43672428486813416943010063)
    ·
      refine ⟨65508642730220125414515095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43672428486813416943010063 65508642730220125414515095)
      ·
        refine ⟨98262964095330188121772643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65508642730220125414515095 98262964095330188121772643)
        ·
          refine ⟨147394446142995282182658965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98262964095330188121772643 147394446142995282182658965)
          ·
            refine ⟨6909114662952903852312139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147394446142995282182658965 6909114662952903852312139)
            ·
              refine ⟨10363671994429355778468209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6909114662952903852312139 10363671994429355778468209)
              ·
                refine ⟨7772753995822016833851157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10363671994429355778468209 7772753995822016833851157)
                ·
                  refine ⟨364347843554157039086773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7772753995822016833851157 364347843554157039086773)
                  ·
                    rfl

theorem cell21_1596521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_1596521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596521 prefixEnd_1596521 := by exact prefixLift 1596521
  have htrace : WordTrace (prefixWord ++ tailWord_1596521) baseStart_1596521 baseEnd_1596521 := by
    simpa [prefixWord, tailWord_1596521, baseEnd_1596521] using wordTrace_append hprefix tailTrace_1596521
  have hstable : (prefixWord ++ tailWord_1596521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596521).length < 2 ^ (prefixWord ++ tailWord_1596521).sum := by decide
  have hdescent : baseEnd_1596521 < baseStart_1596521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596541 : List Nat := [1, 4, 1, 1, 3, 1, 5, 2, 3]
def baseStart_1596541 : Nat := 118140960795 + 1596541 * 2 ^ 59
def prefixEnd_1596541 : Nat := 4983230072969 + 3 ^ 40 * 1596541 * 2
def baseEnd_1596541 : Nat := 364352407826641448753399

theorem tailTrace_1596541 : CollatzResearch.WordTrace tailWord_1596541 prefixEnd_1596541 364352407826641448753399 := by
  unfold tailWord_1596541
  simp only [CollatzResearch.WordTrace]
  refine ⟨58230634109012099339741477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38820422739341399559827651 58230634109012099339741477)
  ·
    refine ⟨10918243895439768626201527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58230634109012099339741477 10918243895439768626201527)
    ·
      refine ⟨16377365843159652939302291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10918243895439768626201527 16377365843159652939302291)
      ·
        refine ⟨24566048764739479408953437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16377365843159652939302291 24566048764739479408953437)
        ·
          refine ⟨9212268286777304778357539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24566048764739479408953437 9212268286777304778357539)
          ·
            refine ⟨13818402430165957167536309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212268286777304778357539 13818402430165957167536309)
            ·
              refine ⟨1295475227828058484456529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13818402430165957167536309 1295475227828058484456529)
              ·
                refine ⟨971606420871043863342397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295475227828058484456529 971606420871043863342397)
                ·
                  refine ⟨364352407826641448753399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971606420871043863342397 364352407826641448753399)
                  ·
                    rfl

theorem cell21_1596541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_1596541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596541 prefixEnd_1596541 := by exact prefixLift 1596541
  have htrace : WordTrace (prefixWord ++ tailWord_1596541) baseStart_1596541 baseEnd_1596541 := by
    simpa [prefixWord, tailWord_1596541, baseEnd_1596541] using wordTrace_append hprefix tailTrace_1596541
  have hstable : (prefixWord ++ tailWord_1596541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596541).length < 2 ^ (prefixWord ++ tailWord_1596541).sum := by decide
  have hdescent : baseEnd_1596541 < baseStart_1596541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596611 : List Nat := [1, 1, 1, 3, 1, 1, 1, 12]
def baseStart_1596611 : Nat := 118140960795 + 1596611 * 2 ^ 59
def prefixEnd_1596611 : Nat := 4983230072969 + 3 ^ 40 * 1596611 * 2
def baseEnd_1596611 : Nat := 121456127593445627528863

theorem tailTrace_1596611 : CollatzResearch.WordTrace tailWord_1596611 prefixEnd_1596611 121456127593445627528863 := by
  unfold tailWord_1596611
  simp only [CollatzResearch.WordTrace]
  refine ⟨58233187218758501294789687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38822124812505667529859791 58233187218758501294789687)
  ·
    refine ⟨87349780828137751942184531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58233187218758501294789687 87349780828137751942184531)
    ·
      refine ⟨131024671242206627913276797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87349780828137751942184531 131024671242206627913276797)
      ·
        refine ⟨49134251715827485467478799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131024671242206627913276797 49134251715827485467478799)
        ·
          refine ⟨73701377573741228201218199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49134251715827485467478799 73701377573741228201218199)
          ·
            refine ⟨110552066360611842301827299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73701377573741228201218199 110552066360611842301827299)
            ·
              refine ⟨165828099540917763452740949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110552066360611842301827299 165828099540917763452740949)
              ·
                refine ⟨121456127593445627528863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 165828099540917763452740949 121456127593445627528863)
                ·
                  rfl

theorem cell21_1596611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_1596611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596611 prefixEnd_1596611 := by exact prefixLift 1596611
  have htrace : WordTrace (prefixWord ++ tailWord_1596611) baseStart_1596611 baseEnd_1596611 := by
    simpa [prefixWord, tailWord_1596611, baseEnd_1596611] using wordTrace_append hprefix tailTrace_1596611
  have hstable : (prefixWord ++ tailWord_1596611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596611).length < 2 ^ (prefixWord ++ tailWord_1596611).sum := by decide
  have hdescent : baseEnd_1596611 < baseStart_1596611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596659 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 5]
def baseStart_1596659 : Nat := 118140960795 + 1596659 * 2 ^ 59
def prefixEnd_1596659 : Nat := 4983230072969 + 3 ^ 40 * 1596659 * 2
def baseEnd_1596659 : Nat := 364379337034299465786491

theorem tailTrace_1596659 : CollatzResearch.WordTrace tailWord_1596659 prefixEnd_1596659 364379337034299465786491 := by
  unfold tailWord_1596659
  simp only [CollatzResearch.WordTrace]
  refine ⟨58234937922584605492537031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38823291948389736995024687 58234937922584605492537031)
  ·
    refine ⟨87352406883876908238805547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58234937922584605492537031 87352406883876908238805547)
    ·
      refine ⟨131028610325815362358208321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87352406883876908238805547 131028610325815362358208321)
      ·
        refine ⟨98271457744361521768656241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131028610325815362358208321 98271457744361521768656241)
        ·
          refine ⟨73703593308271141326492181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98271457744361521768656241 73703593308271141326492181)
          ·
            refine ⟨3454855936325209749679321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73703593308271141326492181 3454855936325209749679321)
            ·
              refine ⟨2591141952243907312259491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3454855936325209749679321 2591141952243907312259491)
              ·
                refine ⟨3886712928365860968389237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591141952243907312259491 3886712928365860968389237)
                ·
                  refine ⟨364379337034299465786491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3886712928365860968389237 364379337034299465786491)
                  ·
                    rfl

theorem cell21_1596659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_1596659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596659 prefixEnd_1596659 := by exact prefixLift 1596659
  have htrace : WordTrace (prefixWord ++ tailWord_1596659) baseStart_1596659 baseEnd_1596659 := by
    simpa [prefixWord, tailWord_1596659, baseEnd_1596659] using wordTrace_append hprefix tailTrace_1596659
  have hstable : (prefixWord ++ tailWord_1596659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596659).length < 2 ^ (prefixWord ++ tailWord_1596659).sum := by decide
  have hdescent : baseEnd_1596659 < baseStart_1596659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596758 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1596758 : Nat := 118140960795 + 1596758 * 2 ^ 59
def prefixEnd_1596758 : Nat := 4983230072969 + 3 ^ 40 * 1596758 * 2
def baseEnd_1596758 : Nat := 364401930183097293636289

theorem tailTrace_1596758 : CollatzResearch.WordTrace tailWord_1596758 prefixEnd_1596758 364401930183097293636289 := by
  unfold tailWord_1596758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3639909296826621587524433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38825699166150630266927285 3639909296826621587524433)
  ·
    refine ⟨2729931972619966190643325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3639909296826621587524433 2729931972619966190643325)
    ·
      refine ⟨1023724489732487321491247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2729931972619966190643325 1023724489732487321491247)
      ·
        refine ⟨1535586734598730982236871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023724489732487321491247 1535586734598730982236871)
        ·
          refine ⟨2303380101898096473355307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535586734598730982236871 2303380101898096473355307)
          ·
            refine ⟨3455070152847144710032961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303380101898096473355307 3455070152847144710032961)
            ·
              refine ⟨2591302614635358532524721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455070152847144710032961 2591302614635358532524721)
              ·
                refine ⟨1943476960976518899393541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591302614635358532524721 1943476960976518899393541)
                ·
                  refine ⟨364401930183097293636289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943476960976518899393541 364401930183097293636289)
                  ·
                    rfl

theorem cell21_1596758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1596758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596758 prefixEnd_1596758 := by exact prefixLift 1596758
  have htrace : WordTrace (prefixWord ++ tailWord_1596758) baseStart_1596758 baseEnd_1596758 := by
    simpa [prefixWord, tailWord_1596758, baseEnd_1596758] using wordTrace_append hprefix tailTrace_1596758
  have hstable : (prefixWord ++ tailWord_1596758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596758).length < 2 ^ (prefixWord ++ tailWord_1596758).sum := by decide
  have hdescent : baseEnd_1596758 < baseStart_1596758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596780 : List Nat := [2, 2, 1, 1, 5, 1, 3, 6]
def baseStart_1596780 : Nat := 118140960795 + 1596780 * 2 ^ 59
def prefixEnd_1596780 : Nat := 4983230072969 + 3 ^ 40 * 1596780 * 2
def baseEnd_1596780 : Nat := 121468983627610048089859

theorem tailTrace_1596780 : CollatzResearch.WordTrace tailWord_1596780 prefixEnd_1596780 121468983627610048089859 := by
  unfold tailWord_1596780
  simp only [CollatzResearch.WordTrace]
  refine ⟨29119675577573121578845897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38826234103430828771794529 29119675577573121578845897)
  ·
    refine ⟨21839756683179841184134423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29119675577573121578845897 21839756683179841184134423)
    ·
      refine ⟨32759635024769761776201635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21839756683179841184134423 32759635024769761776201635)
      ·
        refine ⟨49139452537154642664302453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32759635024769761776201635 49139452537154642664302453)
        ·
          refine ⟨4606823675358247749778355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49139452537154642664302453 4606823675358247749778355)
          ·
            refine ⟨6910235513037371624667533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606823675358247749778355 6910235513037371624667533)
            ·
              refine ⟨2591338317389014359250325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6910235513037371624667533 2591338317389014359250325)
              ·
                refine ⟨121468983627610048089859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2591338317389014359250325 121468983627610048089859)
                ·
                  rfl

theorem cell21_1596780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_1596780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596780 prefixEnd_1596780 := by exact prefixLift 1596780
  have htrace : WordTrace (prefixWord ++ tailWord_1596780) baseStart_1596780 baseEnd_1596780 := by
    simpa [prefixWord, tailWord_1596780, baseEnd_1596780] using wordTrace_append hprefix tailTrace_1596780
  have hstable : (prefixWord ++ tailWord_1596780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596780).length < 2 ^ (prefixWord ++ tailWord_1596780).sum := by decide
  have hdescent : baseEnd_1596780 < baseStart_1596780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596794 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_1596794 : Nat := 118140960795 + 1596794 * 2 ^ 59
def prefixEnd_1596794 : Nat := 4983230072969 + 3 ^ 40 * 1596794 * 2
def baseEnd_1596794 : Nat := 364410145873569231036215

theorem tailTrace_1596794 : CollatzResearch.WordTrace tailWord_1596794 prefixEnd_1596794 364410145873569231036215 := by
  unfold tailWord_1596794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14559965444273880887175359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38826574518063682365800957 14559965444273880887175359)
  ·
    refine ⟨21839948166410821330763039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14559965444273880887175359 21839948166410821330763039)
    ·
      refine ⟨32759922249616231996144559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21839948166410821330763039 32759922249616231996144559)
      ·
        refine ⟨49139883374424347994216839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32759922249616231996144559 49139883374424347994216839)
        ·
          refine ⟨73709825061636521991325259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49139883374424347994216839 73709825061636521991325259)
          ·
            refine ⟨110564737592454782986987889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73709825061636521991325259 110564737592454782986987889)
            ·
              refine ⟨82923553194341087240240917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110564737592454782986987889 82923553194341087240240917)
              ·
                refine ⟨3887041555984738464386293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82923553194341087240240917 3887041555984738464386293)
                ·
                  refine ⟨364410145873569231036215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3887041555984738464386293 364410145873569231036215)
                  ·
                    rfl

theorem cell21_1596794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_1596794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596794 prefixEnd_1596794 := by exact prefixLift 1596794
  have htrace : WordTrace (prefixWord ++ tailWord_1596794) baseStart_1596794 baseEnd_1596794 := by
    simpa [prefixWord, tailWord_1596794, baseEnd_1596794] using wordTrace_append hprefix tailTrace_1596794
  have hstable : (prefixWord ++ tailWord_1596794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596794).length < 2 ^ (prefixWord ++ tailWord_1596794).sum := by decide
  have hdescent : baseEnd_1596794 < baseStart_1596794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596825 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 6]
def baseStart_1596825 : Nat := 118140960795 + 1596825 * 2 ^ 59
def prefixEnd_1596825 : Nat := 4983230072969 + 3 ^ 40 * 1596825 * 2
def baseEnd_1596825 : Nat := 364417220495920066019485

theorem tailTrace_1596825 : CollatzResearch.WordTrace tailWord_1596825 prefixEnd_1596825 364417220495920066019485 := by
  unfold tailWord_1596825
  simp only [CollatzResearch.WordTrace]
  refine ⟨58240992439983215843079929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38827328293322143895386619 58240992439983215843079929)
  ·
    refine ⟨43680744329987411882309947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58240992439983215843079929 43680744329987411882309947)
    ·
      refine ⟨65521116494981117823464921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43680744329987411882309947 65521116494981117823464921)
      ·
        refine ⟨49140837371235838367598691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65521116494981117823464921 49140837371235838367598691)
        ·
          refine ⟨73711256056853757551398037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49140837371235838367598691 73711256056853757551398037)
          ·
            refine ⟨3455215127665019885221783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73711256056853757551398037 3455215127665019885221783)
            ·
              refine ⟨5182822691497529827832675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455215127665019885221783 5182822691497529827832675)
              ·
                refine ⟨7774234037246294741749013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5182822691497529827832675 7774234037246294741749013)
                ·
                  refine ⟨364417220495920066019485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7774234037246294741749013 364417220495920066019485)
                  ·
                    rfl

theorem cell21_1596825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_1596825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596825 prefixEnd_1596825 := by exact prefixLift 1596825
  have htrace : WordTrace (prefixWord ++ tailWord_1596825) baseStart_1596825 baseEnd_1596825 := by
    simpa [prefixWord, tailWord_1596825, baseEnd_1596825] using wordTrace_append hprefix tailTrace_1596825
  have hstable : (prefixWord ++ tailWord_1596825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596825).length < 2 ^ (prefixWord ++ tailWord_1596825).sum := by decide
  have hdescent : baseEnd_1596825 < baseStart_1596825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596856 : List Nat := [2, 1, 2, 1, 2, 2, 6, 5]
def baseStart_1596856 : Nat := 118140960795 + 1596856 * 2 ^ 59
def prefixEnd_1596856 : Nat := 4983230072969 + 3 ^ 40 * 1596856 * 2
def baseEnd_1596856 : Nat := 121474765039423633667585

theorem tailTrace_1596856 : CollatzResearch.WordTrace tailWord_1596856 prefixEnd_1596856 121474765039423633667585 := by
  unfold tailWord_1596856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29121061551435454068729211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38828082068580605424972281 29121061551435454068729211)
  ·
    refine ⟨43681592327153181103093817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29121061551435454068729211 43681592327153181103093817)
    ·
      refine ⟨32761194245364885827320363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43681592327153181103093817 32761194245364885827320363)
      ·
        refine ⟨49141791368047328740980545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32761194245364885827320363 49141791368047328740980545)
        ·
          refine ⟨36856343526035496555735409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49141791368047328740980545 36856343526035496555735409)
          ·
            refine ⟨27642257644526622416801557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36856343526035496555735409 27642257644526622416801557)
            ·
              refine ⟨1295730827087185425787573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27642257644526622416801557 1295730827087185425787573)
              ·
                refine ⟨121474765039423633667585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1295730827087185425787573 121474765039423633667585)
                ·
                  rfl

theorem cell21_1596856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_1596856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596856 prefixEnd_1596856 := by exact prefixLift 1596856
  have htrace : WordTrace (prefixWord ++ tailWord_1596856) baseStart_1596856 baseEnd_1596856 := by
    simpa [prefixWord, tailWord_1596856, baseEnd_1596856] using wordTrace_append hprefix tailTrace_1596856
  have hstable : (prefixWord ++ tailWord_1596856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596856).length < 2 ^ (prefixWord ++ tailWord_1596856).sum := by decide
  have hdescent : baseEnd_1596856 < baseStart_1596856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596887 : List Nat := [1, 1, 3, 2, 1, 1, 1, 8, 3]
def baseStart_1596887 : Nat := 118140960795 + 1596887 * 2 ^ 59
def prefixEnd_1596887 : Nat := 4983230072969 + 3 ^ 40 * 1596887 * 2
def baseEnd_1596887 : Nat := 364431369740621735986025

theorem tailTrace_1596887 : CollatzResearch.WordTrace tailWord_1596887 prefixEnd_1596887 364431369740621735986025 := by
  unfold tailWord_1596887
  simp only [CollatzResearch.WordTrace]
  refine ⟨58243253765758600431836915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38828835843839066954557943 58243253765758600431836915)
  ·
    refine ⟨87364880648637900647755373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58243253765758600431836915 87364880648637900647755373)
    ·
      refine ⟨32761830243239212742908265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87364880648637900647755373 32761830243239212742908265)
      ·
        refine ⟨24571372682429409557181199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32761830243239212742908265 24571372682429409557181199)
        ·
          refine ⟨36857059023644114335771799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24571372682429409557181199 36857059023644114335771799)
          ·
            refine ⟨55285588535466171503657699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36857059023644114335771799 55285588535466171503657699)
            ·
              refine ⟨82928382803199257255486549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55285588535466171503657699 82928382803199257255486549)
              ·
                refine ⟨971816985974991295962733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 82928382803199257255486549 971816985974991295962733)
                ·
                  refine ⟨364431369740621735986025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971816985974991295962733 364431369740621735986025)
                  ·
                    rfl

theorem cell21_1596887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 3].length) (baseStart_1596887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596887 prefixEnd_1596887 := by exact prefixLift 1596887
  have htrace : WordTrace (prefixWord ++ tailWord_1596887) baseStart_1596887 baseEnd_1596887 := by
    simpa [prefixWord, tailWord_1596887, baseEnd_1596887] using wordTrace_append hprefix tailTrace_1596887
  have hstable : (prefixWord ++ tailWord_1596887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596887).length < 2 ^ (prefixWord ++ tailWord_1596887).sum := by decide
  have hdescent : baseEnd_1596887 < baseStart_1596887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596932 : List Nat := [2, 3, 2, 3, 2, 9]
def baseStart_1596932 : Nat := 118140960795 + 1596932 * 2 ^ 59
def prefixEnd_1596932 : Nat := 4983230072969 + 3 ^ 40 * 1596932 * 2
def baseEnd_1596932 : Nat := 13497838494581913249479

theorem tailTrace_1596932 : CollatzResearch.WordTrace tailWord_1596932 prefixEnd_1596932 13497838494581913249479 := by
  unfold tailWord_1596932
  simp only [CollatzResearch.WordTrace]
  refine ⟨29122447525297786558612525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38829930033730382078150033 29122447525297786558612525)
  ·
    refine ⟨10920917821986669959479697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29122447525297786558612525 10920917821986669959479697)
    ·
      refine ⟨8190688366490002469609773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10920917821986669959479697 8190688366490002469609773)
      ·
        refine ⟨3071508137433750926103665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8190688366490002469609773 3071508137433750926103665)
        ·
          refine ⟨2303631103075313194577749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3071508137433750926103665 2303631103075313194577749)
          ·
            refine ⟨13497838494581913249479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2303631103075313194577749 13497838494581913249479)
            ·
              rfl

theorem cell21_1596932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 9].length) (baseStart_1596932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596932 prefixEnd_1596932 := by exact prefixLift 1596932
  have htrace : WordTrace (prefixWord ++ tailWord_1596932) baseStart_1596932 baseEnd_1596932 := by
    simpa [prefixWord, tailWord_1596932, baseEnd_1596932] using wordTrace_append hprefix tailTrace_1596932
  have hstable : (prefixWord ++ tailWord_1596932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596932).length < 2 ^ (prefixWord ++ tailWord_1596932).sum := by decide
  have hdescent : baseEnd_1596932 < baseStart_1596932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596963 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 5]
def baseStart_1596963 : Nat := 118140960795 + 1596963 * 2 ^ 59
def prefixEnd_1596963 : Nat := 4983230072969 + 3 ^ 40 * 1596963 * 2
def baseEnd_1596963 : Nat := 364448713976062492719203

theorem tailTrace_1596963 : CollatzResearch.WordTrace tailWord_1596963 prefixEnd_1596963 364448713976062492719203 := by
  unfold tailWord_1596963
  simp only [CollatzResearch.WordTrace]
  refine ⟨58246025713483265411603543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38830683808988843607735695 58246025713483265411603543)
  ·
    refine ⟨87369038570224898117405315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58246025713483265411603543 87369038570224898117405315)
    ·
      refine ⟨131053557855337347176107973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87369038570224898117405315 131053557855337347176107973)
      ·
        refine ⟨24572542097875752595520245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131053557855337347176107973 24572542097875752595520245)
        ·
          refine ⟨2303675821675851805830023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24572542097875752595520245 2303675821675851805830023)
          ·
            refine ⟨3455513732513777708745035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303675821675851805830023 3455513732513777708745035)
            ·
              refine ⟨5183270598770666563117553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455513732513777708745035 5183270598770666563117553)
              ·
                refine ⟨3887452949077999922338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183270598770666563117553 3887452949077999922338165)
                ·
                  refine ⟨364448713976062492719203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3887452949077999922338165 364448713976062492719203)
                  ·
                    rfl

theorem cell21_1596963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_1596963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596963 prefixEnd_1596963 := by exact prefixLift 1596963
  have htrace : WordTrace (prefixWord ++ tailWord_1596963) baseStart_1596963 baseEnd_1596963 := by
    simpa [prefixWord, tailWord_1596963, baseEnd_1596963] using wordTrace_append hprefix tailTrace_1596963
  have hstable : (prefixWord ++ tailWord_1596963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596963).length < 2 ^ (prefixWord ++ tailWord_1596963).sum := by decide
  have hdescent : baseEnd_1596963 < baseStart_1596963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596991 : List Nat := [1, 1, 2, 2, 3, 4, 8]
def baseStart_1596991 : Nat := 118140960795 + 1596991 * 2 ^ 59
def prefixEnd_1596991 : Nat := 4983230072969 + 3 ^ 40 * 1596991 * 2
def baseEnd_1596991 : Nat := 40495011550837851805831

theorem tailTrace_1596991 : CollatzResearch.WordTrace tailWord_1596991 prefixEnd_1596991 40495011550837851805831 := by
  unfold tailWord_1596991
  simp only [CollatzResearch.WordTrace]
  refine ⟨58247046957381826193622827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38831364638254550795748551 58247046957381826193622827)
  ·
    refine ⟨87370570436072739290434241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58247046957381826193622827 87370570436072739290434241)
    ·
      refine ⟨65527927827054554467825681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87370570436072739290434241 65527927827054554467825681)
      ·
        refine ⟨49145945870290915850869261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65527927827054554467825681 49145945870290915850869261)
        ·
          refine ⟨18429729701359093444075973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49145945870290915850869261 18429729701359093444075973)
          ·
            refine ⟨3455574319004830020764245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18429729701359093444075973 3455574319004830020764245)
            ·
              refine ⟨40495011550837851805831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3455574319004830020764245 40495011550837851805831)
              ·
                rfl

theorem cell21_1596991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 8].length) (baseStart_1596991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1596991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1596991 prefixEnd_1596991 := by exact prefixLift 1596991
  have htrace : WordTrace (prefixWord ++ tailWord_1596991) baseStart_1596991 baseEnd_1596991 := by
    simpa [prefixWord, tailWord_1596991, baseEnd_1596991] using wordTrace_append hprefix tailTrace_1596991
  have hstable : (prefixWord ++ tailWord_1596991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596991).length < 2 ^ (prefixWord ++ tailWord_1596991).sum := by decide
  have hdescent : baseEnd_1596991 < baseStart_1596991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597053 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1597053 : Nat := 118140960795 + 1597053 * 2 ^ 59
def prefixEnd_1597053 : Nat := 4983230072969 + 3 ^ 40 * 1597053 * 2
def baseEnd_1597053 : Nat := 364469253202242336219019

theorem tailTrace_1597053 : CollatzResearch.WordTrace tailWord_1597053 prefixEnd_1597053 364469253202242336219019 := by
  unfold tailWord_1597053
  simp only [CollatzResearch.WordTrace]
  refine ⟨58249308283157210782379813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38832872188771473854919875 58249308283157210782379813)
  ·
    refine ⟨10921745303091977021696215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58249308283157210782379813 10921745303091977021696215)
    ·
      refine ⟨16382617954637965532544323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10921745303091977021696215 16382617954637965532544323)
      ·
        refine ⟨24573926931956948298816485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16382617954637965532544323 24573926931956948298816485)
        ·
          refine ⟨4607611299741927806028091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24573926931956948298816485 4607611299741927806028091)
          ·
            refine ⟨6911416949612891709042137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607611299741927806028091 6911416949612891709042137)
            ·
              refine ⟨5183562712209668781781603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6911416949612891709042137 5183562712209668781781603)
              ·
                refine ⟨7775344068314503172672405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183562712209668781781603 7775344068314503172672405)
                ·
                  refine ⟨364469253202242336219019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7775344068314503172672405 364469253202242336219019)
                  ·
                    rfl

theorem cell21_1597053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1597053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597053 prefixEnd_1597053 := by exact prefixLift 1597053
  have htrace : WordTrace (prefixWord ++ tailWord_1597053) baseStart_1597053 baseEnd_1597053 := by
    simpa [prefixWord, tailWord_1597053, baseEnd_1597053] using wordTrace_append hprefix tailTrace_1597053
  have hstable : (prefixWord ++ tailWord_1597053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597053).length < 2 ^ (prefixWord ++ tailWord_1597053).sum := by decide
  have hdescent : baseEnd_1597053 < baseStart_1597053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597056 : List Nat := [2, 1, 1, 2, 1, 4, 5, 2, 3]
def baseStart_1597056 : Nat := 118140960795 + 1597056 * 2 ^ 59
def prefixEnd_1597056 : Nat := 4983230072969 + 3 ^ 40 * 1597056 * 2
def baseEnd_1597056 : Nat := 364469937843114997669013

theorem tailTrace_1597056 : CollatzResearch.WordTrace tailWord_1597056 prefixEnd_1597056 364469937843114997669013 := by
  unfold tailWord_1597056
  simp only [CollatzResearch.WordTrace]
  refine ⟨29124708851073171147369511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38832945134764228196492681 29124708851073171147369511)
  ·
    refine ⟨43687063276609756721054267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29124708851073171147369511 43687063276609756721054267)
    ·
      refine ⟨65530594914914635081581401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43687063276609756721054267 65530594914914635081581401)
      ·
        refine ⟨49147946186185976311186051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65530594914914635081581401 49147946186185976311186051)
        ·
          refine ⟨73721919279278964466779077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49147946186185976311186051 73721919279278964466779077)
          ·
            refine ⟨13822859864864805837521077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73721919279278964466779077 13822859864864805837521077)
            ·
              refine ⟨1295893112331075547267601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13822859864864805837521077 1295893112331075547267601)
              ·
                refine ⟨971919834248306660450701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295893112331075547267601 971919834248306660450701)
                ·
                  refine ⟨364469937843114997669013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971919834248306660450701 364469937843114997669013)
                  ·
                    rfl

theorem cell21_1597056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_1597056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597056 prefixEnd_1597056 := by exact prefixLift 1597056
  have htrace : WordTrace (prefixWord ++ tailWord_1597056) baseStart_1597056 baseEnd_1597056 := by
    simpa [prefixWord, tailWord_1597056, baseEnd_1597056] using wordTrace_append hprefix tailTrace_1597056
  have hstable : (prefixWord ++ tailWord_1597056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597056).length < 2 ^ (prefixWord ++ tailWord_1597056).sum := by decide
  have hdescent : baseEnd_1597056 < baseStart_1597056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597067 : List Nat := [1, 1, 1, 1, 4, 1, 6, 6]
def baseStart_1597067 : Nat := 118140960795 + 1597067 * 2 ^ 59
def prefixEnd_1597067 : Nat := 4983230072969 + 3 ^ 40 * 1597067 * 2
def baseEnd_1597067 : Nat := 121490816064327140995219

theorem tailTrace_1597067 : CollatzResearch.WordTrace tailWord_1597067 prefixEnd_1597067 121490816064327140995219 := by
  unfold tailWord_1597067
  simp only [CollatzResearch.WordTrace]
  refine ⟨58249818905106491173389455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38833212603404327448926303 58249818905106491173389455)
  ·
    refine ⟨87374728357659736760084183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58249818905106491173389455 87374728357659736760084183)
    ·
      refine ⟨131062092536489605140126275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87374728357659736760084183 131062092536489605140126275)
      ·
        refine ⟨196593138804734407710189413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131062092536489605140126275 196593138804734407710189413)
        ·
          refine ⟨36861213525887701445660515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196593138804734407710189413 36861213525887701445660515)
          ·
            refine ⟨55291820288831552168490773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36861213525887701445660515 55291820288831552168490773)
            ·
              refine ⟨2591804076038979007898005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55291820288831552168490773 2591804076038979007898005)
              ·
                refine ⟨121490816064327140995219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2591804076038979007898005 121490816064327140995219)
                ·
                  rfl

theorem cell21_1597067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 6].length) (baseStart_1597067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597067 prefixEnd_1597067 := by exact prefixLift 1597067
  have htrace : WordTrace (prefixWord ++ tailWord_1597067) baseStart_1597067 baseEnd_1597067 := by
    simpa [prefixWord, tailWord_1597067, baseEnd_1597067] using wordTrace_append hprefix tailTrace_1597067
  have hstable : (prefixWord ++ tailWord_1597067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597067).length < 2 ^ (prefixWord ++ tailWord_1597067).sum := by decide
  have hdescent : baseEnd_1597067 < baseStart_1597067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597070 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_1597070 : Nat := 118140960795 + 1597070 * 2 ^ 59
def prefixEnd_1597070 : Nat := 4983230072969 + 3 ^ 40 * 1597070 * 2
def baseEnd_1597070 : Nat := 364473132833854084435651

theorem tailTrace_1597070 : CollatzResearch.WordTrace tailWord_1597070 prefixEnd_1597070 364473132833854084435651 := by
  unfold tailWord_1597070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7281241040511952835718583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38833285549397081790499109 7281241040511952835718583)
  ·
    refine ⟨10921861560767929253577875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7281241040511952835718583 10921861560767929253577875)
    ·
      refine ⟨16382792341151893880366813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10921861560767929253577875 16382792341151893880366813)
      ·
        refine ⟨6143547127931960205137555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16382792341151893880366813 6143547127931960205137555)
        ·
          refine ⟨9215320691897940307706333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143547127931960205137555 9215320691897940307706333)
          ·
            refine ⟨3455745259461727615389875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9215320691897940307706333 3455745259461727615389875)
            ·
              refine ⟨5183617889192591423084813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455745259461727615389875 5183617889192591423084813)
              ·
                refine ⟨1943856708447221783656805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5183617889192591423084813 1943856708447221783656805)
                ·
                  refine ⟨364473132833854084435651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943856708447221783656805 364473132833854084435651)
                  ·
                    rfl

theorem cell21_1597070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_1597070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597070 prefixEnd_1597070 := by exact prefixLift 1597070
  have htrace : WordTrace (prefixWord ++ tailWord_1597070) baseStart_1597070 baseEnd_1597070 := by
    simpa [prefixWord, tailWord_1597070, baseEnd_1597070] using wordTrace_append hprefix tailTrace_1597070
  have hstable : (prefixWord ++ tailWord_1597070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597070).length < 2 ^ (prefixWord ++ tailWord_1597070).sum := by decide
  have hdescent : baseEnd_1597070 < baseStart_1597070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597112 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_1597112 : Nat := 118140960795 + 1597112 * 2 ^ 59
def prefixEnd_1597112 : Nat := 4983230072969 + 3 ^ 40 * 1597112 * 2
def baseEnd_1597112 : Nat := 364482717806071344735565

theorem tailTrace_1597112 : CollatzResearch.WordTrace tailWord_1597112 prefixEnd_1597112 364482717806071344735565 := by
  unfold tailWord_1597112
  simp only [CollatzResearch.WordTrace]
  refine ⟨29125730094971731929388795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38834306793295642572518393 29125730094971731929388795)
  ·
    refine ⟨43688595142457597894083193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29125730094971731929388795 43688595142457597894083193)
    ·
      refine ⟨32766446356843198420562395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43688595142457597894083193 32766446356843198420562395)
      ·
        refine ⟨49149669535264797630843593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32766446356843198420562395 49149669535264797630843593)
        ·
          refine ⟨36862252151448598223132695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49149669535264797630843593 36862252151448598223132695)
          ·
            refine ⟨55293378227172897334699043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36862252151448598223132695 55293378227172897334699043)
            ·
              refine ⟨82940067340759346002048565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55293378227172897334699043 82940067340759346002048565)
              ·
                refine ⟨7775631313196188687692053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82940067340759346002048565 7775631313196188687692053)
                ·
                  refine ⟨364482717806071344735565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7775631313196188687692053 364482717806071344735565)
                  ·
                    rfl

theorem cell21_1597112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_1597112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597112 prefixEnd_1597112 := by exact prefixLift 1597112
  have htrace : WordTrace (prefixWord ++ tailWord_1597112) baseStart_1597112 baseEnd_1597112 := by
    simpa [prefixWord, tailWord_1597112, baseEnd_1597112] using wordTrace_append hprefix tailTrace_1597112
  have hstable : (prefixWord ++ tailWord_1597112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597112).length < 2 ^ (prefixWord ++ tailWord_1597112).sum := by decide
  have hdescent : baseEnd_1597112 < baseStart_1597112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597236 : List Nat := [2, 5, 1, 1, 2, 1, 1, 8]
def baseStart_1597236 : Nat := 118140960795 + 1597236 * 2 ^ 59
def prefixEnd_1597236 : Nat := 4983230072969 + 3 ^ 40 * 1597236 * 2
def baseEnd_1597236 : Nat := 121503672098491561556215

theorem tailTrace_1597236 : CollatzResearch.WordTrace tailWord_1597236 prefixEnd_1597236 121503672098491561556215 := by
  unfold tailWord_1597236
  simp only [CollatzResearch.WordTrace]
  refine ⟨29127991420747116518145781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38837321894329488690861041 29127991420747116518145781)
  ·
    refine ⟨2730749195695042173576167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29127991420747116518145781 2730749195695042173576167)
    ·
      refine ⟨4096123793542563260364251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2730749195695042173576167 4096123793542563260364251)
      ·
        refine ⟨6144185690313844890546377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4096123793542563260364251 6144185690313844890546377)
        ·
          refine ⟨4608139267735383667909783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6144185690313844890546377 4608139267735383667909783)
          ·
            refine ⟨6912208901603075501864675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608139267735383667909783 6912208901603075501864675)
            ·
              refine ⟨10368313352404613252797013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912208901603075501864675 10368313352404613252797013)
              ·
                refine ⟨121503672098491561556215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10368313352404613252797013 121503672098491561556215)
                ·
                  rfl

theorem cell21_1597236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_1597236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597236 prefixEnd_1597236 := by exact prefixLift 1597236
  have htrace : WordTrace (prefixWord ++ tailWord_1597236) baseStart_1597236 baseEnd_1597236 := by
    simpa [prefixWord, tailWord_1597236, baseEnd_1597236] using wordTrace_append hprefix tailTrace_1597236
  have hstable : (prefixWord ++ tailWord_1597236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597236).length < 2 ^ (prefixWord ++ tailWord_1597236).sum := by decide
  have hdescent : baseEnd_1597236 < baseStart_1597236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597281 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 4]
def baseStart_1597281 : Nat := 118140960795 + 1597281 * 2 ^ 59
def prefixEnd_1597281 : Nat := 4983230072969 + 3 ^ 40 * 1597281 * 2
def baseEnd_1597281 : Nat := 364521285908564606418553

theorem tailTrace_1597281 : CollatzResearch.WordTrace tailWord_1597281 prefixEnd_1597281 364521285908564606418553 := by
  unfold tailWord_1597281
  simp only [CollatzResearch.WordTrace]
  refine ⟨58257624126331205721679697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38838416084220803814453131 58257624126331205721679697)
  ·
    refine ⟨43693218094748404291259773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58257624126331205721679697 43693218094748404291259773)
    ·
      refine ⟨16384956785530651609222415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43693218094748404291259773 16384956785530651609222415)
      ·
        refine ⟨24577435178295977413833623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16384956785530651609222415 24577435178295977413833623)
        ·
          refine ⟨36866152767443966120750435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24577435178295977413833623 36866152767443966120750435)
          ·
            refine ⟨55299229151165949181125653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36866152767443966120750435 55299229151165949181125653)
            ·
              refine ⟨2592151366460903867865265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55299229151165949181125653 2592151366460903867865265)
              ·
                refine ⟨1944113524845677900898949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592151366460903867865265 1944113524845677900898949)
                ·
                  refine ⟨364521285908564606418553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944113524845677900898949 364521285908564606418553)
                  ·
                    rfl

theorem cell21_1597281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_1597281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597281 prefixEnd_1597281 := by exact prefixLift 1597281
  have htrace : WordTrace (prefixWord ++ tailWord_1597281) baseStart_1597281 baseEnd_1597281 := by
    simpa [prefixWord, tailWord_1597281, baseEnd_1597281] using wordTrace_append hprefix tailTrace_1597281
  have hstable : (prefixWord ++ tailWord_1597281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597281).length < 2 ^ (prefixWord ++ tailWord_1597281).sum := by decide
  have hdescent : baseEnd_1597281 < baseStart_1597281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597284 : List Nat := [2, 3, 1, 1, 5, 1, 1, 4, 3]
def baseStart_1597284 : Nat := 118140960795 + 1597284 * 2 ^ 59
def prefixEnd_1597284 : Nat := 4983230072969 + 3 ^ 40 * 1597284 * 2
def baseEnd_1597284 : Nat := 364521970549437267868547

theorem tailTrace_1597284 : CollatzResearch.WordTrace tailWord_1597284 prefixEnd_1597284 364521970549437267868547 := by
  unfold tailWord_1597284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29128866772660168617019453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38838489030213558156025937 29128866772660168617019453)
  ·
    refine ⟨10923325039747563231382295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29128866772660168617019453 10923325039747563231382295)
    ·
      refine ⟨16384987559621344847073443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10923325039747563231382295 16384987559621344847073443)
      ·
        refine ⟨24577481339432017270610165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16384987559621344847073443 24577481339432017270610165)
        ·
          refine ⟨2304138875571751619119703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24577481339432017270610165 2304138875571751619119703)
          ·
            refine ⟨3456208313357627428679555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304138875571751619119703 3456208313357627428679555)
            ·
              refine ⟨5184312470036441143019333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456208313357627428679555 5184312470036441143019333)
              ·
                refine ⟨972058588131832714316125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5184312470036441143019333 972058588131832714316125)
                ·
                  refine ⟨364521970549437267868547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972058588131832714316125 364521970549437267868547)
                  ·
                    rfl

theorem cell21_1597284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_1597284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597284 prefixEnd_1597284 := by exact prefixLift 1597284
  have htrace : WordTrace (prefixWord ++ tailWord_1597284) baseStart_1597284 baseEnd_1597284 := by
    simpa [prefixWord, tailWord_1597284, baseEnd_1597284] using wordTrace_append hprefix tailTrace_1597284
  have hstable : (prefixWord ++ tailWord_1597284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597284).length < 2 ^ (prefixWord ++ tailWord_1597284).sum := by decide
  have hdescent : baseEnd_1597284 < baseStart_1597284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597343 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 5]
def baseStart_1597343 : Nat := 118140960795 + 1597343 * 2 ^ 59
def prefixEnd_1597343 : Nat := 4983230072969 + 3 ^ 40 * 1597343 * 2
def baseEnd_1597343 : Nat := 364535435153266276385093

theorem tailTrace_1597343 : CollatzResearch.WordTrace tailWord_1597343 prefixEnd_1597343 364535435153266276385093 := by
  unfold tailWord_1597343
  simp only [CollatzResearch.WordTrace]
  refine ⟨58259885452106590310436683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38839923634737726873624455 58259885452106590310436683)
  ·
    refine ⟨87389828178159885465655025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58259885452106590310436683 87389828178159885465655025)
    ·
      refine ⟨65542371133619914099241269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87389828178159885465655025 65542371133619914099241269)
      ·
        refine ⟨6144597293776866946803869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65542371133619914099241269 6144597293776866946803869)
        ·
          refine ⟨2304223985166325105051451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6144597293776866946803869 2304223985166325105051451)
          ·
            refine ⟨3456335977749487657577177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304223985166325105051451 3456335977749487657577177)
            ·
              refine ⟨2592251983312115743182883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456335977749487657577177 2592251983312115743182883)
              ·
                refine ⟨3888377974968173614774325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592251983312115743182883 3888377974968173614774325)
                ·
                  refine ⟨364535435153266276385093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3888377974968173614774325 364535435153266276385093)
                  ·
                    rfl

theorem cell21_1597343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_1597343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597343 prefixEnd_1597343 := by exact prefixLift 1597343
  have htrace : WordTrace (prefixWord ++ tailWord_1597343) baseStart_1597343 baseEnd_1597343 := by
    simpa [prefixWord, tailWord_1597343, baseEnd_1597343] using wordTrace_append hprefix tailTrace_1597343
  have hstable : (prefixWord ++ tailWord_1597343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597343).length < 2 ^ (prefixWord ++ tailWord_1597343).sum := by decide
  have hdescent : baseEnd_1597343 < baseStart_1597343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597450 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1597450 : Nat := 118140960795 + 1597450 * 2 ^ 59
def prefixEnd_1597450 : Nat := 4983230072969 + 3 ^ 40 * 1597450 * 2
def baseEnd_1597450 : Nat := 364559854011057868101541

theorem tailTrace_1597450 : CollatzResearch.WordTrace tailWord_1597450 prefixEnd_1597450 364559854011057868101541 := by
  unfold tailWord_1597450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14565947015679736896145451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38842525375145965056387869 14565947015679736896145451)
  ·
    refine ⟨21848920523519605344218177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14565947015679736896145451 21848920523519605344218177)
    ·
      refine ⟨16386690392639704008163633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21848920523519605344218177 16386690392639704008163633)
      ·
        refine ⟨12290017794479778006122725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16386690392639704008163633 12290017794479778006122725)
        ·
          refine ⟨2304378336464958376148011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12290017794479778006122725 2304378336464958376148011)
          ·
            refine ⟨3456567504697437564222017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304378336464958376148011 3456567504697437564222017)
            ·
              refine ⟨2592425628523078173166513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456567504697437564222017 2592425628523078173166513)
              ·
                refine ⟨1944319221392308629874885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592425628523078173166513 1944319221392308629874885)
                ·
                  refine ⟨364559854011057868101541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944319221392308629874885 364559854011057868101541)
                  ·
                    rfl

theorem cell21_1597450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1597450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597450 prefixEnd_1597450 := by exact prefixLift 1597450
  have htrace : WordTrace (prefixWord ++ tailWord_1597450) baseStart_1597450 baseEnd_1597450 := by
    simpa [prefixWord, tailWord_1597450, baseEnd_1597450] using wordTrace_append hprefix tailTrace_1597450
  have hstable : (prefixWord ++ tailWord_1597450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597450).length < 2 ^ (prefixWord ++ tailWord_1597450).sum := by decide
  have hdescent : baseEnd_1597450 < baseStart_1597450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597568 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_1597568 : Nat := 118140960795 + 1597568 * 2 ^ 59
def prefixEnd_1597568 : Nat := 4983230072969 + 3 ^ 40 * 1597568 * 2
def baseEnd_1597568 : Nat := 364586783218715885134633

theorem tailTrace_1597568 : CollatzResearch.WordTrace tailWord_1597568 prefixEnd_1597568 364586783218715885134633 := by
  unfold tailWord_1597568
  simp only [CollatzResearch.WordTrace]
  refine ⟨29134045938145726868688679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38845394584194302491584905 29134045938145726868688679)
  ·
    refine ⟨43701068907218590303033019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29134045938145726868688679 43701068907218590303033019)
    ·
      refine ⟨65551603360827885454549529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43701068907218590303033019 65551603360827885454549529)
      ·
        refine ⟨49163702520620914090912147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65551603360827885454549529 49163702520620914090912147)
        ·
          refine ⟨73745553780931371136368221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49163702520620914090912147 73745553780931371136368221)
          ·
            refine ⟨27654582667849264176138083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73745553780931371136368221 27654582667849264176138083)
            ·
              refine ⟨41481874001773896264207125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27654582667849264176138083 41481874001773896264207125)
              ·
                refine ⟨1944462843833151387384709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41481874001773896264207125 1944462843833151387384709)
                ·
                  refine ⟨364586783218715885134633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944462843833151387384709 364586783218715885134633)
                  ·
                    rfl

theorem cell21_1597568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_1597568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597568 prefixEnd_1597568 := by exact prefixLift 1597568
  have htrace : WordTrace (prefixWord ++ tailWord_1597568) baseStart_1597568 baseEnd_1597568 := by
    simpa [prefixWord, tailWord_1597568, baseEnd_1597568] using wordTrace_append hprefix tailTrace_1597568
  have hstable : (prefixWord ++ tailWord_1597568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597568).length < 2 ^ (prefixWord ++ tailWord_1597568).sum := by decide
  have hdescent : baseEnd_1597568 < baseStart_1597568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597599 : List Nat := [1, 1, 2, 6, 1, 1, 2, 7]
def baseStart_1597599 : Nat := 118140960795 + 1597599 * 2 ^ 59
def prefixEnd_1597599 : Nat := 4983230072969 + 3 ^ 40 * 1597599 * 2
def baseEnd_1597599 : Nat := 121531285947022240039301

theorem tailTrace_1597599 : CollatzResearch.WordTrace tailWord_1597599 prefixEnd_1597599 121531285947022240039301 := by
  unfold tailWord_1597599
  simp only [CollatzResearch.WordTrace]
  refine ⟨58269222539179146031755851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38846148359452764021170567 58269222539179146031755851)
  ·
    refine ⟨87403833808768719047633777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58269222539179146031755851 87403833808768719047633777)
    ·
      refine ⟨65552875356576539285725333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87403833808768719047633777 65552875356576539285725333)
      ·
        refine ⟨3072791032339525279018375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65552875356576539285725333 3072791032339525279018375)
        ·
          refine ⟨4609186548509287918527563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072791032339525279018375 4609186548509287918527563)
          ·
            refine ⟨6913779822763931877791345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609186548509287918527563 6913779822763931877791345)
            ·
              refine ⟨5185334867072948908343509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6913779822763931877791345 5185334867072948908343509)
              ·
                refine ⟨121531285947022240039301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5185334867072948908343509 121531285947022240039301)
                ·
                  rfl

theorem cell21_1597599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 7].length) (baseStart_1597599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597599 prefixEnd_1597599 := by exact prefixLift 1597599
  have htrace : WordTrace (prefixWord ++ tailWord_1597599) baseStart_1597599 baseEnd_1597599 := by
    simpa [prefixWord, tailWord_1597599, baseEnd_1597599] using wordTrace_append hprefix tailTrace_1597599
  have hstable : (prefixWord ++ tailWord_1597599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597599).length < 2 ^ (prefixWord ++ tailWord_1597599).sum := by decide
  have hdescent : baseEnd_1597599 < baseStart_1597599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597633 : List Nat := [1, 2, 6, 1, 2, 2, 1, 6]
def baseStart_1597633 : Nat := 118140960795 + 1597633 * 2 ^ 59
def prefixEnd_1597633 : Nat := 4983230072969 + 3 ^ 40 * 1597633 * 2
def baseEnd_1597633 : Nat := 121533872368096738850389

theorem tailTrace_1597633 : CollatzResearch.WordTrace tailWord_1597633 prefixEnd_1597633 121533872368096738850389 := by
  unfold tailWord_1597633
  simp only [CollatzResearch.WordTrace]
  refine ⟨58270462621055969838493553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38846975080703979892329035 58270462621055969838493553)
  ·
    refine ⟨43702846965791977378870165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58270462621055969838493553 43702846965791977378870165)
    ·
      refine ⟨2048570951521498939634539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43702846965791977378870165 2048570951521498939634539)
      ·
        refine ⟨3072856427282248409451809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048570951521498939634539 3072856427282248409451809)
        ·
          refine ⟨2304642320461686307088857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3072856427282248409451809 2304642320461686307088857)
          ·
            refine ⟨1728481740346264730316643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2304642320461686307088857 1728481740346264730316643)
            ·
              refine ⟨2592722610519397095474965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728481740346264730316643 2592722610519397095474965)
              ·
                refine ⟨121533872368096738850389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2592722610519397095474965 121533872368096738850389)
                ·
                  rfl

theorem cell21_1597633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 6].length) (baseStart_1597633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597633 prefixEnd_1597633 := by exact prefixLift 1597633
  have htrace : WordTrace (prefixWord ++ tailWord_1597633) baseStart_1597633 baseEnd_1597633 := by
    simpa [prefixWord, tailWord_1597633, baseEnd_1597633] using wordTrace_append hprefix tailTrace_1597633
  have hstable : (prefixWord ++ tailWord_1597633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597633).length < 2 ^ (prefixWord ++ tailWord_1597633).sum := by decide
  have hdescent : baseEnd_1597633 < baseStart_1597633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597658 : List Nat := [3, 1, 1, 2, 2, 1, 2, 9]
def baseStart_1597658 : Nat := 118140960795 + 1597658 * 2 ^ 59
def prefixEnd_1597658 : Nat := 4983230072969 + 3 ^ 40 * 1597658 * 2
def baseEnd_1597658 : Nat := 121535774148298576211483

theorem tailTrace_1597658 : CollatzResearch.WordTrace tailWord_1597658 prefixEnd_1597658 121535774148298576211483 := by
  unfold tailWord_1597658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14567843611491349777038407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38847582963976932738769085 14567843611491349777038407)
  ·
    refine ⟨21851765417237024665557611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14567843611491349777038407 21851765417237024665557611)
    ·
      refine ⟨32777648125855536998336417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21851765417237024665557611 32777648125855536998336417)
      ·
        refine ⟨24583236094391652748752313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32777648125855536998336417 24583236094391652748752313)
        ·
          refine ⟨18437427070793739561564235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24583236094391652748752313 18437427070793739561564235)
          ·
            refine ⟨27656140606190609342346353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18437427070793739561564235 27656140606190609342346353)
            ·
              refine ⟨20742105454642957006759765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27656140606190609342346353 20742105454642957006759765)
              ·
                refine ⟨121535774148298576211483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20742105454642957006759765 121535774148298576211483)
                ·
                  rfl

theorem cell21_1597658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_1597658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597658 prefixEnd_1597658 := by exact prefixLift 1597658
  have htrace : WordTrace (prefixWord ++ tailWord_1597658) baseStart_1597658 baseEnd_1597658 := by
    simpa [prefixWord, tailWord_1597658, baseEnd_1597658] using wordTrace_append hprefix tailTrace_1597658
  have hstable : (prefixWord ++ tailWord_1597658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597658).length < 2 ^ (prefixWord ++ tailWord_1597658).sum := by decide
  have hdescent : baseEnd_1597658 < baseStart_1597658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597754 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_1597754 : Nat := 118140960795 + 1597754 * 2 ^ 59
def prefixEnd_1597754 : Nat := 4983230072969 + 3 ^ 40 * 1597754 * 2
def baseEnd_1597754 : Nat := 364629230952820895034253

theorem tailTrace_1597754 : CollatzResearch.WordTrace tailWord_1597754 prefixEnd_1597754 364629230952820895034253 := by
  unfold tailWord_1597754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14568718963404401875912079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38849917235745071669098877 14568718963404401875912079)
  ·
    refine ⟨21853078445106602813868119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14568718963404401875912079 21853078445106602813868119)
    ·
      refine ⟨32779617667659904220802179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21853078445106602813868119 32779617667659904220802179)
      ·
        refine ⟨49169426501489856331203269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32779617667659904220802179 49169426501489856331203269)
        ·
          refine ⟨9219267469029348062100613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49169426501489856331203269 9219267469029348062100613)
          ·
            refine ⟨1728612650443002761643865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9219267469029348062100613 1728612650443002761643865)
            ·
              refine ⟨1296459487832252071232899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728612650443002761643865 1296459487832252071232899)
              ·
                refine ⟨1944689231748378106849349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296459487832252071232899 1944689231748378106849349)
                ·
                  refine ⟨364629230952820895034253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944689231748378106849349 364629230952820895034253)
                  ·
                    rfl

theorem cell21_1597754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_1597754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597754 prefixEnd_1597754 := by exact prefixLift 1597754
  have htrace : WordTrace (prefixWord ++ tailWord_1597754) baseStart_1597754 baseEnd_1597754 := by
    simpa [prefixWord, tailWord_1597754, baseEnd_1597754] using wordTrace_append hprefix tailTrace_1597754
  have hstable : (prefixWord ++ tailWord_1597754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597754).length < 2 ^ (prefixWord ++ tailWord_1597754).sum := by decide
  have hdescent : baseEnd_1597754 < baseStart_1597754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597779 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 6]
def baseStart_1597779 : Nat := 118140960795 + 1597779 * 2 ^ 59
def prefixEnd_1597779 : Nat := 4983230072969 + 3 ^ 40 * 1597779 * 2
def baseEnd_1597779 : Nat := 364634936293426407117535

theorem tailTrace_1597779 : CollatzResearch.WordTrace tailWord_1597779 prefixEnd_1597779 364634936293426407117535 := by
  unfold tailWord_1597779
  simp only [CollatzResearch.WordTrace]
  refine ⟨58275787678527036773308391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38850525119018024515538927 58275787678527036773308391)
  ·
    refine ⟨87413681517790555159962587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58275787678527036773308391 87413681517790555159962587)
    ·
      refine ⟨131120522276685832739943881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87413681517790555159962587 131120522276685832739943881)
      ·
        refine ⟨98340391707514374554957911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131120522276685832739943881 98340391707514374554957911)
        ·
          refine ⟨147510587561271561832436867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98340391707514374554957911 147510587561271561832436867)
          ·
            refine ⟨221265881341907342748655301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147510587561271561832436867 221265881341907342748655301)
            ·
              refine ⟨41487352751607626765372869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221265881341907342748655301 41487352751607626765372869)
              ·
                refine ⟨7778878640926430018507413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41487352751607626765372869 7778878640926430018507413)
                ·
                  refine ⟨364634936293426407117535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7778878640926430018507413 364634936293426407117535)
                  ·
                    rfl

theorem cell21_1597779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_1597779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597779 prefixEnd_1597779 := by exact prefixLift 1597779
  have htrace : WordTrace (prefixWord ++ tailWord_1597779) baseStart_1597779 baseEnd_1597779 := by
    simpa [prefixWord, tailWord_1597779, baseEnd_1597779] using wordTrace_append hprefix tailTrace_1597779
  have hstable : (prefixWord ++ tailWord_1597779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597779).length < 2 ^ (prefixWord ++ tailWord_1597779).sum := by decide
  have hdescent : baseEnd_1597779 < baseStart_1597779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597799 : List Nat := [1, 1, 5, 1, 3, 2, 1, 4, 3]
def baseStart_1597799 : Nat := 118140960795 + 1597799 * 2 ^ 59
def prefixEnd_1597799 : Nat := 4983230072969 + 3 ^ 40 * 1597799 * 2
def baseEnd_1597799 : Nat := 364639500565910816784161

theorem tailTrace_1597799 : CollatzResearch.WordTrace tailWord_1597799 prefixEnd_1597799 364639500565910816784161 := by
  unfold tailWord_1597799
  simp only [CollatzResearch.WordTrace]
  refine ⟨58276517138454580189036451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38851011425636386792690967 58276517138454580189036451)
  ·
    refine ⟨87414775707681870283554677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58276517138454580189036451 87414775707681870283554677)
    ·
      refine ⟨8195135222595175339083251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87414775707681870283554677 8195135222595175339083251)
      ·
        refine ⟨12292702833892763008624877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8195135222595175339083251 12292702833892763008624877)
        ·
          refine ⟨4609763562709786128234329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12292702833892763008624877 4609763562709786128234329)
          ·
            refine ⟨3457322672032339596175747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4609763562709786128234329 3457322672032339596175747)
            ·
              refine ⟨5185984008048509394263621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457322672032339596175747 5185984008048509394263621)
              ·
                refine ⟨972372001509095511424429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5185984008048509394263621 972372001509095511424429)
                ·
                  refine ⟨364639500565910816784161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972372001509095511424429 364639500565910816784161)
                  ·
                    rfl

theorem cell21_1597799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 3].length) (baseStart_1597799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597799 prefixEnd_1597799 := by exact prefixLift 1597799
  have htrace : WordTrace (prefixWord ++ tailWord_1597799) baseStart_1597799 baseEnd_1597799 := by
    simpa [prefixWord, tailWord_1597799, baseEnd_1597799] using wordTrace_append hprefix tailTrace_1597799
  have hstable : (prefixWord ++ tailWord_1597799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597799).length < 2 ^ (prefixWord ++ tailWord_1597799).sum := by decide
  have hdescent : baseEnd_1597799 < baseStart_1597799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597813 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 4]
def baseStart_1597813 : Nat := 118140960795 + 1597813 * 2 ^ 59
def prefixEnd_1597813 : Nat := 4983230072969 + 3 ^ 40 * 1597813 * 2
def baseEnd_1597813 : Nat := 364642695556649903550799

theorem tailTrace_1597813 : CollatzResearch.WordTrace tailWord_1597813 prefixEnd_1597813 364642695556649903550799 := by
  unfold tailWord_1597813
  simp only [CollatzResearch.WordTrace]
  refine ⟨58277027760403860580046093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38851351840269240386697395 58277027760403860580046093)
  ·
    refine ⟨21853885410151447717517285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58277027760403860580046093 21853885410151447717517285)
    ·
      refine ⟨4097603514403396447034491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21853885410151447717517285 4097603514403396447034491)
      ·
        refine ⟨6146405271605094670551737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097603514403396447034491 6146405271605094670551737)
        ·
          refine ⟨4609803953703821002913803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6146405271605094670551737 4609803953703821002913803)
          ·
            refine ⟨6914705930555731504370705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609803953703821002913803 6914705930555731504370705)
            ·
              refine ⟨5186029447916798628278029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6914705930555731504370705 5186029447916798628278029)
              ·
                refine ⟨1944761042968799485604261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5186029447916798628278029 1944761042968799485604261)
                ·
                  refine ⟨364642695556649903550799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944761042968799485604261 364642695556649903550799)
                  ·
                    rfl

theorem cell21_1597813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_1597813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597813 prefixEnd_1597813 := by exact prefixLift 1597813
  have htrace : WordTrace (prefixWord ++ tailWord_1597813) baseStart_1597813 baseEnd_1597813 := by
    simpa [prefixWord, tailWord_1597813, baseEnd_1597813] using wordTrace_append hprefix tailTrace_1597813
  have hstable : (prefixWord ++ tailWord_1597813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597813).length < 2 ^ (prefixWord ++ tailWord_1597813).sum := by decide
  have hdescent : baseEnd_1597813 < baseStart_1597813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597858 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1597858 : Nat := 118140960795 + 1597858 * 2 ^ 59
def prefixEnd_1597858 : Nat := 4983230072969 + 3 ^ 40 * 1597858 * 2
def baseEnd_1597858 : Nat := 364652965169739825300707

theorem tailTrace_1597858 : CollatzResearch.WordTrace tailWord_1597858 prefixEnd_1597858 364652965169739825300707 := by
  unfold tailWord_1597858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14569667261310208316358557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38852446030160555510289485 14569667261310208316358557)
  ·
    refine ⟨5463625222991328118634459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14569667261310208316358557 5463625222991328118634459)
    ·
      refine ⟨8195437834486992177951689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5463625222991328118634459 8195437834486992177951689)
      ·
        refine ⟨6146578375865244133463767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8195437834486992177951689 6146578375865244133463767)
        ·
          refine ⟨9219867563797866200195651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146578375865244133463767 9219867563797866200195651)
          ·
            refine ⟨13829801345696799300293477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219867563797866200195651 13829801345696799300293477)
            ·
              refine ⟨2593087752318149868805027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13829801345696799300293477 2593087752318149868805027)
              ·
                refine ⟨3889631628477224803207541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593087752318149868805027 3889631628477224803207541)
                ·
                  refine ⟨364652965169739825300707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3889631628477224803207541 364652965169739825300707)
                  ·
                    rfl

theorem cell21_1597858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1597858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597858 prefixEnd_1597858 := by exact prefixLift 1597858
  have htrace : WordTrace (prefixWord ++ tailWord_1597858) baseStart_1597858 baseEnd_1597858 := by
    simpa [prefixWord, tailWord_1597858, baseEnd_1597858] using wordTrace_append hprefix tailTrace_1597858
  have hstable : (prefixWord ++ tailWord_1597858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597858).length < 2 ^ (prefixWord ++ tailWord_1597858).sum := by decide
  have hdescent : baseEnd_1597858 < baseStart_1597858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597923 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 4]
def baseStart_1597923 : Nat := 118140960795 + 1597923 * 2 ^ 59
def prefixEnd_1597923 : Nat := 4983230072969 + 3 ^ 40 * 1597923 * 2
def baseEnd_1597923 : Nat := 364667799055314156717241

theorem tailTrace_1597923 : CollatzResearch.WordTrace tailWord_1597923 prefixEnd_1597923 364667799055314156717241 := by
  unfold tailWord_1597923
  simp only [CollatzResearch.WordTrace]
  refine ⟨58281039790005349366550423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38854026526670232911033615 58281039790005349366550423)
  ·
    refine ⟨87421559685008024049825635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58281039790005349366550423 87421559685008024049825635)
    ·
      refine ⟨131132339527512036074738453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87421559685008024049825635 131132339527512036074738453)
      ·
        refine ⟨6146828415352126691003365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131132339527512036074738453 6146828415352126691003365)
        ·
          refine ⟨1152530327878523754563131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6146828415352126691003365 1152530327878523754563131)
          ·
            refine ⟨1728795491817785631844697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152530327878523754563131 1728795491817785631844697)
            ·
              refine ⟨1296596618863339223883523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728795491817785631844697 1296596618863339223883523)
              ·
                refine ⟨1944894928295008835825285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296596618863339223883523 1944894928295008835825285)
                ·
                  refine ⟨364667799055314156717241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944894928295008835825285 364667799055314156717241)
                  ·
                    rfl

theorem cell21_1597923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 4].length) (baseStart_1597923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1597923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1597923 prefixEnd_1597923 := by exact prefixLift 1597923
  have htrace : WordTrace (prefixWord ++ tailWord_1597923) baseStart_1597923 baseEnd_1597923 := by
    simpa [prefixWord, tailWord_1597923, baseEnd_1597923] using wordTrace_append hprefix tailTrace_1597923
  have hstable : (prefixWord ++ tailWord_1597923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597923).length < 2 ^ (prefixWord ++ tailWord_1597923).sum := by decide
  have hdescent : baseEnd_1597923 < baseStart_1597923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598007 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 6]
def baseStart_1598007 : Nat := 118140960795 + 1598007 * 2 ^ 59
def prefixEnd_1598007 : Nat := 4983230072969 + 3 ^ 40 * 1598007 * 2
def baseEnd_1598007 : Nat := 364686968999748677317069

theorem tailTrace_1598007 : CollatzResearch.WordTrace tailWord_1598007 prefixEnd_1598007 364686968999748677317069 := by
  unfold tailWord_1598007
  simp only [CollatzResearch.WordTrace]
  refine ⟨58284103521701031712608275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38856069014467354475072183 58284103521701031712608275)
  ·
    refine ⟨87426155282551547568912413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58284103521701031712608275 87426155282551547568912413)
    ·
      refine ⟨32784808230956830338342155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87426155282551547568912413 32784808230956830338342155)
      ·
        refine ⟨49177212346435245507513233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32784808230956830338342155 49177212346435245507513233)
        ·
          refine ⟨36882909259826434130634925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49177212346435245507513233 36882909259826434130634925)
          ·
            refine ⟨13831090972434912798988097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36882909259826434130634925 13831090972434912798988097)
            ·
              refine ⟨10373318229326184599241073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13831090972434912798988097 10373318229326184599241073)
              ·
                refine ⟨7779988671994638449430805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10373318229326184599241073 7779988671994638449430805)
                ·
                  refine ⟨364686968999748677317069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7779988671994638449430805 364686968999748677317069)
                  ·
                    rfl

theorem cell21_1598007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_1598007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598007 prefixEnd_1598007 := by exact prefixLift 1598007
  have htrace : WordTrace (prefixWord ++ tailWord_1598007) baseStart_1598007 baseEnd_1598007 := by
    simpa [prefixWord, tailWord_1598007, baseEnd_1598007] using wordTrace_append hprefix tailTrace_1598007
  have hstable : (prefixWord ++ tailWord_1598007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598007).length < 2 ^ (prefixWord ++ tailWord_1598007).sum := by decide
  have hdescent : baseEnd_1598007 < baseStart_1598007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598010 : List Nat := [3, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_1598010 : Nat := 118140960795 + 1598010 * 2 ^ 59
def prefixEnd_1598010 : Nat := 4983230072969 + 3 ^ 40 * 1598010 * 2
def baseEnd_1598010 : Nat := 364687653640621338767063

theorem tailTrace_1598010 : CollatzResearch.WordTrace tailWord_1598010 prefixEnd_1598010 364687653640621338767063 := by
  unfold tailWord_1598010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14571053235172540806241871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38856141960460108816644989 14571053235172540806241871)
  ·
    refine ⟨21856579852758811209362807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14571053235172540806241871 21856579852758811209362807)
    ·
      refine ⟨32784869779138216814044211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21856579852758811209362807 32784869779138216814044211)
      ·
        refine ⟨49177304668707325221066317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32784869779138216814044211 49177304668707325221066317)
        ·
          refine ⟨18441489250765246957899869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49177304668707325221066317 18441489250765246957899869)
          ·
            refine ⟨6915558469036967609212451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18441489250765246957899869 6915558469036967609212451)
            ·
              refine ⟨10373337703555451413818677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915558469036967609212451 10373337703555451413818677)
              ·
                refine ⟨972500409708323570045501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10373337703555451413818677 972500409708323570045501)
                ·
                  refine ⟨364687653640621338767063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972500409708323570045501 364687653640621338767063)
                  ·
                    rfl

theorem cell21_1598010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_1598010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598010 prefixEnd_1598010 := by exact prefixLift 1598010
  have htrace : WordTrace (prefixWord ++ tailWord_1598010) baseStart_1598010 baseEnd_1598010 := by
    simpa [prefixWord, tailWord_1598010, baseEnd_1598010] using wordTrace_append hprefix tailTrace_1598010
  have hstable : (prefixWord ++ tailWord_1598010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598010).length < 2 ^ (prefixWord ++ tailWord_1598010).sum := by decide
  have hdescent : baseEnd_1598010 < baseStart_1598010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598083 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 6]
def baseStart_1598083 : Nat := 118140960795 + 1598083 * 2 ^ 59
def prefixEnd_1598083 : Nat := 4983230072969 + 3 ^ 40 * 1598083 * 2
def baseEnd_1598083 : Nat := 364704313235189434050247

theorem tailTrace_1598083 : CollatzResearch.WordTrace tailWord_1598083 prefixEnd_1598083 364704313235189434050247 := by
  unfold tailWord_1598083
  simp only [CollatzResearch.WordTrace]
  refine ⟨58286875469425696692374903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38857916979617131128249935 58286875469425696692374903)
  ·
    refine ⟨87430313204138545038562355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58286875469425696692374903 87430313204138545038562355)
    ·
      refine ⟨131145469806207817557843533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87430313204138545038562355 131145469806207817557843533)
      ·
        refine ⟨49179551177327931584191325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131145469806207817557843533 49179551177327931584191325)
        ·
          refine ⟨18442331691497974344071747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49179551177327931584191325 18442331691497974344071747)
          ·
            refine ⟨27663497537246961516107621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18442331691497974344071747 27663497537246961516107621)
            ·
              refine ⟨5186905788233805284270179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27663497537246961516107621 5186905788233805284270179)
              ·
                refine ⟨7780358682350707926405269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186905788233805284270179 7780358682350707926405269)
                ·
                  refine ⟨364704313235189434050247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7780358682350707926405269 364704313235189434050247)
                  ·
                    rfl

theorem cell21_1598083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_1598083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598083 prefixEnd_1598083 := by exact prefixLift 1598083
  have htrace : WordTrace (prefixWord ++ tailWord_1598083) baseStart_1598083 baseEnd_1598083 := by
    simpa [prefixWord, tailWord_1598083, baseEnd_1598083] using wordTrace_append hprefix tailTrace_1598083
  have hstable : (prefixWord ++ tailWord_1598083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598083).length < 2 ^ (prefixWord ++ tailWord_1598083).sum := by decide
  have hdescent : baseEnd_1598083 < baseStart_1598083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598162 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1598162 : Nat := 118140960795 + 1598162 * 2 ^ 59
def prefixEnd_1598162 : Nat := 4983230072969 + 3 ^ 40 * 1598162 * 2
def baseEnd_1598162 : Nat := 364722342111502852233419

theorem tailTrace_1598162 : CollatzResearch.WordTrace tailWord_1598162 prefixEnd_1598162 364722342111502852233419 := by
  unfold tailWord_1598162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572439209034873296125185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38859837890759662123000493 14572439209034873296125185)
  ·
    refine ⟨10929329406776154972093889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14572439209034873296125185 10929329406776154972093889)
    ·
      refine ⟨8196997055082116229070417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10929329406776154972093889 8196997055082116229070417)
      ·
        refine ⟨6147747791311587171802813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8196997055082116229070417 6147747791311587171802813)
        ·
          refine ⟨2305405421741845189426055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6147747791311587171802813 2305405421741845189426055)
          ·
            refine ⟨3458108132612767784139083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305405421741845189426055 3458108132612767784139083)
            ·
              refine ⟨5187162198919151676208625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458108132612767784139083 5187162198919151676208625)
              ·
                refine ⟨3890371649189363757156469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5187162198919151676208625 3890371649189363757156469)
                ·
                  refine ⟨364722342111502852233419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3890371649189363757156469 364722342111502852233419)
                  ·
                    rfl

theorem cell21_1598162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1598162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598162 prefixEnd_1598162 := by exact prefixLift 1598162
  have htrace : WordTrace (prefixWord ++ tailWord_1598162) baseStart_1598162 baseEnd_1598162 := by
    simpa [prefixWord, tailWord_1598162, baseEnd_1598162] using wordTrace_append hprefix tailTrace_1598162
  have hstable : (prefixWord ++ tailWord_1598162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598162).length < 2 ^ (prefixWord ++ tailWord_1598162).sum := by decide
  have hdescent : baseEnd_1598162 < baseStart_1598162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598179 : List Nat := [1, 1, 1, 7, 1, 2, 2, 3, 3]
def baseStart_1598179 : Nat := 118140960795 + 1598179 * 2 ^ 59
def prefixEnd_1598179 : Nat := 4983230072969 + 3 ^ 40 * 1598179 * 2
def baseEnd_1598179 : Nat := 364726221743114600450051

theorem tailTrace_1598179 : CollatzResearch.WordTrace tailWord_1598179 prefixEnd_1598179 364726221743114600450051 := by
  unfold tailWord_1598179
  simp only [CollatzResearch.WordTrace]
  refine ⟨58290376877077905087869591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38860251251385270058579727 58290376877077905087869591)
  ·
    refine ⟨87435565315616857631804387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58290376877077905087869591 87435565315616857631804387)
    ·
      refine ⟨131153347973425286447706581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87435565315616857631804387 131153347973425286447706581)
      ·
        refine ⟨3073906593127155151118123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 131153347973425286447706581 3073906593127155151118123)
        ·
          refine ⟨4610859889690732726677185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073906593127155151118123 4610859889690732726677185)
          ·
            refine ⟨3458144917268049545007889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4610859889690732726677185 3458144917268049545007889)
            ·
              refine ⟨2593608687951037158755917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458144917268049545007889 2593608687951037158755917)
              ·
                refine ⟨972603257981638934533469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2593608687951037158755917 972603257981638934533469)
                ·
                  refine ⟨364726221743114600450051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972603257981638934533469 364726221743114600450051)
                  ·
                    rfl

theorem cell21_1598179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 3].length) (baseStart_1598179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598179 prefixEnd_1598179 := by exact prefixLift 1598179
  have htrace : WordTrace (prefixWord ++ tailWord_1598179) baseStart_1598179 baseEnd_1598179 := by
    simpa [prefixWord, tailWord_1598179, baseEnd_1598179] using wordTrace_append hprefix tailTrace_1598179
  have hstable : (prefixWord ++ tailWord_1598179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598179).length < 2 ^ (prefixWord ++ tailWord_1598179).sum := by decide
  have hdescent : baseEnd_1598179 < baseStart_1598179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598190 : List Nat := [4, 1, 2, 1, 1, 4, 8]
def baseStart_1598190 : Nat := 118140960795 + 1598190 * 2 ^ 59
def prefixEnd_1598190 : Nat := 4983230072969 + 3 ^ 40 * 1598190 * 2
def baseEnd_1598190 : Nat := 40525414676997891751855

theorem tailTrace_1598190 : CollatzResearch.WordTrace tailWord_1598190 prefixEnd_1598190 40525414676997891751855 := by
  unfold tailWord_1598190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286347260004756745815003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38860518720025369311013349 7286347260004756745815003)
  ·
    refine ⟨10929520890007135118722505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286347260004756745815003 10929520890007135118722505)
    ·
      refine ⟨8197140667505351339041879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10929520890007135118722505 8197140667505351339041879)
      ·
        refine ⟨12295711001258027008562819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8197140667505351339041879 12295711001258027008562819)
        ·
          refine ⟨18443566501887040512844229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12295711001258027008562819 18443566501887040512844229)
          ·
            refine ⟨3458168719103820096158293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18443566501887040512844229 3458168719103820096158293)
            ·
              refine ⟨40525414676997891751855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3458168719103820096158293 40525414676997891751855)
              ·
                rfl

theorem cell21_1598190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 8].length) (baseStart_1598190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598190 prefixEnd_1598190 := by exact prefixLift 1598190
  have htrace : WordTrace (prefixWord ++ tailWord_1598190) baseStart_1598190 baseEnd_1598190 := by
    simpa [prefixWord, tailWord_1598190, baseEnd_1598190] using wordTrace_append hprefix tailTrace_1598190
  have hstable : (prefixWord ++ tailWord_1598190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598190).length < 2 ^ (prefixWord ++ tailWord_1598190).sum := by decide
  have hdescent : baseEnd_1598190 < baseStart_1598190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598196 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1598196 : Nat := 118140960795 + 1598196 * 2 ^ 59
def prefixEnd_1598196 : Nat := 4983230072969 + 3 ^ 40 * 1598196 * 2
def baseEnd_1598196 : Nat := 364730101374726348666683

theorem tailTrace_1598196 : CollatzResearch.WordTrace tailWord_1598196 prefixEnd_1598196 364730101374726348666683 := by
  unfold tailWord_1598196
  simp only [CollatzResearch.WordTrace]
  refine ⟨29145498459008158495619221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38860664612010877994158961 29145498459008158495619221)
  ·
    refine ⟨1366195240266007429482151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29145498459008158495619221 1366195240266007429482151)
    ·
      refine ⟨2049292860399011144223227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366195240266007429482151 2049292860399011144223227)
      ·
        refine ⟨3073939290598516716334841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049292860399011144223227 3073939290598516716334841)
        ·
          refine ⟨2305454467948887537251131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3073939290598516716334841 2305454467948887537251131)
          ·
            refine ⟨3458181701923331305876697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305454467948887537251131 3458181701923331305876697)
            ·
              refine ⟨2593636276442498479407523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458181701923331305876697 2593636276442498479407523)
              ·
                refine ⟨3890454414663747719111285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593636276442498479407523 3890454414663747719111285)
                ·
                  refine ⟨364730101374726348666683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3890454414663747719111285 364730101374726348666683)
                  ·
                    rfl

theorem cell21_1598196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1598196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598196 prefixEnd_1598196 := by exact prefixLift 1598196
  have htrace : WordTrace (prefixWord ++ tailWord_1598196) baseStart_1598196 baseEnd_1598196 := by
    simpa [prefixWord, tailWord_1598196, baseEnd_1598196] using wordTrace_append hprefix tailTrace_1598196
  have hstable : (prefixWord ++ tailWord_1598196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598196).length < 2 ^ (prefixWord ++ tailWord_1598196).sum := by decide
  have hdescent : baseEnd_1598196 < baseStart_1598196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598210 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1598210 : Nat := 118140960795 + 1598210 * 2 ^ 59
def prefixEnd_1598210 : Nat := 4983230072969 + 3 ^ 40 * 1598210 * 2
def baseEnd_1598210 : Nat := 364733296365465435433321

theorem tailTrace_1598210 : CollatzResearch.WordTrace tailWord_1598210 prefixEnd_1598210 364733296365465435433321 := by
  unfold tailWord_1598210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572876884991399345562021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38861005026643731588165389 14572876884991399345562021)
  ·
    refine ⟨2732414415935887377292879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14572876884991399345562021 2732414415935887377292879)
    ·
      refine ⟨4098621623903831065939319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2732414415935887377292879 4098621623903831065939319)
      ·
        refine ⟨6147932435855746598908979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098621623903831065939319 6147932435855746598908979)
        ·
          refine ⟨9221898653783619898363469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6147932435855746598908979 9221898653783619898363469)
          ·
            refine ⟨3458211995168857461886301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9221898653783619898363469 3458211995168857461886301)
            ·
              refine ⟨1296829498188321548207363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3458211995168857461886301 1296829498188321548207363)
              ·
                refine ⟨1945244247282482322311045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296829498188321548207363 1945244247282482322311045)
                ·
                  refine ⟨364733296365465435433321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1945244247282482322311045 364733296365465435433321)
                  ·
                    rfl

theorem cell21_1598210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1598210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598210 prefixEnd_1598210 := by exact prefixLift 1598210
  have htrace : WordTrace (prefixWord ++ tailWord_1598210) baseStart_1598210 baseEnd_1598210 := by
    simpa [prefixWord, tailWord_1598210, baseEnd_1598210] using wordTrace_append hprefix tailTrace_1598210
  have hstable : (prefixWord ++ tailWord_1598210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598210).length < 2 ^ (prefixWord ++ tailWord_1598210).sum := by decide
  have hdescent : baseEnd_1598210 < baseStart_1598210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598269 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 4]
def baseStart_1598269 : Nat := 118140960795 + 1598269 * 2 ^ 59
def prefixEnd_1598269 : Nat := 4983230072969 + 3 ^ 40 * 1598269 * 2
def baseEnd_1598269 : Nat := 364746760969294443949867

theorem tailTrace_1598269 : CollatzResearch.WordTrace tailWord_1598269 prefixEnd_1598269 364746760969294443949867 := by
  unfold tailWord_1598269
  simp only [CollatzResearch.WordTrace]
  refine ⟨58293659446751850458645861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38862439631167900305763907 58293659446751850458645861)
  ·
    refine ⟨10930061146265971960996099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58293659446751850458645861 10930061146265971960996099)
    ·
      refine ⟨16395091719398957941494149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10930061146265971960996099 16395091719398957941494149)
      ·
        refine ⟨3074079697387304614030153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16395091719398957941494149 3074079697387304614030153)
        ·
          refine ⟨2305559773040478460522615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3074079697387304614030153 2305559773040478460522615)
          ·
            refine ⟨3458339659560717690783923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305559773040478460522615 3458339659560717690783923)
            ·
              refine ⟨5187509489341076536175885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458339659560717690783923 5187509489341076536175885)
              ·
                refine ⟨1945316058502903701065957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187509489341076536175885 1945316058502903701065957)
                ·
                  refine ⟨364746760969294443949867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1945316058502903701065957 364746760969294443949867)
                  ·
                    rfl

theorem cell21_1598269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_1598269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598269 prefixEnd_1598269 := by exact prefixLift 1598269
  have htrace : WordTrace (prefixWord ++ tailWord_1598269) baseStart_1598269 baseEnd_1598269 := by
    simpa [prefixWord, tailWord_1598269, baseEnd_1598269] using wordTrace_append hprefix tailTrace_1598269
  have hstable : (prefixWord ++ tailWord_1598269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598269).length < 2 ^ (prefixWord ++ tailWord_1598269).sum := by decide
  have hdescent : baseEnd_1598269 < baseStart_1598269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598280 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_1598280 : Nat := 118140960795 + 1598280 * 2 ^ 59
def prefixEnd_1598280 : Nat := 4983230072969 + 3 ^ 40 * 1598280 * 2
def baseEnd_1598280 : Nat := 364749271319160869266511

theorem tailTrace_1598280 : CollatzResearch.WordTrace tailWord_1598280 prefixEnd_1598280 364749271319160869266511 := by
  unfold tailWord_1598280
  simp only [CollatzResearch.WordTrace]
  refine ⟨29147030324855999668648147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38862707099807999558197529 29147030324855999668648147)
  ·
    refine ⟨43720545487283999502972221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29147030324855999668648147 43720545487283999502972221)
    ·
      refine ⟨16395204557731499813614583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43720545487283999502972221 16395204557731499813614583)
      ·
        refine ⟨24592806836597249720421875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16395204557731499813614583 24592806836597249720421875)
        ·
          refine ⟨36889210254895874580632813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24592806836597249720421875 36889210254895874580632813)
          ·
            refine ⟨13833453845585952967737305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36889210254895874580632813 13833453845585952967737305)
            ·
              refine ⟨10375090384189464725802979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13833453845585952967737305 10375090384189464725802979)
              ·
                refine ⟨15562635576284197088704469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10375090384189464725802979 15562635576284197088704469)
                ·
                  refine ⟨364749271319160869266511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15562635576284197088704469 364749271319160869266511)
                  ·
                    rfl

theorem cell21_1598280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_1598280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598280 prefixEnd_1598280 := by exact prefixLift 1598280
  have htrace : WordTrace (prefixWord ++ tailWord_1598280) baseStart_1598280 baseEnd_1598280 := by
    simpa [prefixWord, tailWord_1598280, baseEnd_1598280] using wordTrace_append hprefix tailTrace_1598280
  have hstable : (prefixWord ++ tailWord_1598280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598280).length < 2 ^ (prefixWord ++ tailWord_1598280).sum := by decide
  have hdescent : baseEnd_1598280 < baseStart_1598280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598362 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_1598362 : Nat := 118140960795 + 1598362 * 2 ^ 59
def prefixEnd_1598362 : Nat := 4983230072969 + 3 ^ 40 * 1598362 * 2
def baseEnd_1598362 : Nat := 364767984836346948899677

theorem tailTrace_1598362 : CollatzResearch.WordTrace tailWord_1598362 prefixEnd_1598362 364767984836346948899677 := by
  unfold tailWord_1598362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574262858853731835445335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38864700956943284894520893 14574262858853731835445335)
  ·
    refine ⟨21861394288280597753168003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14574262858853731835445335 21861394288280597753168003)
    ·
      refine ⟨32792091432420896629752005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21861394288280597753168003 32792091432420896629752005)
      ·
        refine ⟨6148517143578918118078501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32792091432420896629752005 6148517143578918118078501)
        ·
          refine ⟨1152846964421047147139719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6148517143578918118078501 1152846964421047147139719)
          ·
            refine ⟨1729270446631570720709579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152846964421047147139719 1729270446631570720709579)
            ·
              refine ⟨2593905669947356081064369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729270446631570720709579 2593905669947356081064369)
              ·
                refine ⟨1945429252460517060798277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593905669947356081064369 1945429252460517060798277)
                ·
                  refine ⟨364767984836346948899677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1945429252460517060798277 364767984836346948899677)
                  ·
                    rfl

theorem cell21_1598362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_1598362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598362 prefixEnd_1598362 := by exact prefixLift 1598362
  have htrace : WordTrace (prefixWord ++ tailWord_1598362) baseStart_1598362 baseEnd_1598362 := by
    simpa [prefixWord, tailWord_1598362, baseEnd_1598362] using wordTrace_append hprefix tailTrace_1598362
  have hstable : (prefixWord ++ tailWord_1598362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598362).length < 2 ^ (prefixWord ++ tailWord_1598362).sum := by decide
  have hdescent : baseEnd_1598362 < baseStart_1598362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598418 : List Nat := [3, 2, 2, 3, 1, 1, 9]
def baseStart_1598418 : Nat := 118140960795 + 1598418 * 2 ^ 59
def prefixEnd_1598418 : Nat := 4983230072969 + 3 ^ 40 * 1598418 * 2
def baseEnd_1598418 : Nat := 40531196088811477329581

theorem tailTrace_1598418 : CollatzResearch.WordTrace tailWord_1598418 prefixEnd_1598418 40531196088811477329581 := by
  unfold tailWord_1598418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574773480803012226454977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38866062615474699270546605 14574773480803012226454977)
  ·
    refine ⟨10931080110602259169841233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14574773480803012226454977 10931080110602259169841233)
    ·
      refine ⟨8198310082951694377380925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10931080110602259169841233 8198310082951694377380925)
      ·
        refine ⟨3074366281106885391517847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8198310082951694377380925 3074366281106885391517847)
        ·
          refine ⟨4611549421660328087276771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074366281106885391517847 4611549421660328087276771)
          ·
            refine ⟨6917324132490492130915157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611549421660328087276771 6917324132490492130915157)
            ·
              refine ⟨40531196088811477329581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6917324132490492130915157 40531196088811477329581)
              ·
                rfl

theorem cell21_1598418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 9].length) (baseStart_1598418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598418 prefixEnd_1598418 := by exact prefixLift 1598418
  have htrace : WordTrace (prefixWord ++ tailWord_1598418) baseStart_1598418 baseEnd_1598418 := by
    simpa [prefixWord, tailWord_1598418, baseEnd_1598418] using wordTrace_append hprefix tailTrace_1598418
  have hstable : (prefixWord ++ tailWord_1598418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598418).length < 2 ^ (prefixWord ++ tailWord_1598418).sum := by decide
  have hdescent : baseEnd_1598418 < baseStart_1598418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598508 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_1598508 : Nat := 118140960795 + 1598508 * 2 ^ 59
def prefixEnd_1598508 : Nat := 4983230072969 + 3 ^ 40 * 1598508 * 2
def baseEnd_1598508 : Nat := 364801304025483139466045

theorem tailTrace_1598508 : CollatzResearch.WordTrace tailWord_1598508 prefixEnd_1598508 364801304025483139466045 := by
  unfold tailWord_1598508
  simp only [CollatzResearch.WordTrace]
  refine ⟨29151188246442997138298089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38868250995257329517730785 29151188246442997138298089)
  ·
    refine ⟨21863391184832247853723567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29151188246442997138298089 21863391184832247853723567)
    ·
      refine ⟨32795086777248371780585351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863391184832247853723567 32795086777248371780585351)
      ·
        refine ⟨49192630165872557670878027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32795086777248371780585351 49192630165872557670878027)
        ·
          refine ⟨73788945248808836506317041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49192630165872557670878027 73788945248808836506317041)
          ·
            refine ⟨55341708936606627379737781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73788945248808836506317041 55341708936606627379737781)
            ·
              refine ⟨5188285212806871316850417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55341708936606627379737781 5188285212806871316850417)
              ·
                refine ⟨3891213909605153487637813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5188285212806871316850417 3891213909605153487637813)
                ·
                  refine ⟨364801304025483139466045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3891213909605153487637813 364801304025483139466045)
                  ·
                    rfl

theorem cell21_1598508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_1598508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598508 prefixEnd_1598508 := by exact prefixLift 1598508
  have htrace : WordTrace (prefixWord ++ tailWord_1598508) baseStart_1598508 baseEnd_1598508 := by
    simpa [prefixWord, tailWord_1598508, baseEnd_1598508] using wordTrace_append hprefix tailTrace_1598508
  have hstable : (prefixWord ++ tailWord_1598508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598508).length < 2 ^ (prefixWord ++ tailWord_1598508).sum := by decide
  have hdescent : baseEnd_1598508 < baseStart_1598508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598570 : List Nat := [3, 1, 3, 2, 2, 2, 1, 7]
def baseStart_1598570 : Nat := 118140960795 + 1598570 * 2 ^ 59
def prefixEnd_1598570 : Nat := 4983230072969 + 3 ^ 40 * 1598570 * 2
def baseEnd_1598570 : Nat := 121605151090061603144195

theorem tailTrace_1598570 : CollatzResearch.WordTrace tailWord_1598570 prefixEnd_1598570 121605151090061603144195 := by
  unfold tailWord_1598570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576159454665344716338291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38869758545774252576902109 14576159454665344716338291)
  ·
    refine ⟨21864239181998017074507437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14576159454665344716338291 21864239181998017074507437)
    ·
      refine ⟨8199089693249256402940289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21864239181998017074507437 8199089693249256402940289)
      ·
        refine ⟨6149317269936942302205217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8199089693249256402940289 6149317269936942302205217)
        ·
          refine ⟨4611987952452706726653913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6149317269936942302205217 4611987952452706726653913)
          ·
            refine ⟨3458990964339530044990435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4611987952452706726653913 3458990964339530044990435)
            ·
              refine ⟨5188486446509295067485653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458990964339530044990435 5188486446509295067485653)
              ·
                refine ⟨121605151090061603144195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5188486446509295067485653 121605151090061603144195)
                ·
                  rfl

theorem cell21_1598570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_1598570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598570 prefixEnd_1598570 := by exact prefixLift 1598570
  have htrace : WordTrace (prefixWord ++ tailWord_1598570) baseStart_1598570 baseEnd_1598570 := by
    simpa [prefixWord, tailWord_1598570, baseEnd_1598570] using wordTrace_append hprefix tailTrace_1598570
  have hstable : (prefixWord ++ tailWord_1598570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598570).length < 2 ^ (prefixWord ++ tailWord_1598570).sum := by decide
  have hdescent : baseEnd_1598570 < baseStart_1598570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598601 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 5]
def baseStart_1598601 : Nat := 118140960795 + 1598601 * 2 ^ 59
def prefixEnd_1598601 : Nat := 4983230072969 + 3 ^ 40 * 1598601 * 2
def baseEnd_1598601 : Nat := 364822527892535644415855

theorem tailTrace_1598601 : CollatzResearch.WordTrace tailWord_1598601 prefixEnd_1598601 364822527892535644415855 := by
  unfold tailWord_1598601
  simp only [CollatzResearch.WordTrace]
  refine ⟨58305768481549071159731657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38870512321032714106487771 58305768481549071159731657)
  ·
    refine ⟨43729326361161803369798743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58305768481549071159731657 43729326361161803369798743)
    ·
      refine ⟨65593989541742705054698115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43729326361161803369798743 65593989541742705054698115)
      ·
        refine ⟨98390984312614057582047173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65593989541742705054698115 98390984312614057582047173)
        ·
          refine ⟨18448309558615135796633845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98390984312614057582047173 18448309558615135796633845)
          ·
            refine ⟨1729529021120168980934423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18448309558615135796633845 1729529021120168980934423)
            ·
              refine ⟨2594293531680253471401635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729529021120168980934423 2594293531680253471401635)
              ·
                refine ⟨3891440297520380207102453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594293531680253471401635 3891440297520380207102453)
                ·
                  refine ⟨364822527892535644415855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3891440297520380207102453 364822527892535644415855)
                  ·
                    rfl

theorem cell21_1598601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_1598601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598601 prefixEnd_1598601 := by exact prefixLift 1598601
  have htrace : WordTrace (prefixWord ++ tailWord_1598601) baseStart_1598601 baseEnd_1598601 := by
    simpa [prefixWord, tailWord_1598601, baseEnd_1598601] using wordTrace_append hprefix tailTrace_1598601
  have hstable : (prefixWord ++ tailWord_1598601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598601).length < 2 ^ (prefixWord ++ tailWord_1598601).sum := by decide
  have hdescent : baseEnd_1598601 < baseStart_1598601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598629 : List Nat := [1, 3, 1, 2, 1, 4, 2, 7]
def baseStart_1598629 : Nat := 118140960795 + 1598629 * 2 ^ 59
def prefixEnd_1598629 : Nat := 4983230072969 + 3 ^ 40 * 1598629 * 2
def baseEnd_1598629 : Nat := 121609639291337939316377

theorem tailTrace_1598629 : CollatzResearch.WordTrace tailWord_1598629 prefixEnd_1598629 121609639291337939316377 := by
  unfold tailWord_1598629
  simp only [CollatzResearch.WordTrace]
  refine ⟨58306789725447631941750941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38871193150298421294500627 58306789725447631941750941)
  ·
    refine ⟨21865046147042861978156603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58306789725447631941750941 21865046147042861978156603)
    ·
      refine ⟨32797569220564292967234905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21865046147042861978156603 32797569220564292967234905)
      ·
        refine ⟨24598176915423219725426179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32797569220564292967234905 24598176915423219725426179)
        ·
          refine ⟨36897265373134829588139269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24598176915423219725426179 36897265373134829588139269)
          ·
            refine ⟨6918237257462780547776113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36897265373134829588139269 6918237257462780547776113)
            ·
              refine ⟨5188677943097085410832085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6918237257462780547776113 5188677943097085410832085)
              ·
                refine ⟨121609639291337939316377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5188677943097085410832085 121609639291337939316377)
                ·
                  rfl

theorem cell21_1598629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 7].length) (baseStart_1598629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598629 prefixEnd_1598629 := by exact prefixLift 1598629
  have htrace : WordTrace (prefixWord ++ tailWord_1598629) baseStart_1598629 baseEnd_1598629 := by
    simpa [prefixWord, tailWord_1598629, baseEnd_1598629] using wordTrace_append hprefix tailTrace_1598629
  have hstable : (prefixWord ++ tailWord_1598629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598629).length < 2 ^ (prefixWord ++ tailWord_1598629).sum := by decide
  have hdescent : baseEnd_1598629 < baseStart_1598629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598677 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 5]
def baseStart_1598677 : Nat := 118140960795 + 1598677 * 2 ^ 59
def prefixEnd_1598677 : Nat := 4983230072969 + 3 ^ 40 * 1598677 * 2
def baseEnd_1598677 : Nat := 364839872127976401149033

theorem tailTrace_1598677 : CollatzResearch.WordTrace tailWord_1598677 prefixEnd_1598677 364839872127976401149033 := by
  unfold tailWord_1598677
  simp only [CollatzResearch.WordTrace]
  refine ⟨58308540429273736139498285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38872360286182490759665523 58308540429273736139498285)
  ·
    refine ⟨21865702660977651052311857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58308540429273736139498285 21865702660977651052311857)
    ·
      refine ⟨16399276995733238289233893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21865702660977651052311857 16399276995733238289233893)
      ·
        refine ⟨3074864436699982179231355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16399276995733238289233893 3074864436699982179231355)
        ·
          refine ⟨4612296655049973268847033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074864436699982179231355 4612296655049973268847033)
          ·
            refine ⟨3459222491287479951635275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4612296655049973268847033 3459222491287479951635275)
            ·
              refine ⟨5188833736931219927452913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459222491287479951635275 5188833736931219927452913)
              ·
                refine ⟨3891625302698414945589685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5188833736931219927452913 3891625302698414945589685)
                ·
                  refine ⟨364839872127976401149033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3891625302698414945589685 364839872127976401149033)
                  ·
                    rfl

theorem cell21_1598677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_1598677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598677 prefixEnd_1598677 := by exact prefixLift 1598677
  have htrace : WordTrace (prefixWord ++ tailWord_1598677) baseStart_1598677 baseEnd_1598677 := by
    simpa [prefixWord, tailWord_1598677, baseEnd_1598677] using wordTrace_append hprefix tailTrace_1598677
  have hstable : (prefixWord ++ tailWord_1598677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598677).length < 2 ^ (prefixWord ++ tailWord_1598677).sum := by decide
  have hdescent : baseEnd_1598677 < baseStart_1598677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598871 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 9]
def baseStart_1598871 : Nat := 118140960795 + 1598871 * 2 ^ 59
def prefixEnd_1598871 : Nat := 4983230072969 + 3 ^ 40 * 1598871 * 2
def baseEnd_1598871 : Nat := 364884145571075174915303

theorem tailTrace_1598871 : CollatzResearch.WordTrace tailWord_1598871 prefixEnd_1598871 364884145571075174915303 := by
  unfold tailWord_1598871
  simp only [CollatzResearch.WordTrace]
  refine ⟨58315616190570907272060467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38877077460380604848040311 58315616190570907272060467)
  ·
    refine ⟨87473424285856360908090701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58315616190570907272060467 87473424285856360908090701)
    ·
      refine ⟨32802534107196135340534013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87473424285856360908090701 32802534107196135340534013)
      ·
        refine ⟨12300950290198550752700255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32802534107196135340534013 12300950290198550752700255)
        ·
          refine ⟨18451425435297826129050383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12300950290198550752700255 18451425435297826129050383)
          ·
            refine ⟨27677138152946739193575575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18451425435297826129050383 27677138152946739193575575)
            ·
              refine ⟨41515707229420108790363363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27677138152946739193575575 41515707229420108790363363)
              ·
                refine ⟨62273560844130163185545045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41515707229420108790363363 62273560844130163185545045)
                ·
                  refine ⟨364884145571075174915303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62273560844130163185545045 364884145571075174915303)
                  ·
                    rfl

theorem cell21_1598871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_1598871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598871 prefixEnd_1598871 := by exact prefixLift 1598871
  have htrace : WordTrace (prefixWord ++ tailWord_1598871) baseStart_1598871 baseEnd_1598871 := by
    simpa [prefixWord, tailWord_1598871, baseEnd_1598871] using wordTrace_append hprefix tailTrace_1598871
  have hstable : (prefixWord ++ tailWord_1598871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598871).length < 2 ^ (prefixWord ++ tailWord_1598871).sum := by decide
  have hdescent : baseEnd_1598871 < baseStart_1598871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598908 : List Nat := [2, 2, 2, 4, 3, 1, 2, 5]
def baseStart_1598908 : Nat := 118140960795 + 1598908 * 2 ^ 59
def prefixEnd_1598908 : Nat := 4983230072969 + 3 ^ 40 * 1598908 * 2
def baseEnd_1598908 : Nat := 121630863158390444266187

theorem tailTrace_1598908 : CollatzResearch.WordTrace tailWord_1598908 prefixEnd_1598908 121630863158390444266187 := by
  unfold tailWord_1598908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29158482845718431295578689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38877977127624575060771585 29158482845718431295578689)
  ·
    refine ⟨21868862134288823471684017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29158482845718431295578689 21868862134288823471684017)
    ·
      refine ⟨16401646600716617603763013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21868862134288823471684017 16401646600716617603763013)
      ·
        refine ⟨3075308737634365800705565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16401646600716617603763013 3075308737634365800705565)
        ·
          refine ⟨1153240776612887175264587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3075308737634365800705565 1153240776612887175264587)
          ·
            refine ⟨1729861164919330762896881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153240776612887175264587 1729861164919330762896881)
            ·
              refine ⟨1297395873689498072172661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729861164919330762896881 1297395873689498072172661)
              ·
                refine ⟨121630863158390444266187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1297395873689498072172661 121630863158390444266187)
                ·
                  rfl

theorem cell21_1598908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_1598908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598908 prefixEnd_1598908 := by exact prefixLift 1598908
  have htrace : WordTrace (prefixWord ++ tailWord_1598908) baseStart_1598908 baseEnd_1598908 := by
    simpa [prefixWord, tailWord_1598908, baseEnd_1598908] using wordTrace_append hprefix tailTrace_1598908
  have hstable : (prefixWord ++ tailWord_1598908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598908).length < 2 ^ (prefixWord ++ tailWord_1598908).sum := by decide
  have hdescent : baseEnd_1598908 < baseStart_1598908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598914 : List Nat := [3, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1598914 : Nat := 118140960795 + 1598914 * 2 ^ 59
def prefixEnd_1598914 : Nat := 4983230072969 + 3 ^ 40 * 1598914 * 2
def baseEnd_1598914 : Nat := 364893958756916655698549

theorem tailTrace_1598914 : CollatzResearch.WordTrace tailWord_1598914 prefixEnd_1598914 364893958756916655698549 := by
  unfold tailWord_1598914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579296132353781403968949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38878123019610083743917197 14579296132353781403968949)
  ·
    refine ⟨1366809012408167006622089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14579296132353781403968949 1366809012408167006622089)
    ·
      refine ⟨1025106759306125254966567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1366809012408167006622089 1025106759306125254966567)
      ·
        refine ⟨1537660138959187882449851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025106759306125254966567 1537660138959187882449851)
        ·
          refine ⟨2306490208438781823674777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537660138959187882449851 2306490208438781823674777)
          ·
            refine ⟨1729867656329086367756083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306490208438781823674777 1729867656329086367756083)
            ·
              refine ⟨2594801484493629551634125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729867656329086367756083 2594801484493629551634125)
              ·
                refine ⟨973050556685111081862797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2594801484493629551634125 973050556685111081862797)
                ·
                  refine ⟨364893958756916655698549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973050556685111081862797 364893958756916655698549)
                  ·
                    rfl

theorem cell21_1598914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1598914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598914 prefixEnd_1598914 := by exact prefixLift 1598914
  have htrace : WordTrace (prefixWord ++ tailWord_1598914) baseStart_1598914 baseEnd_1598914 := by
    simpa [prefixWord, tailWord_1598914, baseEnd_1598914] using wordTrace_append hprefix tailTrace_1598914
  have hstable : (prefixWord ++ tailWord_1598914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598914).length < 2 ^ (prefixWord ++ tailWord_1598914).sum := by decide
  have hdescent : baseEnd_1598914 < baseStart_1598914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598922 : List Nat := [3, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_1598922 : Nat := 118140960795 + 1598922 * 2 ^ 59
def prefixEnd_1598922 : Nat := 4983230072969 + 3 ^ 40 * 1598922 * 2
def baseEnd_1598922 : Nat := 364895784465910419565199

theorem tailTrace_1598922 : CollatzResearch.WordTrace tailWord_1598922 prefixEnd_1598922 364895784465910419565199 := by
  unfold tailWord_1598922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579369078346535745541755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38878317542257428654778013 14579369078346535745541755)
  ·
    refine ⟨21869053617519803618312633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14579369078346535745541755 21869053617519803618312633)
    ·
      refine ⟨16401790213139852713734475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21869053617519803618312633 16401790213139852713734475)
      ·
        refine ⟨24602685319709779070601713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16401790213139852713734475 24602685319709779070601713)
        ·
          refine ⟨18452013989782334302951285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24602685319709779070601713 18452013989782334302951285)
          ·
            refine ⟨1729876311542093840901683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18452013989782334302951285 1729876311542093840901683)
            ·
              refine ⟨2594814467313140761352525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729876311542093840901683 2594814467313140761352525)
              ·
                refine ⟨973055425242427785507197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2594814467313140761352525 973055425242427785507197)
                ·
                  refine ⟨364895784465910419565199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973055425242427785507197 364895784465910419565199)
                  ·
                    rfl

theorem cell21_1598922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_1598922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598922 prefixEnd_1598922 := by exact prefixLift 1598922
  have htrace : WordTrace (prefixWord ++ tailWord_1598922) baseStart_1598922 baseEnd_1598922 := by
    simpa [prefixWord, tailWord_1598922, baseEnd_1598922] using wordTrace_append hprefix tailTrace_1598922
  have hstable : (prefixWord ++ tailWord_1598922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598922).length < 2 ^ (prefixWord ++ tailWord_1598922).sum := by decide
  have hdescent : baseEnd_1598922 < baseStart_1598922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598995 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 4]
def baseStart_1598995 : Nat := 118140960795 + 1598995 * 2 ^ 59
def prefixEnd_1598995 : Nat := 4983230072969 + 3 ^ 40 * 1598995 * 2
def baseEnd_1598995 : Nat := 364912444060478514848383

theorem tailTrace_1598995 : CollatzResearch.WordTrace tailWord_1598995 prefixEnd_1598995 364912444060478514848383 := by
  unfold tailWord_1598995
  simp only [CollatzResearch.WordTrace]
  refine ⟨58320138842121676449574439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38880092561414450966382959 58320138842121676449574439)
  ·
    refine ⟨87480208263182514674361659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58320138842121676449574439 87480208263182514674361659)
    ·
      refine ⟨131220312394773772011542489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87480208263182514674361659 131220312394773772011542489)
      ·
        refine ⟨98415234296080329008656867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131220312394773772011542489 98415234296080329008656867)
        ·
          refine ⟨147622851444120493512985301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98415234296080329008656867 147622851444120493512985301)
          ·
            refine ⟨3459910580721574066710593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 147622851444120493512985301 3459910580721574066710593)
            ·
              refine ⟨2594932935541180550032945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459910580721574066710593 2594932935541180550032945)
              ·
                refine ⟨1946199701655885412524709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2594932935541180550032945 1946199701655885412524709)
                ·
                  refine ⟨364912444060478514848383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946199701655885412524709 364912444060478514848383)
                  ·
                    rfl

theorem cell21_1598995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_1598995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1598995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1598995 prefixEnd_1598995 := by exact prefixLift 1598995
  have htrace : WordTrace (prefixWord ++ tailWord_1598995) baseStart_1598995 baseEnd_1598995 := by
    simpa [prefixWord, tailWord_1598995, baseEnd_1598995] using wordTrace_append hprefix tailTrace_1598995
  have hstable : (prefixWord ++ tailWord_1598995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598995).length < 2 ^ (prefixWord ++ tailWord_1598995).sum := by decide
  have hdescent : baseEnd_1598995 < baseStart_1598995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599009 : List Nat := [1, 2, 3, 2, 2, 2, 3, 6]
def baseStart_1599009 : Nat := 118140960795 + 1599009 * 2 ^ 59
def prefixEnd_1599009 : Nat := 4983230072969 + 3 ^ 40 * 1599009 * 2
def baseEnd_1599009 : Nat := 121638546350405867205007

theorem tailTrace_1599009 : CollatzResearch.WordTrace tailWord_1599009 prefixEnd_1599009 121638546350405867205007 := by
  unfold tailWord_1599009
  simp only [CollatzResearch.WordTrace]
  refine ⟨58320649464070956840584081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38880432976047304560389387 58320649464070956840584081)
  ·
    refine ⟨43740487098053217630438061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58320649464070956840584081 43740487098053217630438061)
    ·
      refine ⟨16402682661769956611414273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43740487098053217630438061 16402682661769956611414273)
      ·
        refine ⟨12302011996327467458560705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16402682661769956611414273 12302011996327467458560705)
        ·
          refine ⟨9226508997245600593920529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12302011996327467458560705 9226508997245600593920529)
          ·
            refine ⟨6919881747934200445440397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9226508997245600593920529 6919881747934200445440397)
            ·
              refine ⟨2594955655475325167040149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6919881747934200445440397 2594955655475325167040149)
              ·
                refine ⟨121638546350405867205007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2594955655475325167040149 121638546350405867205007)
                ·
                  rfl

theorem cell21_1599009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 6].length) (baseStart_1599009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599009 prefixEnd_1599009 := by exact prefixLift 1599009
  have htrace : WordTrace (prefixWord ++ tailWord_1599009) baseStart_1599009 baseEnd_1599009 := by
    simpa [prefixWord, tailWord_1599009, baseEnd_1599009] using wordTrace_append hprefix tailTrace_1599009
  have hstable : (prefixWord ++ tailWord_1599009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599009).length < 2 ^ (prefixWord ++ tailWord_1599009).sum := by decide
  have hdescent : baseEnd_1599009 < baseStart_1599009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599046 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1599046 : Nat := 118140960795 + 1599046 * 2 ^ 59
def prefixEnd_1599046 : Nat := 4983230072969 + 3 ^ 40 * 1599046 * 2
def baseEnd_1599046 : Nat := 364924082955313759498279

theorem tailTrace_1599046 : CollatzResearch.WordTrace tailWord_1599046 prefixEnd_1599046 364924082955313759498279 := by
  unfold tailWord_1599046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822562467654278504990031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38881332643291274773120661 1822562467654278504990031)
  ·
    refine ⟨2733843701481417757485047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822562467654278504990031 2733843701481417757485047)
    ·
      refine ⟨4100765552222126636227571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2733843701481417757485047 4100765552222126636227571)
      ·
        refine ⟨6151148328333189954341357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100765552222126636227571 6151148328333189954341357)
        ·
          refine ⟨2306680623124946232878009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6151148328333189954341357 2306680623124946232878009)
          ·
            refine ⟨1730010467343709674658507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306680623124946232878009 1730010467343709674658507)
            ·
              refine ⟨2595015701015564511987761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730010467343709674658507 2595015701015564511987761)
              ·
                refine ⟨1946261775761673383990821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595015701015564511987761 1946261775761673383990821)
                ·
                  refine ⟨364924082955313759498279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946261775761673383990821 364924082955313759498279)
                  ·
                    rfl

theorem cell21_1599046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1599046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599046 prefixEnd_1599046 := by exact prefixLift 1599046
  have htrace : WordTrace (prefixWord ++ tailWord_1599046) baseStart_1599046 baseEnd_1599046 := by
    simpa [prefixWord, tailWord_1599046, baseEnd_1599046] using wordTrace_append hprefix tailTrace_1599046
  have hstable : (prefixWord ++ tailWord_1599046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599046).length < 2 ^ (prefixWord ++ tailWord_1599046).sum := by decide
  have hdescent : baseEnd_1599046 < baseStart_1599046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599122 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_1599122 : Nat := 118140960795 + 1599122 * 2 ^ 59
def prefixEnd_1599122 : Nat := 4983230072969 + 3 ^ 40 * 1599122 * 2
def baseEnd_1599122 : Nat := 364941427190754516231457

theorem tailTrace_1599122 : CollatzResearch.WordTrace tailWord_1599122 prefixEnd_1599122 364941427190754516231457 := by
  unfold tailWord_1599122
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581192728165394284861905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38883180608441051426298413 14581192728165394284861905)
  ·
    refine ⟨10935894546124045713646429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14581192728165394284861905 10935894546124045713646429)
    ·
      refine ⟨4100960454796517142617411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10935894546124045713646429 4100960454796517142617411)
      ·
        refine ⟨6151440682194775713926117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100960454796517142617411 6151440682194775713926117)
        ·
          refine ⟨1153395127911520446361147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6151440682194775713926117 1153395127911520446361147)
          ·
            refine ⟨1730092691867280669541721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153395127911520446361147 1730092691867280669541721)
            ·
              refine ⟨1297569518900460502156291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730092691867280669541721 1297569518900460502156291)
              ·
                refine ⟨1946354278350690753234437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297569518900460502156291 1946354278350690753234437)
                ·
                  refine ⟨364941427190754516231457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946354278350690753234437 364941427190754516231457)
                  ·
                    rfl

theorem cell21_1599122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_1599122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599122 prefixEnd_1599122 := by exact prefixLift 1599122
  have htrace : WordTrace (prefixWord ++ tailWord_1599122) baseStart_1599122 baseEnd_1599122 := by
    simpa [prefixWord, tailWord_1599122, baseEnd_1599122] using wordTrace_append hprefix tailTrace_1599122
  have hstable : (prefixWord ++ tailWord_1599122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599122).length < 2 ^ (prefixWord ++ tailWord_1599122).sum := by decide
  have hdescent : baseEnd_1599122 < baseStart_1599122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599175 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 5]
def baseStart_1599175 : Nat := 118140960795 + 1599175 * 2 ^ 59
def prefixEnd_1599175 : Nat := 4983230072969 + 3 ^ 40 * 1599175 * 2
def baseEnd_1599175 : Nat := 364953522512838201848015

theorem tailTrace_1599175 : CollatzResearch.WordTrace tailWord_1599175 prefixEnd_1599175 364953522512838201848015 := by
  unfold tailWord_1599175
  simp only [CollatzResearch.WordTrace]
  refine ⟨58326703981469567191126979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38884469320979711460751319 58326703981469567191126979)
  ·
    refine ⟨87490055972204350786690469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58326703981469567191126979 87490055972204350786690469)
    ·
      refine ⟨16404385494788315772504463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87490055972204350786690469 16404385494788315772504463)
      ·
        refine ⟨24606578242182473658756695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16404385494788315772504463 24606578242182473658756695)
        ·
          refine ⟨36909867363273710488135043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24606578242182473658756695 36909867363273710488135043)
          ·
            refine ⟨55364801044910565732202565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36909867363273710488135043 55364801044910565732202565)
            ·
              refine ⟨10380900195920731074787981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55364801044910565732202565 10380900195920731074787981)
              ·
                refine ⟨3892837573470274153045493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10380900195920731074787981 3892837573470274153045493)
                ·
                  refine ⟨364953522512838201848015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3892837573470274153045493 364953522512838201848015)
                  ·
                    rfl

theorem cell21_1599175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_1599175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599175 prefixEnd_1599175 := by exact prefixLift 1599175
  have htrace : WordTrace (prefixWord ++ tailWord_1599175) baseStart_1599175 baseEnd_1599175 := by
    simpa [prefixWord, tailWord_1599175, baseEnd_1599175] using wordTrace_append hprefix tailTrace_1599175
  have hstable : (prefixWord ++ tailWord_1599175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599175).length < 2 ^ (prefixWord ++ tailWord_1599175).sum := by decide
  have hdescent : baseEnd_1599175 < baseStart_1599175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599178 : List Nat := [3, 1, 2, 1, 5, 2, 1, 6]
def baseStart_1599178 : Nat := 118140960795 + 1599178 * 2 ^ 59
def prefixEnd_1599178 : Nat := 4983230072969 + 3 ^ 40 * 1599178 * 2
def baseEnd_1599178 : Nat := 121651402384570287766003

theorem tailTrace_1599178 : CollatzResearch.WordTrace tailWord_1599178 prefixEnd_1599178 121651402384570287766003 := by
  unfold tailWord_1599178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581703350114674675871547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38884542266972465802324125 14581703350114674675871547)
  ·
    refine ⟨21872555025172012013807321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14581703350114674675871547 21872555025172012013807321)
    ·
      refine ⟨16404416268879009010355491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21872555025172012013807321 16404416268879009010355491)
      ·
        refine ⟨24606624403318513515533237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16404416268879009010355491 24606624403318513515533237)
        ·
          refine ⟨2306871037811110642081241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24606624403318513515533237 2306871037811110642081241)
          ·
            refine ⟨1730153278358332981560931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306871037811110642081241 1730153278358332981560931)
            ·
              refine ⟨2595229917537499472341397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730153278358332981560931 2595229917537499472341397)
              ·
                refine ⟨121651402384570287766003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2595229917537499472341397 121651402384570287766003)
                ·
                  rfl

theorem cell21_1599178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_1599178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599178 prefixEnd_1599178 := by exact prefixLift 1599178
  have htrace : WordTrace (prefixWord ++ tailWord_1599178) baseStart_1599178 baseEnd_1599178 := by
    simpa [prefixWord, tailWord_1599178, baseEnd_1599178] using wordTrace_append hprefix tailTrace_1599178
  have hstable : (prefixWord ++ tailWord_1599178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599178).length < 2 ^ (prefixWord ++ tailWord_1599178).sum := by decide
  have hdescent : baseEnd_1599178 < baseStart_1599178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599282 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1599282 : Nat := 118140960795 + 1599282 * 2 ^ 59
def prefixEnd_1599282 : Nat := 4983230072969 + 3 ^ 40 * 1599282 * 2
def baseEnd_1599282 : Nat := 364977941370629793564463

theorem tailTrace_1599282 : CollatzResearch.WordTrace tailWord_1599282 prefixEnd_1599282 364977941370629793564463 := by
  unfold tailWord_1599282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14582651648020481116318025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38887071061387949643514733 14582651648020481116318025)
  ·
    refine ⟨10936988736015360837238519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14582651648020481116318025 10936988736015360837238519)
    ·
      refine ⟨16405483104023041255857779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10936988736015360837238519 16405483104023041255857779)
      ·
        refine ⟨24608224656034561883786669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16405483104023041255857779 24608224656034561883786669)
        ·
          refine ⟨9228084246012960706420001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24608224656034561883786669 9228084246012960706420001)
          ·
            refine ⟨6921063184509720529815001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9228084246012960706420001 6921063184509720529815001)
            ·
              refine ⟨5190797388382290397361251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6921063184509720529815001 5190797388382290397361251)
              ·
                refine ⟨7786196082573435596041877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190797388382290397361251 7786196082573435596041877)
                ·
                  refine ⟨364977941370629793564463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7786196082573435596041877 364977941370629793564463)
                  ·
                    rfl

theorem cell21_1599282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1599282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599282 prefixEnd_1599282 := by exact prefixLift 1599282
  have htrace : WordTrace (prefixWord ++ tailWord_1599282) baseStart_1599282 baseEnd_1599282 := by
    simpa [prefixWord, tailWord_1599282, baseEnd_1599282] using wordTrace_append hprefix tailTrace_1599282
  have hstable : (prefixWord ++ tailWord_1599282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599282).length < 2 ^ (prefixWord ++ tailWord_1599282).sum := by decide
  have hdescent : baseEnd_1599282 < baseStart_1599282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599285 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 5]
def baseStart_1599285 : Nat := 118140960795 + 1599285 * 2 ^ 59
def prefixEnd_1599285 : Nat := 4983230072969 + 3 ^ 40 * 1599285 * 2
def baseEnd_1599285 : Nat := 364978626011502455014457

theorem tailTrace_1599285 : CollatzResearch.WordTrace tailWord_1599285 prefixEnd_1599285 364978626011502455014457 := by
  unfold tailWord_1599285
  simp only [CollatzResearch.WordTrace]
  refine ⟨58330716011071055977631309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38887144007380703985087539 58330716011071055977631309)
  ·
    refine ⟨21874018504151645991611741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58330716011071055977631309 21874018504151645991611741)
    ·
      refine ⟨8202756939056867246854403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21874018504151645991611741 8202756939056867246854403)
      ·
        refine ⟨12304135408585300870281605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8202756939056867246854403 12304135408585300870281605)
        ·
          refine ⟨2307025389109743913177801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12304135408585300870281605 2307025389109743913177801)
          ·
            refine ⟨1730269041832307934883351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307025389109743913177801 1730269041832307934883351)
            ·
              refine ⟨2595403562748461902325027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730269041832307934883351 2595403562748461902325027)
              ·
                refine ⟨3893105344122692853487541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595403562748461902325027 3893105344122692853487541)
                ·
                  refine ⟨364978626011502455014457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3893105344122692853487541 364978626011502455014457)
                  ·
                    rfl

theorem cell21_1599285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_1599285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599285 prefixEnd_1599285 := by exact prefixLift 1599285
  have htrace : WordTrace (prefixWord ++ tailWord_1599285) baseStart_1599285 baseEnd_1599285 := by
    simpa [prefixWord, tailWord_1599285, baseEnd_1599285] using wordTrace_append hprefix tailTrace_1599285
  have hstable : (prefixWord ++ tailWord_1599285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599285).length < 2 ^ (prefixWord ++ tailWord_1599285).sum := by decide
  have hdescent : baseEnd_1599285 < baseStart_1599285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599299 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 4]
def baseStart_1599299 : Nat := 118140960795 + 1599299 * 2 ^ 59
def prefixEnd_1599299 : Nat := 4983230072969 + 3 ^ 40 * 1599299 * 2
def baseEnd_1599299 : Nat := 364981821002241541781095

theorem tailTrace_1599299 : CollatzResearch.WordTrace tailWord_1599299 prefixEnd_1599299 364981821002241541781095 := by
  unfold tailWord_1599299
  simp only [CollatzResearch.WordTrace]
  refine ⟨58331226633020336368640951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38887484422013557579093967 58331226633020336368640951)
  ·
    refine ⟨87496839949530504552961427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58331226633020336368640951 87496839949530504552961427)
    ·
      refine ⟨131245259924295756829442141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87496839949530504552961427 131245259924295756829442141)
      ·
        refine ⟨49216972471610908811040803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131245259924295756829442141 49216972471610908811040803)
        ·
          refine ⟨73825458707416363216561205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49216972471610908811040803 73825458707416363216561205)
          ·
            refine ⟨6921136753820284051552613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73825458707416363216561205 6921136753820284051552613)
            ·
              refine ⟨1297713141341303259666115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6921136753820284051552613 1297713141341303259666115)
              ·
                refine ⟨1946569712011954889499173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297713141341303259666115 1946569712011954889499173)
                ·
                  refine ⟨364981821002241541781095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946569712011954889499173 364981821002241541781095)
                  ·
                    rfl

theorem cell21_1599299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 4].length) (baseStart_1599299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599299 prefixEnd_1599299 := by exact prefixLift 1599299
  have htrace : WordTrace (prefixWord ++ tailWord_1599299) baseStart_1599299 baseEnd_1599299 := by
    simpa [prefixWord, tailWord_1599299, baseEnd_1599299] using wordTrace_append hprefix tailTrace_1599299
  have hstable : (prefixWord ++ tailWord_1599299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599299).length < 2 ^ (prefixWord ++ tailWord_1599299).sum := by decide
  have hdescent : baseEnd_1599299 < baseStart_1599299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599361 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 5]
def baseStart_1599361 : Nat := 118140960795 + 1599361 * 2 ^ 59
def prefixEnd_1599361 : Nat := 4983230072969 + 3 ^ 40 * 1599361 * 2
def baseEnd_1599361 : Nat := 364995970246943211747635

theorem tailTrace_1599361 : CollatzResearch.WordTrace tailWord_1599361 prefixEnd_1599361 364995970246943211747635 := by
  unfold tailWord_1599361
  simp only [CollatzResearch.WordTrace]
  refine ⟨58333487958795720957397937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38888991972530480638265291 58333487958795720957397937)
  ·
    refine ⟨43750115969096790718048453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58333487958795720957397937 43750115969096790718048453)
    ·
      refine ⟨8203146744205648259634085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43750115969096790718048453 8203146744205648259634085)
      ·
        refine ⟨1538090014538559048681391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8203146744205648259634085 1538090014538559048681391)
        ·
          refine ⟨2307135021807838573022087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538090014538559048681391 2307135021807838573022087)
          ·
            refine ⟨3460702532711757859533131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307135021807838573022087 3460702532711757859533131)
            ·
              refine ⟨5191053799067636789299697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460702532711757859533131 5191053799067636789299697)
              ·
                refine ⟨3893290349300727591974773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191053799067636789299697 3893290349300727591974773)
                ·
                  refine ⟨364995970246943211747635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3893290349300727591974773 364995970246943211747635)
                  ·
                    rfl

theorem cell21_1599361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_1599361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599361 prefixEnd_1599361 := by exact prefixLift 1599361
  have htrace : WordTrace (prefixWord ++ tailWord_1599361) baseStart_1599361 baseEnd_1599361 := by
    simpa [prefixWord, tailWord_1599361, baseEnd_1599361] using wordTrace_append hprefix tailTrace_1599361
  have hstable : (prefixWord ++ tailWord_1599361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599361).length < 2 ^ (prefixWord ++ tailWord_1599361).sum := by decide
  have hdescent : baseEnd_1599361 < baseStart_1599361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599378 : List Nat := [3, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1599378 : Nat := 118140960795 + 1599378 * 2 ^ 59
def prefixEnd_1599378 : Nat := 4983230072969 + 3 ^ 40 * 1599378 * 2
def baseEnd_1599378 : Nat := 364999849878554959964267

theorem tailTrace_1599378 : CollatzResearch.WordTrace tailWord_1599378 prefixEnd_1599378 364999849878554959964267 := by
  unfold tailWord_1599378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583526999933533215191697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38889405333156088573844525 14583526999933533215191697)
  ·
    refine ⟨10937645249950149911393773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14583526999933533215191697 10937645249950149911393773)
    ·
      refine ⟨4101616968731306216772665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10937645249950149911393773 4101616968731306216772665)
      ·
        refine ⟨3076212726548479662579499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4101616968731306216772665 3076212726548479662579499)
        ·
          refine ⟨4614319089822719493869249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076212726548479662579499 4614319089822719493869249)
          ·
            refine ⟨3460739317367039620401937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4614319089822719493869249 3460739317367039620401937)
            ·
              refine ⟨2595554488025279715301453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3460739317367039620401937 2595554488025279715301453)
              ·
                refine ⟨973332933009479893238045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2595554488025279715301453 973332933009479893238045)
                ·
                  refine ⟨364999849878554959964267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973332933009479893238045 364999849878554959964267)
                  ·
                    rfl

theorem cell21_1599378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1599378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599378 prefixEnd_1599378 := by exact prefixLift 1599378
  have htrace : WordTrace (prefixWord ++ tailWord_1599378) baseStart_1599378 baseEnd_1599378 := by
    simpa [prefixWord, tailWord_1599378, baseEnd_1599378] using wordTrace_append hprefix tailTrace_1599378
  have hstable : (prefixWord ++ tailWord_1599378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599378).length < 2 ^ (prefixWord ++ tailWord_1599378).sum := by decide
  have hdescent : baseEnd_1599378 < baseStart_1599378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599496 : List Nat := [2, 1, 3, 2, 1, 2, 2, 5, 3]
def baseStart_1599496 : Nat := 118140960795 + 1599496 * 2 ^ 59
def prefixEnd_1599496 : Nat := 4983230072969 + 3 ^ 40 * 1599496 * 2
def baseEnd_1599496 : Nat := 365026779086212976997359

theorem tailTrace_1599496 : CollatzResearch.WordTrace tailWord_1599496 prefixEnd_1599496 365026779086212976997359 := by
  unfold tailWord_1599496
  simp only [CollatzResearch.WordTrace]
  refine ⟨29169205906653319506781171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38892274542204426009041561 29169205906653319506781171)
  ·
    refine ⟨43753808859979979260171757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29169205906653319506781171 43753808859979979260171757)
    ·
      refine ⟨16407678322492492222564409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43753808859979979260171757 16407678322492492222564409)
      ·
        refine ⟨12305758741869369166923307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16407678322492492222564409 12305758741869369166923307)
        ·
          refine ⟨18458638112804053750384961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12305758741869369166923307 18458638112804053750384961)
          ·
            refine ⟨13843978584603040312788721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18458638112804053750384961 13843978584603040312788721)
            ·
              refine ⟨10382983938452280234591541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13843978584603040312788721 10382983938452280234591541)
              ·
                refine ⟨973404744229901271992957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10382983938452280234591541 973404744229901271992957)
                ·
                  refine ⟨365026779086212976997359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973404744229901271992957 365026779086212976997359)
                  ·
                    rfl

theorem cell21_1599496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_1599496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599496 prefixEnd_1599496 := by exact prefixLift 1599496
  have htrace : WordTrace (prefixWord ++ tailWord_1599496) baseStart_1599496 baseEnd_1599496 := by
    simpa [prefixWord, tailWord_1599496, baseEnd_1599496] using wordTrace_append hprefix tailTrace_1599496
  have hstable : (prefixWord ++ tailWord_1599496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599496).length < 2 ^ (prefixWord ++ tailWord_1599496).sum := by decide
  have hdescent : baseEnd_1599496 < baseStart_1599496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599600 : List Nat := [2, 1, 1, 1, 5, 3, 1, 7]
def baseStart_1599600 : Nat := 118140960795 + 1599600 * 2 ^ 59
def prefixEnd_1599600 : Nat := 4983230072969 + 3 ^ 40 * 1599600 * 2
def baseEnd_1599600 : Nat := 121683504434377302421271

theorem tailTrace_1599600 : CollatzResearch.WordTrace tailWord_1599600 prefixEnd_1599600 121683504434377302421271 := by
  unfold tailWord_1599600
  simp only [CollatzResearch.WordTrace]
  refine ⟨29171102502464932387674127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38894803336619909850232169 29171102502464932387674127)
  ·
    refine ⟨43756653753697398581511191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29171102502464932387674127 43756653753697398581511191)
    ·
      refine ⟨65634980630546097872266787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43756653753697398581511191 65634980630546097872266787)
      ·
        refine ⟨98452470945819146808400181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65634980630546097872266787 98452470945819146808400181)
        ·
          refine ⟨9229919151170545013287517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98452470945819146808400181 9229919151170545013287517)
          ·
            refine ⟨3461219681688954379982819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9229919151170545013287517 3461219681688954379982819)
            ·
              refine ⟨5191829522533431569974229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461219681688954379982819 5191829522533431569974229)
              ·
                refine ⟨121683504434377302421271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5191829522533431569974229 121683504434377302421271)
                ·
                  rfl

theorem cell21_1599600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_1599600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599600 prefixEnd_1599600 := by exact prefixLift 1599600
  have htrace : WordTrace (prefixWord ++ tailWord_1599600) baseStart_1599600 baseEnd_1599600 := by
    simpa [prefixWord, tailWord_1599600, baseEnd_1599600] using wordTrace_append hprefix tailTrace_1599600
  have hstable : (prefixWord ++ tailWord_1599600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599600).length < 2 ^ (prefixWord ++ tailWord_1599600).sum := by decide
  have hdescent : baseEnd_1599600 < baseStart_1599600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599606 : List Nat := [5, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1599606 : Nat := 118140960795 + 1599606 * 2 ^ 59
def prefixEnd_1599606 : Nat := 4983230072969 + 3 ^ 40 * 1599606 * 2
def baseEnd_1599606 : Nat := 365051882584877230163801

theorem tailTrace_1599606 : CollatzResearch.WordTrace tailWord_1599606 prefixEnd_1599606 365051882584877230163801 := by
  unfold tailWord_1599606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646401490181757987504167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38894949228605418533377781 3646401490181757987504167)
  ·
    refine ⟨5469602235272636981256251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3646401490181757987504167 5469602235272636981256251)
    ·
      refine ⟨8204403352908955471884377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5469602235272636981256251 8204403352908955471884377)
      ·
        refine ⟨6153302514681716603913283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8204403352908955471884377 6153302514681716603913283)
        ·
          refine ⟨9229953772022574905869925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6153302514681716603913283 9229953772022574905869925)
          ·
            refine ⟨1730616332254232794850611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9229953772022574905869925 1730616332254232794850611)
            ·
              refine ⟨2595924498381349192275917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730616332254232794850611 2595924498381349192275917)
              ·
                refine ⟨973471686893005947103469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2595924498381349192275917 973471686893005947103469)
                ·
                  refine ⟨365051882584877230163801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973471686893005947103469 365051882584877230163801)
                  ·
                    rfl

theorem cell21_1599606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1599606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599606 prefixEnd_1599606 := by exact prefixLift 1599606
  have htrace : WordTrace (prefixWord ++ tailWord_1599606) baseStart_1599606 baseEnd_1599606 := by
    simpa [prefixWord, tailWord_1599606, baseEnd_1599606] using wordTrace_append hprefix tailTrace_1599606
  have hstable : (prefixWord ++ tailWord_1599606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599606).length < 2 ^ (prefixWord ++ tailWord_1599606).sum := by decide
  have hdescent : baseEnd_1599606 < baseStart_1599606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599617 : List Nat := [1, 2, 4, 2, 3, 2, 7]
def baseStart_1599617 : Nat := 118140960795 + 1599617 * 2 ^ 59
def prefixEnd_1599617 : Nat := 4983230072969 + 3 ^ 40 * 1599617 * 2
def baseEnd_1599617 : Nat := 40561599214971517275605

theorem tailTrace_1599617 : CollatzResearch.WordTrace tailWord_1599617 prefixEnd_1599617 40561599214971517275605 := by
  unfold tailWord_1599617
  simp only [CollatzResearch.WordTrace]
  refine ⟨58342825045868276678717105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38895216697245517785811403 58342825045868276678717105)
  ·
    refine ⟨43757118784401207509037829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58342825045868276678717105 43757118784401207509037829)
    ·
      refine ⟨8204459772075226407944593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43757118784401207509037829 8204459772075226407944593)
      ·
        refine ⟨6153344829056419805958445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8204459772075226407944593 6153344829056419805958445)
        ·
          refine ⟨2307504310896157427234417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6153344829056419805958445 2307504310896157427234417)
          ·
            refine ⟨1730628233172118070425813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307504310896157427234417 1730628233172118070425813)
            ·
              refine ⟨40561599214971517275605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1730628233172118070425813 40561599214971517275605)
              ·
                rfl

theorem cell21_1599617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 7].length) (baseStart_1599617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599617 prefixEnd_1599617 := by exact prefixLift 1599617
  have htrace : WordTrace (prefixWord ++ tailWord_1599617) baseStart_1599617 baseEnd_1599617 := by
    simpa [prefixWord, tailWord_1599617, baseEnd_1599617] using wordTrace_append hprefix tailTrace_1599617
  have hstable : (prefixWord ++ tailWord_1599617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599617).length < 2 ^ (prefixWord ++ tailWord_1599617).sum := by decide
  have hdescent : baseEnd_1599617 < baseStart_1599617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599676 : List Nat := [2, 2, 2, 3, 3, 9]
def baseStart_1599676 : Nat := 118140960795 + 1599676 * 2 ^ 59
def prefixEnd_1599676 : Nat := 4983230072969 + 3 ^ 40 * 1599676 * 2
def baseEnd_1599676 : Nat := 13521031760687876444333

theorem tailTrace_1599676 : CollatzResearch.WordTrace tailWord_1599676 prefixEnd_1599676 13521031760687876444333 := by
  unfold tailWord_1599676
  simp only [CollatzResearch.WordTrace]
  refine ⟨29172488476327264877557441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38896651301769686503409921 29172488476327264877557441)
  ·
    refine ⟨21879366357245448658168081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29172488476327264877557441 21879366357245448658168081)
    ·
      refine ⟨16409524767934086493626061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21879366357245448658168081 16409524767934086493626061)
      ·
        refine ⟨6153571787975282435109773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16409524767934086493626061 6153571787975282435109773)
        ·
          refine ⟨2307589420490730913166165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6153571787975282435109773 2307589420490730913166165)
          ·
            refine ⟨13521031760687876444333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2307589420490730913166165 13521031760687876444333)
            ·
              rfl

theorem cell21_1599676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 9].length) (baseStart_1599676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599676 prefixEnd_1599676 := by exact prefixLift 1599676
  have htrace : WordTrace (prefixWord ++ tailWord_1599676) baseStart_1599676 baseEnd_1599676 := by
    simpa [prefixWord, tailWord_1599676, baseEnd_1599676] using wordTrace_append hprefix tailTrace_1599676
  have hstable : (prefixWord ++ tailWord_1599676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599676).length < 2 ^ (prefixWord ++ tailWord_1599676).sum := by decide
  have hdescent : baseEnd_1599676 < baseStart_1599676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599724 : List Nat := [2, 2, 1, 1, 2, 3, 4, 3, 3]
def baseStart_1599724 : Nat := 118140960795 + 1599724 * 2 ^ 59
def prefixEnd_1599724 : Nat := 4983230072969 + 3 ^ 40 * 1599724 * 2
def baseEnd_1599724 : Nat := 365078811792535247196893

theorem tailTrace_1599724 : CollatzResearch.WordTrace tailWord_1599724 prefixEnd_1599724 365078811792535247196893 := by
  unfold tailWord_1599724
  simp only [CollatzResearch.WordTrace]
  refine ⟨29173363828240316976431113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38897818437653755968574817 29173363828240316976431113)
  ·
    refine ⟨21880022871180237732323335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29173363828240316976431113 21880022871180237732323335)
    ·
      refine ⟨32820034306770356598485003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21880022871180237732323335 32820034306770356598485003)
      ·
        refine ⟨49230051460155534897727505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32820034306770356598485003 49230051460155534897727505)
        ·
          refine ⟨36922538595116651173295629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49230051460155534897727505 36922538595116651173295629)
          ·
            refine ⟨13845951973168744189985861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36922538595116651173295629 13845951973168744189985861)
            ·
              refine ⟨2596115994969139535622349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13845951973168744189985861 2596115994969139535622349)
              ·
                refine ⟨973543498113427325858381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2596115994969139535622349 973543498113427325858381)
                ·
                  refine ⟨365078811792535247196893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973543498113427325858381 365078811792535247196893)
                  ·
                    rfl

theorem cell21_1599724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_1599724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599724 prefixEnd_1599724 := by exact prefixLift 1599724
  have htrace : WordTrace (prefixWord ++ tailWord_1599724) baseStart_1599724 baseEnd_1599724 := by
    simpa [prefixWord, tailWord_1599724, baseEnd_1599724] using wordTrace_append hprefix tailTrace_1599724
  have hstable : (prefixWord ++ tailWord_1599724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599724).length < 2 ^ (prefixWord ++ tailWord_1599724).sum := by decide
  have hdescent : baseEnd_1599724 < baseStart_1599724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599738 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1599738 : Nat := 118140960795 + 1599738 * 2 ^ 59
def prefixEnd_1599738 : Nat := 4983230072969 + 3 ^ 40 * 1599738 * 2
def baseEnd_1599738 : Nat := 365082006783274333963531

theorem tailTrace_1599738 : CollatzResearch.WordTrace tailWord_1599738 prefixEnd_1599738 365082006783274333963531 := by
  unfold tailWord_1599738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14586809569607478585967967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38898158852286609562581245 14586809569607478585967967)
  ·
    refine ⟨21880214354411217878951951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14586809569607478585967967 21880214354411217878951951)
    ·
      refine ⟨32820321531616826818427927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21880214354411217878951951 32820321531616826818427927)
      ·
        refine ⟨49230482297425240227641891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32820321531616826818427927 49230482297425240227641891)
        ·
          refine ⟨73845723446137860341462837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49230482297425240227641891 73845723446137860341462837)
          ·
            refine ⟨6923036573075424407012141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73845723446137860341462837 6923036573075424407012141)
            ·
              refine ⟨2596138714903284152629553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6923036573075424407012141 2596138714903284152629553)
              ·
                refine ⟨1947104036177463114472165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596138714903284152629553 1947104036177463114472165)
                ·
                  refine ⟨365082006783274333963531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947104036177463114472165 365082006783274333963531)
                  ·
                    rfl

theorem cell21_1599738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1599738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599738 prefixEnd_1599738 := by exact prefixLift 1599738
  have htrace : WordTrace (prefixWord ++ tailWord_1599738) baseStart_1599738 baseEnd_1599738 := by
    simpa [prefixWord, tailWord_1599738, baseEnd_1599738] using wordTrace_append hprefix tailTrace_1599738
  have hstable : (prefixWord ++ tailWord_1599738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599738).length < 2 ^ (prefixWord ++ tailWord_1599738).sum := by decide
  have hdescent : baseEnd_1599738 < baseStart_1599738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599786 : List Nat := [3, 1, 4, 2, 3, 1, 7]
def baseStart_1599786 : Nat := 118140960795 + 1599786 * 2 ^ 59
def prefixEnd_1599786 : Nat := 4983230072969 + 3 ^ 40 * 1599786 * 2
def baseEnd_1599786 : Nat := 40565884559692990795937

theorem tailTrace_1599786 : CollatzResearch.WordTrace tailWord_1599786 prefixEnd_1599786 40565884559692990795937 := by
  unfold tailWord_1599786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587247245564004635404803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38899325988170679027746141 14587247245564004635404803)
  ·
    refine ⟨21880870868346006953107205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14587247245564004635404803 21880870868346006953107205)
    ·
      refine ⟨4102663287814876303707601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21880870868346006953107205 4102663287814876303707601)
      ·
        refine ⟨3076997465861157227780701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4102663287814876303707601 3076997465861157227780701)
        ·
          refine ⟨1153874049697933960417763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3076997465861157227780701 1153874049697933960417763)
          ·
            refine ⟨1730811074546900940626645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153874049697933960417763 1730811074546900940626645)
            ·
              refine ⟨40565884559692990795937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1730811074546900940626645 40565884559692990795937)
              ·
                rfl

theorem cell21_1599786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 7].length) (baseStart_1599786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599786 prefixEnd_1599786 := by exact prefixLift 1599786
  have htrace : WordTrace (prefixWord ++ tailWord_1599786) baseStart_1599786 baseEnd_1599786 := by
    simpa [prefixWord, tailWord_1599786, baseEnd_1599786] using wordTrace_append hprefix tailTrace_1599786
  have hstable : (prefixWord ++ tailWord_1599786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599786).length < 2 ^ (prefixWord ++ tailWord_1599786).sum := by decide
  have hdescent : baseEnd_1599786 < baseStart_1599786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599797 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 6]
def baseStart_1599797 : Nat := 118140960795 + 1599797 * 2 ^ 59
def prefixEnd_1599797 : Nat := 4983230072969 + 3 ^ 40 * 1599797 * 2
def baseEnd_1599797 : Nat := 365095471387103342480077

theorem tailTrace_1599797 : CollatzResearch.WordTrace tailWord_1599797 prefixEnd_1599797 365095471387103342480077 := by
  unfold tailWord_1599797
  simp only [CollatzResearch.WordTrace]
  refine ⟨58349390185216167420269645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38899593456810778280179763 58349390185216167420269645)
  ·
    refine ⟨21881021319456062782601117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58349390185216167420269645 21881021319456062782601117)
    ·
      refine ⟨8205382994796023543475419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21881021319456062782601117 8205382994796023543475419)
      ·
        refine ⟨12308074492194035315213129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8205382994796023543475419 12308074492194035315213129)
        ·
          refine ⟨9231055869145526486409847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12308074492194035315213129 9231055869145526486409847)
          ·
            refine ⟨13846583803718289729614771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9231055869145526486409847 13846583803718289729614771)
            ·
              refine ⟨20769875705577434594422157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846583803718289729614771 20769875705577434594422157)
              ·
                refine ⟨7788703389591537972908309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20769875705577434594422157 7788703389591537972908309)
                ·
                  refine ⟨365095471387103342480077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7788703389591537972908309 365095471387103342480077)
                  ·
                    rfl

theorem cell21_1599797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_1599797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599797 prefixEnd_1599797 := by exact prefixLift 1599797
  have htrace : WordTrace (prefixWord ++ tailWord_1599797) baseStart_1599797 baseEnd_1599797 := by
    simpa [prefixWord, tailWord_1599797, baseEnd_1599797] using wordTrace_append hprefix tailTrace_1599797
  have hstable : (prefixWord ++ tailWord_1599797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599797).length < 2 ^ (prefixWord ++ tailWord_1599797).sum := by decide
  have hdescent : baseEnd_1599797 < baseStart_1599797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599811 : List Nat := [1, 1, 1, 3, 1, 3, 3, 8]
def baseStart_1599811 : Nat := 118140960795 + 1599811 * 2 ^ 59
def prefixEnd_1599811 : Nat := 4983230072969 + 3 ^ 40 * 1599811 * 2
def baseEnd_1599811 : Nat := 121699555459280809748905

theorem tailTrace_1599811 : CollatzResearch.WordTrace tailWord_1599811 prefixEnd_1599811 121699555459280809748905 := by
  unfold tailWord_1599811
  simp only [CollatzResearch.WordTrace]
  refine ⟨58349900807165447811279287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38899933871443631874186191 58349900807165447811279287)
  ·
    refine ⟨87524851210748171716918931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58349900807165447811279287 87524851210748171716918931)
    ·
      refine ⟨131287276816122257575378397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87524851210748171716918931 131287276816122257575378397)
      ·
        refine ⟨49232728806045846590766899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131287276816122257575378397 49232728806045846590766899)
        ·
          refine ⟨73849093209068769886150349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49232728806045846590766899 73849093209068769886150349)
          ·
            refine ⟨27693409953400788707306381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73849093209068769886150349 27693409953400788707306381)
            ·
              refine ⟨10385028732525295765239893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27693409953400788707306381 10385028732525295765239893)
              ·
                refine ⟨121699555459280809748905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10385028732525295765239893 121699555459280809748905)
                ·
                  rfl

theorem cell21_1599811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_1599811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599811 prefixEnd_1599811 := by exact prefixLift 1599811
  have htrace : WordTrace (prefixWord ++ tailWord_1599811) baseStart_1599811 baseEnd_1599811 := by
    simpa [prefixWord, tailWord_1599811, baseEnd_1599811] using wordTrace_append hprefix tailTrace_1599811
  have hstable : (prefixWord ++ tailWord_1599811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599811).length < 2 ^ (prefixWord ++ tailWord_1599811).sum := by decide
  have hdescent : baseEnd_1599811 < baseStart_1599811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599828 : List Nat := [2, 4, 1, 1, 2, 2, 2, 7]
def baseStart_1599828 : Nat := 118140960795 + 1599828 * 2 ^ 59
def prefixEnd_1599828 : Nat := 4983230072969 + 3 ^ 40 * 1599828 * 2
def baseEnd_1599828 : Nat := 121700848669818059154449

theorem tailTrace_1599828 : CollatzResearch.WordTrace tailWord_1599828 prefixEnd_1599828 121700848669818059154449 := by
  unfold tailWord_1599828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29175260424051929857324069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38900347232069239809765425 29175260424051929857324069)
  ·
    refine ⟨5470361329509736848248263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29175260424051929857324069 5470361329509736848248263)
    ·
      refine ⟨8205541994264605272372395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5470361329509736848248263 8205541994264605272372395)
      ·
        refine ⟨12308312991396907908558593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8205541994264605272372395 12308312991396907908558593)
        ·
          refine ⟨9231234743547680931418945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12308312991396907908558593 9231234743547680931418945)
          ·
            refine ⟨6923426057660760698564209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9231234743547680931418945 6923426057660760698564209)
            ·
              refine ⟨5192569543245570523923157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6923426057660760698564209 5192569543245570523923157)
              ·
                refine ⟨121700848669818059154449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5192569543245570523923157 121700848669818059154449)
                ·
                  rfl

theorem cell21_1599828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_1599828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599828 prefixEnd_1599828 := by exact prefixLift 1599828
  have htrace : WordTrace (prefixWord ++ tailWord_1599828) baseStart_1599828 baseEnd_1599828 := by
    simpa [prefixWord, tailWord_1599828, baseEnd_1599828] using wordTrace_append hprefix tailTrace_1599828
  have hstable : (prefixWord ++ tailWord_1599828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599828).length < 2 ^ (prefixWord ++ tailWord_1599828).sum := by decide
  have hdescent : baseEnd_1599828 < baseStart_1599828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599859 : List Nat := [1, 1, 1, 2, 2, 1, 2, 8, 3]
def baseStart_1599859 : Nat := 118140960795 + 1599859 * 2 ^ 59
def prefixEnd_1599859 : Nat := 4983230072969 + 3 ^ 40 * 1599859 * 2
def baseEnd_1599859 : Nat := 365109620631805012446617

theorem tailTrace_1599859 : CollatzResearch.WordTrace tailWord_1599859 prefixEnd_1599859 365109620631805012446617 := by
  unfold tailWord_1599859
  simp only [CollatzResearch.WordTrace]
  refine ⟨58351651510991552009026631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38901101007327701339351087 58351651510991552009026631)
  ·
    refine ⟨87527477266487328013539947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58351651510991552009026631 87527477266487328013539947)
    ·
      refine ⟨131291215899730992020309921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87527477266487328013539947 131291215899730992020309921)
      ·
        refine ⟨98468411924798244015232441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131291215899730992020309921 98468411924798244015232441)
        ·
          refine ⟨73851308943598683011424331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98468411924798244015232441 73851308943598683011424331)
          ·
            refine ⟨110776963415398024517136497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73851308943598683011424331 110776963415398024517136497)
            ·
              refine ⟨83082722561548518387852373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110776963415398024517136497 83082722561548518387852373)
              ·
                refine ⟨973625655018146699857645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 83082722561548518387852373 973625655018146699857645)
                ·
                  refine ⟨365109620631805012446617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973625655018146699857645 365109620631805012446617)
                  ·
                    rfl

theorem cell21_1599859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 3].length) (baseStart_1599859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1599859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1599859 prefixEnd_1599859 := by exact prefixLift 1599859
  have htrace : WordTrace (prefixWord ++ tailWord_1599859) baseStart_1599859 baseEnd_1599859 := by
    simpa [prefixWord, tailWord_1599859, baseEnd_1599859] using wordTrace_append hprefix tailTrace_1599859
  have hstable : (prefixWord ++ tailWord_1599859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599859).length < 2 ^ (prefixWord ++ tailWord_1599859).sum := by decide
  have hdescent : baseEnd_1599859 < baseStart_1599859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600028 : List Nat := [2, 2, 3, 1, 2, 3, 1, 4, 3]
def baseStart_1600028 : Nat := 118140960795 + 1600028 * 2 ^ 59
def prefixEnd_1600028 : Nat := 4983230072969 + 3 ^ 40 * 1600028 * 2
def baseEnd_1600028 : Nat := 365148188734298274129605

theorem tailTrace_1600028 : CollatzResearch.WordTrace tailWord_1600028 prefixEnd_1600028 365148188734298274129605 := by
  unfold tailWord_1600028
  simp only [CollatzResearch.WordTrace]
  refine ⟨29178907723689646935964369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38905210298252862581285825 29178907723689646935964369)
  ·
    refine ⟨21884180792767235201973277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29178907723689646935964369 21884180792767235201973277)
    ·
      refine ⟨8206567797287713200739979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21884180792767235201973277 8206567797287713200739979)
      ·
        refine ⟨12309851695931569801109969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8206567797287713200739979 12309851695931569801109969)
        ·
          refine ⟨9232388771948677350832477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12309851695931569801109969 9232388771948677350832477)
          ·
            refine ⟨3462145789480754006562179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9232388771948677350832477 3462145789480754006562179)
            ·
              refine ⟨5193218684221131009843269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462145789480754006562179 5193218684221131009843269)
              ·
                refine ⟨973728503291462064345613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5193218684221131009843269 973728503291462064345613)
                ·
                  refine ⟨365148188734298274129605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973728503291462064345613 365148188734298274129605)
                  ·
                    rfl

theorem cell21_1600028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_1600028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600028 prefixEnd_1600028 := by exact prefixLift 1600028
  have htrace : WordTrace (prefixWord ++ tailWord_1600028) baseStart_1600028 baseEnd_1600028 := by
    simpa [prefixWord, tailWord_1600028, baseEnd_1600028] using wordTrace_append hprefix tailTrace_1600028
  have hstable : (prefixWord ++ tailWord_1600028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600028).length < 2 ^ (prefixWord ++ tailWord_1600028).sum := by decide
  have hdescent : baseEnd_1600028 < baseStart_1600028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600042 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1600042 : Nat := 118140960795 + 1600042 * 2 ^ 59
def prefixEnd_1600042 : Nat := 4983230072969 + 3 ^ 40 * 1600042 * 2
def baseEnd_1600042 : Nat := 365151383725037360896243

theorem tailTrace_1600042 : CollatzResearch.WordTrace tailWord_1600042 prefixEnd_1600042 365151383725037360896243 := by
  unfold tailWord_1600042
  simp only [CollatzResearch.WordTrace]
  refine ⟨14589581517332143565734595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38905550712885716175292253 14589581517332143565734595)
  ·
    refine ⟨21884372275998215348601893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14589581517332143565734595 21884372275998215348601893)
    ·
      refine ⟨4103319801749665377862855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21884372275998215348601893 4103319801749665377862855)
      ·
        refine ⟨6154979702624498066794283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103319801749665377862855 6154979702624498066794283)
        ·
          refine ⟨9232469553936747100191425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154979702624498066794283 9232469553936747100191425)
          ·
            refine ⟨6924352165452560325143569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9232469553936747100191425 6924352165452560325143569)
            ·
              refine ⟨5193264124089420243857677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6924352165452560325143569 5193264124089420243857677)
              ·
                refine ⟨1947474046533532591446629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5193264124089420243857677 1947474046533532591446629)
                ·
                  refine ⟨365151383725037360896243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947474046533532591446629 365151383725037360896243)
                  ·
                    rfl

theorem cell21_1600042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1600042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600042 prefixEnd_1600042 := by exact prefixLift 1600042
  have htrace : WordTrace (prefixWord ++ tailWord_1600042) baseStart_1600042 baseEnd_1600042 := by
    simpa [prefixWord, tailWord_1600042, baseEnd_1600042] using wordTrace_append hprefix tailTrace_1600042
  have hstable : (prefixWord ++ tailWord_1600042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600042).length < 2 ^ (prefixWord ++ tailWord_1600042).sum := by decide
  have hdescent : baseEnd_1600042 < baseStart_1600042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600056 : List Nat := [2, 1, 2, 1, 4, 1, 5, 5]
def baseStart_1600056 : Nat := 118140960795 + 1600056 * 2 ^ 59
def prefixEnd_1600056 : Nat := 4983230072969 + 3 ^ 40 * 1600056 * 2
def baseEnd_1600056 : Nat := 121718192905258815887627

theorem tailTrace_1600056 : CollatzResearch.WordTrace tailWord_1600056 prefixEnd_1600056 121718192905258815887627 := by
  unfold tailWord_1600056
  simp only [CollatzResearch.WordTrace]
  refine ⟨29179418345638927326974011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38905891127518569769298681 29179418345638927326974011)
  ·
    refine ⟨43769127518458390990461017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29179418345638927326974011 43769127518458390990461017)
    ·
      refine ⟨32826845638843793242845763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43769127518458390990461017 32826845638843793242845763)
      ·
        refine ⟨49240268458265689864268645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32826845638843793242845763 49240268458265689864268645)
        ·
          refine ⟨9232550335924816849550371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49240268458265689864268645 9232550335924816849550371)
          ·
            refine ⟨13848825503887225274325557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232550335924816849550371 13848825503887225274325557)
            ·
              refine ⟨1298327390989427369468021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13848825503887225274325557 1298327390989427369468021)
              ·
                refine ⟨121718192905258815887627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1298327390989427369468021 121718192905258815887627)
                ·
                  rfl

theorem cell21_1600056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_1600056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600056 prefixEnd_1600056 := by exact prefixLift 1600056
  have htrace : WordTrace (prefixWord ++ tailWord_1600056) baseStart_1600056 baseEnd_1600056 := by
    simpa [prefixWord, tailWord_1600056, baseEnd_1600056] using wordTrace_append hprefix tailTrace_1600056
  have hstable : (prefixWord ++ tailWord_1600056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600056).length < 2 ^ (prefixWord ++ tailWord_1600056).sum := by decide
  have hdescent : baseEnd_1600056 < baseStart_1600056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600062 : List Nat := [4, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1600062 : Nat := 118140960795 + 1600062 * 2 ^ 59
def prefixEnd_1600062 : Nat := 4983230072969 + 3 ^ 40 * 1600062 * 2
def baseEnd_1600062 : Nat := 365155947997521770562869

theorem tailTrace_1600062 : CollatzResearch.WordTrace tailWord_1600062 prefixEnd_1600062 365155947997521770562869 := by
  unfold tailWord_1600062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294881941157014709833305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38906037019504078452444293 7294881941157014709833305)
  ·
    refine ⟨5471161455867761032374979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7294881941157014709833305 5471161455867761032374979)
    ·
      refine ⟨8206742183801641548562469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5471161455867761032374979 8206742183801641548562469)
      ·
        refine ⟨1538764159462807790355463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8206742183801641548562469 1538764159462807790355463)
        ·
          refine ⟨2308146239194211685533195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538764159462807790355463 2308146239194211685533195)
          ·
            refine ⟨3462219358791317528299793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308146239194211685533195 3462219358791317528299793)
            ·
              refine ⟨2596664519093488146224845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462219358791317528299793 2596664519093488146224845)
              ·
                refine ⟨973749194660058054834317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2596664519093488146224845 973749194660058054834317)
                ·
                  refine ⟨365155947997521770562869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973749194660058054834317 365155947997521770562869)
                  ·
                    rfl

theorem cell21_1600062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1600062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600062 prefixEnd_1600062 := by exact prefixLift 1600062
  have htrace : WordTrace (prefixWord ++ tailWord_1600062) baseStart_1600062 baseEnd_1600062 := by
    simpa [prefixWord, tailWord_1600062, baseEnd_1600062] using wordTrace_append hprefix tailTrace_1600062
  have hstable : (prefixWord ++ tailWord_1600062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600062).length < 2 ^ (prefixWord ++ tailWord_1600062).sum := by decide
  have hdescent : baseEnd_1600062 < baseStart_1600062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600087 : List Nat := [1, 1, 3, 2, 2, 2, 1, 6, 3]
def baseStart_1600087 : Nat := 118140960795 + 1600087 * 2 ^ 59
def prefixEnd_1600087 : Nat := 4983230072969 + 3 ^ 40 * 1600087 * 2
def baseEnd_1600087 : Nat := 365161653338127282646151

theorem tailTrace_1600087 : CollatzResearch.WordTrace tailWord_1600087 prefixEnd_1600087 365161653338127282646151 := by
  unfold tailWord_1600087
  simp only [CollatzResearch.WordTrace]
  refine ⟨58359967354165546948326515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38906644902777031298884343 58359967354165546948326515)
  ·
    refine ⟨87539951031248320422489773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58359967354165546948326515 87539951031248320422489773)
    ·
      refine ⟨32827481636718120158433665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87539951031248320422489773 32827481636718120158433665)
      ·
        refine ⟨24620611227538590118825249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32827481636718120158433665 24620611227538590118825249)
        ·
          refine ⟨18465458420653942589118937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24620611227538590118825249 18465458420653942589118937)
          ·
            refine ⟨13849093815490456941839203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18465458420653942589118937 13849093815490456941839203)
            ·
              refine ⟨20773640723235685412758805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13849093815490456941839203 20773640723235685412758805)
              ·
                refine ⟨973764408901672753723069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20773640723235685412758805 973764408901672753723069)
                ·
                  refine ⟨365161653338127282646151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973764408901672753723069 365161653338127282646151)
                  ·
                    rfl

theorem cell21_1600087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 3].length) (baseStart_1600087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600087 prefixEnd_1600087 := by exact prefixLift 1600087
  have htrace : WordTrace (prefixWord ++ tailWord_1600087) baseStart_1600087 baseEnd_1600087 := by
    simpa [prefixWord, tailWord_1600087, baseEnd_1600087] using wordTrace_append hprefix tailTrace_1600087
  have hstable : (prefixWord ++ tailWord_1600087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600087).length < 2 ^ (prefixWord ++ tailWord_1600087).sum := by decide
  have hdescent : baseEnd_1600087 < baseStart_1600087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600132 : List Nat := [2, 3, 2, 1, 3, 3, 7]
def baseStart_1600132 : Nat := 118140960795 + 1600132 * 2 ^ 59
def prefixEnd_1600132 : Nat := 4983230072969 + 3 ^ 40 * 1600132 * 2
def baseEnd_1600132 : Nat := 40574658105690800488451

theorem tailTrace_1600132 : CollatzResearch.WordTrace tailWord_1600132 prefixEnd_1600132 40574658105690800488451 := by
  unfold tailWord_1600132
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180804319501259816857325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38907739092668346422476433 29180804319501259816857325)
  ·
    refine ⟨10942801619812972431321497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29180804319501259816857325 10942801619812972431321497)
    ·
      refine ⟨8207101214859729323491123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10942801619812972431321497 8207101214859729323491123)
      ·
        refine ⟨12310651822289593985236685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8207101214859729323491123 12310651822289593985236685)
        ·
          refine ⟨4616494433358597744463757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12310651822289593985236685 4616494433358597744463757)
          ·
            refine ⟨1731185412509474154173909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4616494433358597744463757 1731185412509474154173909)
            ·
              refine ⟨40574658105690800488451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1731185412509474154173909 40574658105690800488451)
              ·
                rfl

theorem cell21_1600132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 7].length) (baseStart_1600132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600132 prefixEnd_1600132 := by exact prefixLift 1600132
  have htrace : WordTrace (prefixWord ++ tailWord_1600132) baseStart_1600132 baseEnd_1600132 := by
    simpa [prefixWord, tailWord_1600132, baseEnd_1600132] using wordTrace_append hprefix tailTrace_1600132
  have hstable : (prefixWord ++ tailWord_1600132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600132).length < 2 ^ (prefixWord ++ tailWord_1600132).sum := by decide
  have hdescent : baseEnd_1600132 < baseStart_1600132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600236 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1600236 : Nat := 118140960795 + 1600236 * 2 ^ 59
def prefixEnd_1600236 : Nat := 4983230072969 + 3 ^ 40 * 1600236 * 2
def baseEnd_1600236 : Nat := 365195657168136134662513

theorem tailTrace_1600236 : CollatzResearch.WordTrace tailWord_1600236 prefixEnd_1600236 365195657168136134662513 := by
  unfold tailWord_1600236
  simp only [CollatzResearch.WordTrace]
  refine ⟨29182700915312872697750281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38910267887083830263667041 29182700915312872697750281)
  ·
    refine ⟨21887025686484654523312711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29182700915312872697750281 21887025686484654523312711)
    ·
      refine ⟨32830538529726981784969067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21887025686484654523312711 32830538529726981784969067)
      ·
        refine ⟨49245807794590472677453601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32830538529726981784969067 49245807794590472677453601)
        ·
          refine ⟨36934355845942854508090201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49245807794590472677453601 36934355845942854508090201)
          ·
            refine ⟨27700766884457140881067651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36934355845942854508090201 27700766884457140881067651)
            ·
              refine ⟨41551150326685711321601477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27700766884457140881067651 41551150326685711321601477)
              ·
                refine ⟨7790840686253570872800277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41551150326685711321601477 7790840686253570872800277)
                ·
                  refine ⟨365195657168136134662513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7790840686253570872800277 365195657168136134662513)
                  ·
                    rfl

theorem cell21_1600236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1600236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600236 prefixEnd_1600236 := by exact prefixLift 1600236
  have htrace : WordTrace (prefixWord ++ tailWord_1600236) baseStart_1600236 baseEnd_1600236 := by
    simpa [prefixWord, tailWord_1600236, baseEnd_1600236] using wordTrace_append hprefix tailTrace_1600236
  have hstable : (prefixWord ++ tailWord_1600236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600236).length < 2 ^ (prefixWord ++ tailWord_1600236).sum := by decide
  have hdescent : baseEnd_1600236 < baseStart_1600236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600239 : List Nat := [1, 1, 2, 1, 5, 2, 1, 5, 3]
def baseStart_1600239 : Nat := 118140960795 + 1600239 * 2 ^ 59
def prefixEnd_1600239 : Nat := 4983230072969 + 3 ^ 40 * 1600239 * 2
def baseEnd_1600239 : Nat := 365196341809008796112507

theorem tailTrace_1600239 : CollatzResearch.WordTrace tailWord_1600239 prefixEnd_1600239 365196341809008796112507 := by
  unfold tailWord_1600239
  simp only [CollatzResearch.WordTrace]
  refine ⟨58365511249614876907859771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38910340833076584605239847 58365511249614876907859771)
  ·
    refine ⟨87548266874422315361789657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58365511249614876907859771 87548266874422315361789657)
    ·
      refine ⟨65661200155816736521342243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87548266874422315361789657 65661200155816736521342243)
      ·
        refine ⟨98491800233725104782013365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65661200155816736521342243 98491800233725104782013365)
        ·
          refine ⟨9233606271911728573313753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98491800233725104782013365 9233606271911728573313753)
          ·
            refine ⟨6925204703933796429985315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9233606271911728573313753 6925204703933796429985315)
            ·
              refine ⟨10387807055900694644977973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6925204703933796429985315 10387807055900694644977973)
              ·
                refine ⟨973856911490690122966685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10387807055900694644977973 973856911490690122966685)
                ·
                  refine ⟨365196341809008796112507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973856911490690122966685 365196341809008796112507)
                  ·
                    rfl

theorem cell21_1600239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 3].length) (baseStart_1600239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600239 prefixEnd_1600239 := by exact prefixLift 1600239
  have htrace : WordTrace (prefixWord ++ tailWord_1600239) baseStart_1600239 baseEnd_1600239 := by
    simpa [prefixWord, tailWord_1600239, baseEnd_1600239] using wordTrace_append hprefix tailTrace_1600239
  have hstable : (prefixWord ++ tailWord_1600239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600239).length < 2 ^ (prefixWord ++ tailWord_1600239).sum := by decide
  have hdescent : baseEnd_1600239 < baseStart_1600239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600245 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 4]
def baseStart_1600245 : Nat := 118140960795 + 1600245 * 2 ^ 59
def prefixEnd_1600245 : Nat := 4983230072969 + 3 ^ 40 * 1600245 * 2
def baseEnd_1600245 : Nat := 365197711090754119012495

theorem tailTrace_1600245 : CollatzResearch.WordTrace tailWord_1600245 prefixEnd_1600245 365197711090754119012495 := by
  unfold tailWord_1600245
  simp only [CollatzResearch.WordTrace]
  refine ⟨58365730087593139932578189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38910486725062093288385459 58365730087593139932578189)
  ·
    refine ⟨21887148782847427474716821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58365730087593139932578189 21887148782847427474716821)
    ·
      refine ⟨1025960099195973162877351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21887148782847427474716821 1025960099195973162877351)
      ·
        refine ⟨1538940148793959744316027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025960099195973162877351 1538940148793959744316027)
        ·
          refine ⟨2308410223190939616474041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538940148793959744316027 2308410223190939616474041)
          ·
            refine ⟨1731307667393204712355531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308410223190939616474041 1731307667393204712355531)
            ·
              refine ⟨2596961501089807068533297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731307667393204712355531 2596961501089807068533297)
              ·
                refine ⟨1947721125817355301399973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596961501089807068533297 1947721125817355301399973)
                ·
                  refine ⟨365197711090754119012495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947721125817355301399973 365197711090754119012495)
                  ·
                    rfl

theorem cell21_1600245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_1600245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600245 prefixEnd_1600245 := by exact prefixLift 1600245
  have htrace : WordTrace (prefixWord ++ tailWord_1600245) baseStart_1600245 baseEnd_1600245 := by
    simpa [prefixWord, tailWord_1600245, baseEnd_1600245] using wordTrace_append hprefix tailTrace_1600245
  have hstable : (prefixWord ++ tailWord_1600245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600245).length < 2 ^ (prefixWord ++ tailWord_1600245).sum := by decide
  have hdescent : baseEnd_1600245 < baseStart_1600245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600281 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 7]
def baseStart_1600281 : Nat := 118140960795 + 1600281 * 2 ^ 59
def prefixEnd_1600281 : Nat := 4983230072969 + 3 ^ 40 * 1600281 * 2
def baseEnd_1600281 : Nat := 365205926781226056412421

theorem tailTrace_1600281 : CollatzResearch.WordTrace tailWord_1600281 prefixEnd_1600281 365205926781226056412421 := by
  unfold tailWord_1600281
  simp only [CollatzResearch.WordTrace]
  refine ⟨58367043115462718080888697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38911362076975145387259131 58367043115462718080888697)
  ·
    refine ⟨43775282336597038560666523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58367043115462718080888697 43775282336597038560666523)
    ·
      refine ⟨65662923504895557840999785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43775282336597038560666523 65662923504895557840999785)
      ·
        refine ⟨49247192628671668380749839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65662923504895557840999785 49247192628671668380749839)
        ·
          refine ⟨73870788943007502571124759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49247192628671668380749839 73870788943007502571124759)
          ·
            refine ⟨110806183414511253856687139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73870788943007502571124759 110806183414511253856687139)
            ·
              refine ⟨166209275121766880785030709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110806183414511253856687139 166209275121766880785030709)
              ·
                refine ⟨15582119542665645073596629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166209275121766880785030709 15582119542665645073596629)
                ·
                  refine ⟨365205926781226056412421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15582119542665645073596629 365205926781226056412421)
                  ·
                    rfl

theorem cell21_1600281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_1600281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600281 prefixEnd_1600281 := by exact prefixLift 1600281
  have htrace : WordTrace (prefixWord ++ tailWord_1600281) baseStart_1600281 baseEnd_1600281 := by
    simpa [prefixWord, tailWord_1600281, baseEnd_1600281] using wordTrace_append hprefix tailTrace_1600281
  have hstable : (prefixWord ++ tailWord_1600281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600281).length < 2 ^ (prefixWord ++ tailWord_1600281).sum := by decide
  have hdescent : baseEnd_1600281 < baseStart_1600281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600284 : List Nat := [2, 2, 3, 1, 1, 3, 4, 5]
def baseStart_1600284 : Nat := 118140960795 + 1600284 * 2 ^ 59
def prefixEnd_1600284 : Nat := 4983230072969 + 3 ^ 40 * 1600284 * 2
def baseEnd_1600284 : Nat := 121735537140699572620805

theorem tailTrace_1600284 : CollatzResearch.WordTrace tailWord_1600284 prefixEnd_1600284 121735537140699572620805 := by
  unfold tailWord_1600284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183576267225924796623953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38911435022967899728831937 29183576267225924796623953)
  ·
    refine ⟨21887682200419443597467965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29183576267225924796623953 21887682200419443597467965)
    ·
      refine ⟨8207880825157291349050487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21887682200419443597467965 8207880825157291349050487)
      ·
        refine ⟨12311821237735937023575731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8207880825157291349050487 12311821237735937023575731)
        ·
          refine ⟨18467731856603905535363597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12311821237735937023575731 18467731856603905535363597)
          ·
            refine ⟨6925399446226464575761349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18467731856603905535363597 6925399446226464575761349)
            ·
              refine ⟨1298512396167462107955253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6925399446226464575761349 1298512396167462107955253)
              ·
                refine ⟨121735537140699572620805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1298512396167462107955253 121735537140699572620805)
                ·
                  rfl

theorem cell21_1600284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_1600284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600284 prefixEnd_1600284 := by exact prefixLift 1600284
  have htrace : WordTrace (prefixWord ++ tailWord_1600284) baseStart_1600284 baseEnd_1600284 := by
    simpa [prefixWord, tailWord_1600284, baseEnd_1600284] using wordTrace_append hprefix tailTrace_1600284
  have hstable : (prefixWord ++ tailWord_1600284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600284).length < 2 ^ (prefixWord ++ tailWord_1600284).sum := by decide
  have hdescent : baseEnd_1600284 < baseStart_1600284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600312 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_1600312 : Nat := 118140960795 + 1600312 * 2 ^ 59
def prefixEnd_1600312 : Nat := 4983230072969 + 3 ^ 40 * 1600312 * 2
def baseEnd_1600312 : Nat := 365213001403576891395691

theorem tailTrace_1600312 : CollatzResearch.WordTrace tailWord_1600312 prefixEnd_1600312 365213001403576891395691 := by
  unfold tailWord_1600312
  simp only [CollatzResearch.WordTrace]
  refine ⟨29184086889175205187633595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38912115852233606916844793 29184086889175205187633595)
  ·
    refine ⟨43776130333762807781450393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29184086889175205187633595 43776130333762807781450393)
    ·
      refine ⟨32832097750322105836087795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43776130333762807781450393 32832097750322105836087795)
      ·
        refine ⟨49248146625483158754131693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32832097750322105836087795 49248146625483158754131693)
        ·
          refine ⟨18468054984556184532799385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49248146625483158754131693 18468054984556184532799385)
          ·
            refine ⟨13851041238417138399599539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18468054984556184532799385 13851041238417138399599539)
            ·
              refine ⟨20776561857625707599399309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13851041238417138399599539 20776561857625707599399309)
              ·
                refine ⟨7791210696609640349774741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20776561857625707599399309 7791210696609640349774741)
                ·
                  refine ⟨365213001403576891395691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7791210696609640349774741 365213001403576891395691)
                  ·
                    rfl

theorem cell21_1600312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_1600312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600312 prefixEnd_1600312 := by exact prefixLift 1600312
  have htrace : WordTrace (prefixWord ++ tailWord_1600312) baseStart_1600312 baseEnd_1600312 := by
    simpa [prefixWord, tailWord_1600312, baseEnd_1600312] using wordTrace_append hprefix tailTrace_1600312
  have hstable : (prefixWord ++ tailWord_1600312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600312).length < 2 ^ (prefixWord ++ tailWord_1600312).sum := by decide
  have hdescent : baseEnd_1600312 < baseStart_1600312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600321 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 4]
def baseStart_1600321 : Nat := 118140960795 + 1600321 * 2 ^ 59
def prefixEnd_1600321 : Nat := 4983230072969 + 3 ^ 40 * 1600321 * 2
def baseEnd_1600321 : Nat := 365215055326194875745673

theorem tailTrace_1600321 : CollatzResearch.WordTrace tailWord_1600321 prefixEnd_1600321 365215055326194875745673 := by
  unfold tailWord_1600321
  simp only [CollatzResearch.WordTrace]
  refine ⟨58368502035317804912344817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38912334690211869941563211 58368502035317804912344817)
  ·
    refine ⟨43776376526488353684258613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58368502035317804912344817 43776376526488353684258613)
    ·
      refine ⟨4104035299358283157899245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43776376526488353684258613 4104035299358283157899245)
      ·
        refine ⟨1539013237259356184212217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4104035299358283157899245 1539013237259356184212217)
        ·
          refine ⟨1154259927944517138159163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539013237259356184212217 1154259927944517138159163)
          ·
            refine ⟨1731389891916775707238745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154259927944517138159163 1731389891916775707238745)
            ·
              refine ⟨1298542418937581780429059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731389891916775707238745 1298542418937581780429059)
              ·
                refine ⟨1947813628406372670643589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298542418937581780429059 1947813628406372670643589)
                ·
                  refine ⟨365215055326194875745673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947813628406372670643589 365215055326194875745673)
                  ·
                    rfl

theorem cell21_1600321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_1600321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600321 prefixEnd_1600321 := by exact prefixLift 1600321
  have htrace : WordTrace (prefixWord ++ tailWord_1600321) baseStart_1600321 baseEnd_1600321 := by
    simpa [prefixWord, tailWord_1600321, baseEnd_1600321] using wordTrace_append hprefix tailTrace_1600321
  have hstable : (prefixWord ++ tailWord_1600321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600321).length < 2 ^ (prefixWord ++ tailWord_1600321).sum := by decide
  have hdescent : baseEnd_1600321 < baseStart_1600321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600329 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 4]
def baseStart_1600329 : Nat := 118140960795 + 1600329 * 2 ^ 59
def prefixEnd_1600329 : Nat := 4983230072969 + 3 ^ 40 * 1600329 * 2
def baseEnd_1600329 : Nat := 365216881035188639612323

theorem tailTrace_1600329 : CollatzResearch.WordTrace tailWord_1600329 prefixEnd_1600329 365216881035188639612323 := by
  unfold tailWord_1600329
  simp only [CollatzResearch.WordTrace]
  refine ⟨58368793819288822278636041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38912529212859214852424027 58368793819288822278636041)
  ·
    refine ⟨43776595364466616708977031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58368793819288822278636041 43776595364466616708977031)
    ·
      refine ⟨65664893046699925063465547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43776595364466616708977031 65664893046699925063465547)
      ·
        refine ⟨98497339570049887595198321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65664893046699925063465547 98497339570049887595198321)
        ·
          refine ⟨73873004677537415696398741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98497339570049887595198321 73873004677537415696398741)
          ·
            refine ⟨3462797094259566360768691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73873004677537415696398741 3462797094259566360768691)
            ·
              refine ⟨5194195641389349541153037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462797094259566360768691 5194195641389349541153037)
              ·
                refine ⟨1947823365521006077932389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5194195641389349541153037 1947823365521006077932389)
                ·
                  refine ⟨365216881035188639612323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947823365521006077932389 365216881035188639612323)
                  ·
                    rfl

theorem cell21_1600329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_1600329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600329 prefixEnd_1600329 := by exact prefixLift 1600329
  have htrace : WordTrace (prefixWord ++ tailWord_1600329) baseStart_1600329 baseEnd_1600329 := by
    simpa [prefixWord, tailWord_1600329, baseEnd_1600329] using wordTrace_append hprefix tailTrace_1600329
  have hstable : (prefixWord ++ tailWord_1600329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600329).length < 2 ^ (prefixWord ++ tailWord_1600329).sum := by decide
  have hdescent : baseEnd_1600329 < baseStart_1600329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600343 : List Nat := [1, 1, 3, 2, 4, 1, 2, 7]
def baseStart_1600343 : Nat := 118140960795 + 1600343 * 2 ^ 59
def prefixEnd_1600343 : Nat := 4983230072969 + 3 ^ 40 * 1600343 * 2
def baseEnd_1600343 : Nat := 121740025341975908792987

theorem tailTrace_1600343 : CollatzResearch.WordTrace tailWord_1600343 prefixEnd_1600343 121740025341975908792987 := by
  unfold tailWord_1600343
  simp only [CollatzResearch.WordTrace]
  refine ⟨58369304441238102669645683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38912869627492068446430455 58369304441238102669645683)
  ·
    refine ⟨87553956661857154004468525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58369304441238102669645683 87553956661857154004468525)
    ·
      refine ⟨32832733748196432751675697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87553956661857154004468525 32832733748196432751675697)
      ·
        refine ⟨24624550311147324563756773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32832733748196432751675697 24624550311147324563756773)
        ·
          refine ⟨4617103183340123355704395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24624550311147324563756773 4617103183340123355704395)
          ·
            refine ⟨6925654775010185033556593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617103183340123355704395 6925654775010185033556593)
            ·
              refine ⟨5194241081257638775167445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925654775010185033556593 5194241081257638775167445)
              ·
                refine ⟨121740025341975908792987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5194241081257638775167445 121740025341975908792987)
                ·
                  rfl

theorem cell21_1600343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_1600343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600343 prefixEnd_1600343 := by exact prefixLift 1600343
  have htrace : WordTrace (prefixWord ++ tailWord_1600343) baseStart_1600343 baseEnd_1600343 := by
    simpa [prefixWord, tailWord_1600343, baseEnd_1600343] using wordTrace_append hprefix tailTrace_1600343
  have hstable : (prefixWord ++ tailWord_1600343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600343).length < 2 ^ (prefixWord ++ tailWord_1600343).sum := by decide
  have hdescent : baseEnd_1600343 < baseStart_1600343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600366 : List Nat := [4, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_1600366 : Nat := 118140960795 + 1600366 * 2 ^ 59
def prefixEnd_1600366 : Nat := 4983230072969 + 3 ^ 40 * 1600366 * 2
def baseEnd_1600366 : Nat := 365225324939284797495581

theorem tailTrace_1600366 : CollatzResearch.WordTrace tailWord_1600366 prefixEnd_1600366 365225324939284797495581 := by
  unfold tailWord_1600366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296267915019347199716619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38913428880103185065155301 7296267915019347199716619)
  ·
    refine ⟨10944401872529020799574929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7296267915019347199716619 10944401872529020799574929)
    ·
      refine ⟨8208301404396765599681197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10944401872529020799574929 8208301404396765599681197)
      ·
        refine ⟨3078113026648787099880449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8208301404396765599681197 3078113026648787099880449)
        ·
          refine ⟨2308584769986590324910337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078113026648787099880449 2308584769986590324910337)
          ·
            refine ⟨1731438577489942743682753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308584769986590324910337 1731438577489942743682753)
            ·
              refine ⟨1298578933117457057762065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731438577489942743682753 1298578933117457057762065)
              ·
                refine ⟨973934199838092793321549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298578933117457057762065 973934199838092793321549)
                ·
                  refine ⟨365225324939284797495581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973934199838092793321549 365225324939284797495581)
                  ·
                    rfl

theorem cell21_1600366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_1600366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600366 prefixEnd_1600366 := by exact prefixLift 1600366
  have htrace : WordTrace (prefixWord ++ tailWord_1600366) baseStart_1600366 baseEnd_1600366 := by
    simpa [prefixWord, tailWord_1600366, baseEnd_1600366] using wordTrace_append hprefix tailTrace_1600366
  have hstable : (prefixWord ++ tailWord_1600366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600366).length < 2 ^ (prefixWord ++ tailWord_1600366).sum := by decide
  have hdescent : baseEnd_1600366 < baseStart_1600366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600388 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1600388 : Nat := 118140960795 + 1600388 * 2 ^ 59
def prefixEnd_1600388 : Nat := 4983230072969 + 3 ^ 40 * 1600388 * 2
def baseEnd_1600388 : Nat := 365230345639017648128869

theorem tailTrace_1600388 : CollatzResearch.WordTrace tailWord_1600388 prefixEnd_1600388 365230345639017648128869 := by
  unfold tailWord_1600388
  simp only [CollatzResearch.WordTrace]
  refine ⟨29185472863037537677516909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38913963817383383570022545 29185472863037537677516909)
  ·
    refine ⟨10944552323639076629068841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29185472863037537677516909 10944552323639076629068841)
    ·
      refine ⟨8208414242729307471801631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10944552323639076629068841 8208414242729307471801631)
      ·
        refine ⟨12312621364093961207702447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8208414242729307471801631 12312621364093961207702447)
        ·
          refine ⟨18468932046140941811553671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12312621364093961207702447 18468932046140941811553671)
          ·
            refine ⟨27703398069211412717330507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18468932046140941811553671 27703398069211412717330507)
            ·
              refine ⟨41555097103817119075995761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27703398069211412717330507 41555097103817119075995761)
              ·
                refine ⟨31166322827862839306996821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41555097103817119075995761 31166322827862839306996821)
                ·
                  refine ⟨365230345639017648128869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31166322827862839306996821 365230345639017648128869)
                  ·
                    rfl

theorem cell21_1600388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1600388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600388 prefixEnd_1600388 := by exact prefixLift 1600388
  have htrace : WordTrace (prefixWord ++ tailWord_1600388) baseStart_1600388 baseEnd_1600388 := by
    simpa [prefixWord, tailWord_1600388, baseEnd_1600388] using wordTrace_append hprefix tailTrace_1600388
  have hstable : (prefixWord ++ tailWord_1600388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600388).length < 2 ^ (prefixWord ++ tailWord_1600388).sum := by decide
  have hdescent : baseEnd_1600388 < baseStart_1600388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600495 : List Nat := [1, 1, 2, 1, 4, 4, 2, 6]
def baseStart_1600495 : Nat := 118140960795 + 1600495 * 2 ^ 59
def prefixEnd_1600495 : Nat := 4983230072969 + 3 ^ 40 * 1600495 * 2
def baseEnd_1600495 : Nat := 121751588165603079948439

theorem tailTrace_1600495 : CollatzResearch.WordTrace tailWord_1600495 prefixEnd_1600495 121751588165603079948439 := by
  unfold tailWord_1600495
  simp only [CollatzResearch.WordTrace]
  refine ⟨58374848336687432629178939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38916565557791621752785959 58374848336687432629178939)
  ·
    refine ⟨87562272505031148943768409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58374848336687432629178939 87562272505031148943768409)
    ·
      refine ⟨65671704378773361707826307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87562272505031148943768409 65671704378773361707826307)
      ·
        refine ⟨98507556568160042561739461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65671704378773361707826307 98507556568160042561739461)
        ·
          refine ⟨18470166856530007980326149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98507556568160042561739461 18470166856530007980326149)
          ·
            refine ⟨3463156285599376496311153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18470166856530007980326149 3463156285599376496311153)
            ·
              refine ⟨2597367214199532372233365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3463156285599376496311153 2597367214199532372233365)
              ·
                refine ⟨121751588165603079948439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2597367214199532372233365 121751588165603079948439)
                ·
                  rfl

theorem cell21_1600495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 6].length) (baseStart_1600495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600495 prefixEnd_1600495 := by exact prefixLift 1600495
  have htrace : WordTrace (prefixWord ++ tailWord_1600495) baseStart_1600495 baseEnd_1600495 := by
    simpa [prefixWord, tailWord_1600495, baseEnd_1600495] using wordTrace_append hprefix tailTrace_1600495
  have hstable : (prefixWord ++ tailWord_1600495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600495).length < 2 ^ (prefixWord ++ tailWord_1600495).sum := by decide
  have hdescent : baseEnd_1600495 < baseStart_1600495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600509 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1600509 : Nat := 118140960795 + 1600509 * 2 ^ 59
def prefixEnd_1600509 : Nat := 4983230072969 + 3 ^ 40 * 1600509 * 2
def baseEnd_1600509 : Nat := 365257959487548326611955

theorem tailTrace_1600509 : CollatzResearch.WordTrace tailWord_1600509 prefixEnd_1600509 365257959487548326611955 := by
  unfold tailWord_1600509
  simp only [CollatzResearch.WordTrace]
  refine ⟨58375358958636713020188581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38916905972424475346792387 58375358958636713020188581)
  ·
    refine ⟨10945379804744383691285359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58375358958636713020188581 10945379804744383691285359)
    ·
      refine ⟨16418069707116575536928039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10945379804744383691285359 16418069707116575536928039)
      ·
        refine ⟨24627104560674863305392059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16418069707116575536928039 24627104560674863305392059)
        ·
          refine ⟨36940656841012294958088089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24627104560674863305392059 36940656841012294958088089)
          ·
            refine ⟨27705492630759221218566067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36940656841012294958088089 27705492630759221218566067)
            ·
              refine ⟨41558238946138831827849101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27705492630759221218566067 41558238946138831827849101)
              ·
                refine ⟨15584339604802061935443413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41558238946138831827849101 15584339604802061935443413)
                ·
                  refine ⟨365257959487548326611955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15584339604802061935443413 365257959487548326611955)
                  ·
                    rfl

theorem cell21_1600509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1600509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600509 prefixEnd_1600509 := by exact prefixLift 1600509
  have htrace : WordTrace (prefixWord ++ tailWord_1600509) baseStart_1600509 baseEnd_1600509 := by
    simpa [prefixWord, tailWord_1600509, baseEnd_1600509] using wordTrace_append hprefix tailTrace_1600509
  have hstable : (prefixWord ++ tailWord_1600509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600509).length < 2 ^ (prefixWord ++ tailWord_1600509).sum := by decide
  have hdescent : baseEnd_1600509 < baseStart_1600509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600543 : List Nat := [1, 1, 2, 4, 1, 4, 1, 4, 3]
def baseStart_1600543 : Nat := 118140960795 + 1600543 * 2 ^ 59
def prefixEnd_1600543 : Nat := 4983230072969 + 3 ^ 40 * 1600543 * 2
def baseEnd_1600543 : Nat := 365265718750771823045219

theorem tailTrace_1600543 : CollatzResearch.WordTrace tailWord_1600543 prefixEnd_1600543 365265718750771823045219 := by
  unfold tailWord_1600543
  simp only [CollatzResearch.WordTrace]
  refine ⟨58376599040513536826926283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38917732693675691217950855 58376599040513536826926283)
  ·
    refine ⟨87564898560770305240389425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58376599040513536826926283 87564898560770305240389425)
    ·
      refine ⟨65673673920577728930292069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87564898560770305240389425 65673673920577728930292069)
      ·
        refine ⟨12313813860108324174429763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65673673920577728930292069 12313813860108324174429763)
        ·
          refine ⟨18470720790162486261644645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12313813860108324174429763 18470720790162486261644645)
          ·
            refine ⟨3463260148155466174058371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18470720790162486261644645 3463260148155466174058371)
            ·
              refine ⟨5194890222233199261087557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463260148155466174058371 5194890222233199261087557)
              ·
                refine ⟨974041916668724861453917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5194890222233199261087557 974041916668724861453917)
                ·
                  refine ⟨365265718750771823045219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974041916668724861453917 365265718750771823045219)
                  ·
                    rfl

theorem cell21_1600543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 3].length) (baseStart_1600543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600543 prefixEnd_1600543 := by exact prefixLift 1600543
  have htrace : WordTrace (prefixWord ++ tailWord_1600543) baseStart_1600543 baseEnd_1600543 := by
    simpa [prefixWord, tailWord_1600543, baseEnd_1600543] using wordTrace_append hprefix tailTrace_1600543
  have hstable : (prefixWord ++ tailWord_1600543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600543).length < 2 ^ (prefixWord ++ tailWord_1600543).sum := by decide
  have hdescent : baseEnd_1600543 < baseStart_1600543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600661 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 5]
def baseStart_1600661 : Nat := 118140960795 + 1600661 * 2 ^ 59
def prefixEnd_1600661 : Nat := 4983230072969 + 3 ^ 40 * 1600661 * 2
def baseEnd_1600661 : Nat := 365292647958429840078311

theorem tailTrace_1600661 : CollatzResearch.WordTrace tailWord_1600661 prefixEnd_1600661 365292647958429840078311 := by
  unfold tailWord_1600661
  simp only [CollatzResearch.WordTrace]
  refine ⟨58380902854086042979721837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38920601902724028653147891 58380902854086042979721837)
  ·
    refine ⟨21892838570282266117395689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58380902854086042979721837 21892838570282266117395689)
    ·
      refine ⟨16419628927711699588046767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21892838570282266117395689 16419628927711699588046767)
      ·
        refine ⟨24629443391567549382070151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16419628927711699588046767 24629443391567549382070151)
        ·
          refine ⟨36944165087351324073105227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24629443391567549382070151 36944165087351324073105227)
          ·
            refine ⟨55416247631026986109657841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36944165087351324073105227 55416247631026986109657841)
            ·
              refine ⟨41562185723270239582243381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55416247631026986109657841 41562185723270239582243381)
              ·
                refine ⟨3896454911556584960835317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41562185723270239582243381 3896454911556584960835317)
                ·
                  refine ⟨365292647958429840078311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896454911556584960835317 365292647958429840078311)
                  ·
                    rfl

theorem cell21_1600661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_1600661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600661 prefixEnd_1600661 := by exact prefixLift 1600661
  have htrace : WordTrace (prefixWord ++ tailWord_1600661) baseStart_1600661 baseEnd_1600661 := by
    simpa [prefixWord, tailWord_1600661, baseEnd_1600661] using wordTrace_append hprefix tailTrace_1600661
  have hstable : (prefixWord ++ tailWord_1600661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600661).length < 2 ^ (prefixWord ++ tailWord_1600661).sum := by decide
  have hdescent : baseEnd_1600661 < baseStart_1600661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600737 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 7]
def baseStart_1600737 : Nat := 118140960795 + 1600737 * 2 ^ 59
def prefixEnd_1600737 : Nat := 4983230072969 + 3 ^ 40 * 1600737 * 2
def baseEnd_1600737 : Nat := 365309992193870596811489

theorem tailTrace_1600737 : CollatzResearch.WordTrace tailWord_1600737 prefixEnd_1600737 365309992193870596811489 := by
  unfold tailWord_1600737
  simp only [CollatzResearch.WordTrace]
  refine ⟨58383674801810707959488465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38922449867873805306325643 58383674801810707959488465)
  ·
    refine ⟨43787756101358030969616349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58383674801810707959488465 43787756101358030969616349)
    ·
      refine ⟨16420408538009261613606131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43787756101358030969616349 16420408538009261613606131)
      ·
        refine ⟨24630612807013892420409197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16420408538009261613606131 24630612807013892420409197)
        ·
          refine ⟨9236479802630209657653449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24630612807013892420409197 9236479802630209657653449)
          ·
            refine ⟨6927359851972657243240087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9236479802630209657653449 6927359851972657243240087)
            ·
              refine ⟨10391039777958985864860131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927359851972657243240087 10391039777958985864860131)
              ·
                refine ⟨15586559666938478797290197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10391039777958985864860131 15586559666938478797290197)
                ·
                  refine ⟨365309992193870596811489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15586559666938478797290197 365309992193870596811489)
                  ·
                    rfl

theorem cell21_1600737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_1600737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600737 prefixEnd_1600737 := by exact prefixLift 1600737
  have htrace : WordTrace (prefixWord ++ tailWord_1600737) baseStart_1600737 baseEnd_1600737 := by
    simpa [prefixWord, tailWord_1600737, baseEnd_1600737] using wordTrace_append hprefix tailTrace_1600737
  have hstable : (prefixWord ++ tailWord_1600737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600737).length < 2 ^ (prefixWord ++ tailWord_1600737).sum := by decide
  have hdescent : baseEnd_1600737 < baseStart_1600737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600785 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 4]
def baseStart_1600785 : Nat := 118140960795 + 1600785 * 2 ^ 59
def prefixEnd_1600785 : Nat := 4983230072969 + 3 ^ 40 * 1600785 * 2
def baseEnd_1600785 : Nat := 365320946447833180011391

theorem tailTrace_1600785 : CollatzResearch.WordTrace tailWord_1600785 prefixEnd_1600785 365320946447833180011391 := by
  unfold tailWord_1600785
  simp only [CollatzResearch.WordTrace]
  refine ⟨58385425505636812157235809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38923617003757874771490539 58385425505636812157235809)
  ·
    refine ⟨43789069129227609117926857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58385425505636812157235809 43789069129227609117926857)
    ·
      refine ⟨32841801846920706838445143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43789069129227609117926857 32841801846920706838445143)
      ·
        refine ⟨49262702770381060257667715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32841801846920706838445143 49262702770381060257667715)
        ·
          refine ⟨73894054155571590386501573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49262702770381060257667715 73894054155571590386501573)
          ·
            refine ⟨13855135154169673197469045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73894054155571590386501573 13855135154169673197469045)
            ·
              refine ⟨1298918920703406862262723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13855135154169673197469045 1298918920703406862262723)
              ·
                refine ⟨1948378381055110293394085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298918920703406862262723 1948378381055110293394085)
                ·
                  refine ⟨365320946447833180011391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948378381055110293394085 365320946447833180011391)
                  ·
                    rfl

theorem cell21_1600785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_1600785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600785 prefixEnd_1600785 := by exact prefixLift 1600785
  have htrace : WordTrace (prefixWord ++ tailWord_1600785) baseStart_1600785 baseEnd_1600785 := by
    simpa [prefixWord, tailWord_1600785, baseEnd_1600785] using wordTrace_append hprefix tailTrace_1600785
  have hstable : (prefixWord ++ tailWord_1600785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600785).length < 2 ^ (prefixWord ++ tailWord_1600785).sum := by decide
  have hdescent : baseEnd_1600785 < baseStart_1600785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600799 : List Nat := [1, 1, 2, 4, 4, 1, 1, 7]
def baseStart_1600799 : Nat := 118140960795 + 1600799 * 2 ^ 59
def prefixEnd_1600799 : Nat := 4983230072969 + 3 ^ 40 * 1600799 * 2
def baseEnd_1600799 : Nat := 121774713812857422259343

theorem tailTrace_1600799 : CollatzResearch.WordTrace tailWord_1600799 prefixEnd_1600799 121774713812857422259343 := by
  unfold tailWord_1600799
  simp only [CollatzResearch.WordTrace]
  refine ⟨58385936127586092548245451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38923957418390728365496967 58385936127586092548245451)
  ·
    refine ⟨87578904191379138822368177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58385936127586092548245451 87578904191379138822368177)
    ·
      refine ⟨65684178143534354116776133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87578904191379138822368177 65684178143534354116776133)
      ·
        refine ⟨12315783401912691396895525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65684178143534354116776133 12315783401912691396895525)
        ·
          refine ⟨2309209387858629636917911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12315783401912691396895525 2309209387858629636917911)
          ·
            refine ⟨3463814081787944455376867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309209387858629636917911 3463814081787944455376867)
            ·
              refine ⟨5195721122681916683065301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463814081787944455376867 5195721122681916683065301)
              ·
                refine ⟨121774713812857422259343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5195721122681916683065301 121774713812857422259343)
                ·
                  rfl

theorem cell21_1600799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 7].length) (baseStart_1600799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600799 prefixEnd_1600799 := by exact prefixLift 1600799
  have htrace : WordTrace (prefixWord ++ tailWord_1600799) baseStart_1600799 baseEnd_1600799 := by
    simpa [prefixWord, tailWord_1600799, baseEnd_1600799] using wordTrace_append hprefix tailTrace_1600799
  have hstable : (prefixWord ++ tailWord_1600799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600799).length < 2 ^ (prefixWord ++ tailWord_1600799).sum := by decide
  have hdescent : baseEnd_1600799 < baseStart_1600799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600822 : List Nat := [5, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1600822 : Nat := 118140960795 + 1600822 * 2 ^ 59
def prefixEnd_1600822 : Nat := 4983230072969 + 3 ^ 40 * 1600822 * 2
def baseEnd_1600822 : Nat := 365329390351929337894649

theorem tailTrace_1600822 : CollatzResearch.WordTrace tailWord_1600822 prefixEnd_1600822 365329390351929337894649 := by
  unfold tailWord_1600822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649173437906422967270795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38924516671001844984221813 3649173437906422967270795)
  ·
    refine ⟨5473760156859634450906193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3649173437906422967270795 5473760156859634450906193)
    ·
      refine ⟨4105320117644725838179645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5473760156859634450906193 4105320117644725838179645)
      ·
        refine ⟨1539495044116772189317367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4105320117644725838179645 1539495044116772189317367)
        ·
          refine ⟨2309242566175158283976051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539495044116772189317367 2309242566175158283976051)
          ·
            refine ⟨3463863849262737425964077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309242566175158283976051 3463863849262737425964077)
            ·
              refine ⟨1298948943473526534736529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3463863849262737425964077 1298948943473526534736529)
              ·
                refine ⟨974211707605144901052397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298948943473526534736529 974211707605144901052397)
                ·
                  refine ⟨365329390351929337894649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974211707605144901052397 365329390351929337894649)
                  ·
                    rfl

theorem cell21_1600822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1600822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600822 prefixEnd_1600822 := by exact prefixLift 1600822
  have htrace : WordTrace (prefixWord ++ tailWord_1600822) baseStart_1600822 baseEnd_1600822 := by
    simpa [prefixWord, tailWord_1600822, baseEnd_1600822] using wordTrace_append hprefix tailTrace_1600822
  have hstable : (prefixWord ++ tailWord_1600822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600822).length < 2 ^ (prefixWord ++ tailWord_1600822).sum := by decide
  have hdescent : baseEnd_1600822 < baseStart_1600822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600858 : List Nat := [3, 1, 1, 2, 1, 2, 4, 7]
def baseStart_1600858 : Nat := 118140960795 + 1600858 * 2 ^ 59
def prefixEnd_1600858 : Nat := 4983230072969 + 3 ^ 40 * 1600858 * 2
def baseEnd_1600858 : Nat := 121779202014133758431525

theorem tailTrace_1600858 : CollatzResearch.WordTrace tailWord_1600858 prefixEnd_1600858 121779202014133758431525 := by
  unfold tailWord_1600858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14597022008593086406160807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38925392022914897083095485 14597022008593086406160807)
  ·
    refine ⟨21895533012889629609241211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14597022008593086406160807 21895533012889629609241211)
    ·
      refine ⟨32843299519334444413861817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21895533012889629609241211 32843299519334444413861817)
      ·
        refine ⟨24632474639500833310396363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32843299519334444413861817 24632474639500833310396363)
        ·
          refine ⟨36948711959251249965594545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24632474639500833310396363 36948711959251249965594545)
          ·
            refine ⟨27711533969438437474195909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36948711959251249965594545 27711533969438437474195909)
            ·
              refine ⟨5195912619269707026411733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27711533969438437474195909 5195912619269707026411733)
              ·
                refine ⟨121779202014133758431525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5195912619269707026411733 121779202014133758431525)
                ·
                  rfl

theorem cell21_1600858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_1600858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1600858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1600858 prefixEnd_1600858 := by exact prefixLift 1600858
  have htrace : WordTrace (prefixWord ++ tailWord_1600858) baseStart_1600858 baseEnd_1600858 := by
    simpa [prefixWord, tailWord_1600858, baseEnd_1600858] using wordTrace_append hprefix tailTrace_1600858
  have hstable : (prefixWord ++ tailWord_1600858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600858).length < 2 ^ (prefixWord ++ tailWord_1600858).sum := by decide
  have hdescent : baseEnd_1600858 < baseStart_1600858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601044 : List Nat := [2, 4, 3, 1, 3, 8]
def baseStart_1601044 : Nat := 118140960795 + 1601044 * 2 ^ 59
def prefixEnd_1601044 : Nat := 4983230072969 + 3 ^ 40 * 1601044 * 2
def baseEnd_1601044 : Nat := 13532594584315047599785

theorem tailTrace_1601044 : CollatzResearch.WordTrace tailWord_1601044 prefixEnd_1601044 13532594584315047599785 := by
  unfold tailWord_1601044
  simp only [CollatzResearch.WordTrace]
  refine ⟨29197436005849249695457093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38929914674465666260609457 29197436005849249695457093)
  ·
    refine ⟨5474519251096734317898205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29197436005849249695457093 5474519251096734317898205)
    ·
      refine ⟨2052944719161275369211827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5474519251096734317898205 2052944719161275369211827)
      ·
        refine ⟨3079417078741913053817741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052944719161275369211827 3079417078741913053817741)
        ·
          refine ⟨1154781404528217395181653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3079417078741913053817741 1154781404528217395181653)
          ·
            refine ⟨13532594584315047599785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1154781404528217395181653 13532594584315047599785)
            ·
              rfl

theorem cell21_1601044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 8].length) (baseStart_1601044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601044 prefixEnd_1601044 := by exact prefixLift 1601044
  have htrace : WordTrace (prefixWord ++ tailWord_1601044) baseStart_1601044 baseEnd_1601044 := by
    simpa [prefixWord, tailWord_1601044, baseEnd_1601044] using wordTrace_append hprefix tailTrace_1601044
  have hstable : (prefixWord ++ tailWord_1601044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601044).length < 2 ^ (prefixWord ++ tailWord_1601044).sum := by decide
  have hdescent : baseEnd_1601044 < baseStart_1601044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601055 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 6]
def baseStart_1601055 : Nat := 118140960795 + 1601055 * 2 ^ 59
def prefixEnd_1601055 : Nat := 4983230072969 + 3 ^ 40 * 1601055 * 2
def baseEnd_1601055 : Nat := 365382564126372710510839

theorem tailTrace_1601055 : CollatzResearch.WordTrace tailWord_1601055 prefixEnd_1601055 365382564126372710510839 := by
  unfold tailWord_1601055
  simp only [CollatzResearch.WordTrace]
  refine ⟨58395273214658648269564619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38930182143105765513043079 58395273214658648269564619)
  ·
    refine ⟨87592909821987972404346929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58395273214658648269564619 87592909821987972404346929)
    ·
      refine ⟨65694682366490979303260197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87592909821987972404346929 65694682366490979303260197)
      ·
        refine ⟨12317752943717058619361287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65694682366490979303260197 12317752943717058619361287)
        ·
          refine ⟨18476629415575587929041931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12317752943717058619361287 18476629415575587929041931)
          ·
            refine ⟨27714944123363381893562897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18476629415575587929041931 27714944123363381893562897)
            ·
              refine ⟨20786208092522536420172173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27714944123363381893562897 20786208092522536420172173)
              ·
                refine ⟨7794828034695951157564565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20786208092522536420172173 7794828034695951157564565)
                ·
                  refine ⟨365382564126372710510839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7794828034695951157564565 365382564126372710510839)
                  ·
                    rfl

theorem cell21_1601055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_1601055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601055 prefixEnd_1601055 := by exact prefixLift 1601055
  have htrace : WordTrace (prefixWord ++ tailWord_1601055) baseStart_1601055 baseEnd_1601055 := by
    simpa [prefixWord, tailWord_1601055, baseEnd_1601055] using wordTrace_append hprefix tailTrace_1601055
  have hstable : (prefixWord ++ tailWord_1601055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601055).length < 2 ^ (prefixWord ++ tailWord_1601055).sum := by decide
  have hdescent : baseEnd_1601055 < baseStart_1601055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601162 : List Nat := [3, 1, 2, 3, 2, 1, 9]
def baseStart_1601162 : Nat := 118140960795 + 1601162 * 2 ^ 59
def prefixEnd_1601162 : Nat := 4983230072969 + 3 ^ 40 * 1601162 * 2
def baseEnd_1601162 : Nat := 40600775887129366914143

theorem tailTrace_1601162 : CollatzResearch.WordTrace tailWord_1601162 prefixEnd_1601162 40600775887129366914143 := by
  unfold tailWord_1601162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14599793956317751385927435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38932783883514003695806493 14599793956317751385927435)
  ·
    refine ⟨21899690934476627078891153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14599793956317751385927435 21899690934476627078891153)
    ·
      refine ⟨16424768200857470309168365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21899690934476627078891153 16424768200857470309168365)
      ·
        refine ⟨6159288075321551365938137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16424768200857470309168365 6159288075321551365938137)
        ·
          refine ⟨4619466056491163524453603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6159288075321551365938137 4619466056491163524453603)
          ·
            refine ⟨6929199084736745286680405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4619466056491163524453603 6929199084736745286680405)
            ·
              refine ⟨40600775887129366914143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6929199084736745286680405 40600775887129366914143)
              ·
                rfl

theorem cell21_1601162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 9].length) (baseStart_1601162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601162 prefixEnd_1601162 := by exact prefixLift 1601162
  have htrace : WordTrace (prefixWord ++ tailWord_1601162) baseStart_1601162 baseEnd_1601162 := by
    simpa [prefixWord, tailWord_1601162, baseEnd_1601162] using wordTrace_append hprefix tailTrace_1601162
  have hstable : (prefixWord ++ tailWord_1601162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601162).length < 2 ^ (prefixWord ++ tailWord_1601162).sum := by decide
  have hdescent : baseEnd_1601162 < baseStart_1601162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601182 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1601182 : Nat := 118140960795 + 1601182 * 2 ^ 59
def prefixEnd_1601182 : Nat := 4983230072969 + 3 ^ 40 * 1601182 * 2
def baseEnd_1601182 : Nat := 365411547256648711893913

theorem tailTrace_1601182 : CollatzResearch.WordTrace tailWord_1601182 prefixEnd_1601182 365411547256648711893913 := by
  unfold tailWord_1601182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299988160649818619929725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38933270190132365972958533 7299988160649818619929725)
  ·
    refine ⟨2737495560243681982473647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7299988160649818619929725 2737495560243681982473647)
    ·
      refine ⟨4106243340365522973710471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2737495560243681982473647 4106243340365522973710471)
      ·
        refine ⟨6159365010548284460565707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106243340365522973710471 6159365010548284460565707)
        ·
          refine ⟨9239047515822426690848561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6159365010548284460565707 9239047515822426690848561)
          ·
            refine ⟨6929285636866820018136421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9239047515822426690848561 6929285636866820018136421)
            ·
              refine ⟨1299241056912528753400579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6929285636866820018136421 1299241056912528753400579)
              ·
                refine ⟨1948861585368793130100869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299241056912528753400579 1948861585368793130100869)
                ·
                  refine ⟨365411547256648711893913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948861585368793130100869 365411547256648711893913)
                  ·
                    rfl

theorem cell21_1601182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1601182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601182 prefixEnd_1601182 := by exact prefixLift 1601182
  have htrace : WordTrace (prefixWord ++ tailWord_1601182) baseStart_1601182 baseEnd_1601182 := by
    simpa [prefixWord, tailWord_1601182, baseEnd_1601182] using wordTrace_append hprefix tailTrace_1601182
  have hstable : (prefixWord ++ tailWord_1601182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601182).length < 2 ^ (prefixWord ++ tailWord_1601182).sum := by decide
  have hdescent : baseEnd_1601182 < baseStart_1601182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601224 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_1601224 : Nat := 118140960795 + 1601224 * 2 ^ 59
def prefixEnd_1601224 : Nat := 4983230072969 + 3 ^ 40 * 1601224 * 2
def baseEnd_1601224 : Nat := 365421132228865972193827

theorem tailTrace_1601224 : CollatzResearch.WordTrace tailWord_1601224 prefixEnd_1601224 365421132228865972193827 := by
  unfold tailWord_1601224
  simp only [CollatzResearch.WordTrace]
  refine ⟨29200718575523195066233363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38934291434030926754977817 29200718575523195066233363)
  ·
    refine ⟨43801077863284792599350045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29200718575523195066233363 43801077863284792599350045)
    ·
      refine ⟨16425404198731797224756267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43801077863284792599350045 16425404198731797224756267)
      ·
        refine ⟨24638106298097695837134401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16425404198731797224756267 24638106298097695837134401)
        ·
          refine ⟨18478579723573271877850801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24638106298097695837134401 18478579723573271877850801)
          ·
            refine ⟨13858934792679953908388101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18478579723573271877850801 13858934792679953908388101)
            ·
              refine ⟨2598550273627491357822769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13858934792679953908388101 2598550273627491357822769)
              ·
                refine ⟨1948912705220618518367077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2598550273627491357822769 1948912705220618518367077)
                ·
                  refine ⟨365421132228865972193827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948912705220618518367077 365421132228865972193827)
                  ·
                    rfl

theorem cell21_1601224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_1601224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601224 prefixEnd_1601224 := by exact prefixLift 1601224
  have htrace : WordTrace (prefixWord ++ tailWord_1601224) baseStart_1601224 baseEnd_1601224 := by
    simpa [prefixWord, tailWord_1601224, baseEnd_1601224] using wordTrace_append hprefix tailTrace_1601224
  have hstable : (prefixWord ++ tailWord_1601224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601224).length < 2 ^ (prefixWord ++ tailWord_1601224).sum := by decide
  have hdescent : baseEnd_1601224 < baseStart_1601224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601297 : List Nat := [1, 2, 2, 1, 1, 3, 1, 10]
def baseStart_1601297 : Nat := 118140960795 + 1601297 * 2 ^ 59
def prefixEnd_1601297 : Nat := 4983230072969 + 3 ^ 40 * 1601297 * 2
def baseEnd_1601297 : Nat := 121812597274478022492337

theorem tailTrace_1601297 : CollatzResearch.WordTrace tailWord_1601297 prefixEnd_1601297 121812597274478022492337 := by
  unfold tailWord_1601297
  simp only [CollatzResearch.WordTrace]
  refine ⟨58404099679781923599874145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38936066453187949066582763 58404099679781923599874145)
  ·
    refine ⟨43803074759836442699905609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58404099679781923599874145 43803074759836442699905609)
    ·
      refine ⟨32852306069877332024929207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43803074759836442699905609 32852306069877332024929207)
      ·
        refine ⟨49278459104815998037393811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32852306069877332024929207 49278459104815998037393811)
        ·
          refine ⟨73917688657223997056090717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49278459104815998037393811 73917688657223997056090717)
          ·
            refine ⟨27719133246458998896034019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73917688657223997056090717 27719133246458998896034019)
            ·
              refine ⟨41578699869688498344051029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27719133246458998896034019 41578699869688498344051029)
              ·
                refine ⟨121812597274478022492337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41578699869688498344051029 121812597274478022492337)
                ·
                  rfl

theorem cell21_1601297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 10].length) (baseStart_1601297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601297 prefixEnd_1601297 := by exact prefixLift 1601297
  have htrace : WordTrace (prefixWord ++ tailWord_1601297) baseStart_1601297 baseEnd_1601297 := by
    simpa [prefixWord, tailWord_1601297, baseEnd_1601297] using wordTrace_append hprefix tailTrace_1601297
  have hstable : (prefixWord ++ tailWord_1601297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601297).length < 2 ^ (prefixWord ++ tailWord_1601297).sum := by decide
  have hdescent : baseEnd_1601297 < baseStart_1601297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601314 : List Nat := [3, 3, 1, 1, 2, 1, 3, 7]
def baseStart_1601314 : Nat := 118140960795 + 1601314 * 2 ^ 59
def prefixEnd_1601314 : Nat := 4983230072969 + 3 ^ 40 * 1601314 * 2
def baseEnd_1601314 : Nat := 121813890485015271897881

theorem tailTrace_1601314 : CollatzResearch.WordTrace tailWord_1601314 prefixEnd_1601314 121813890485015271897881 := by
  unfold tailWord_1601314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601179930180083875810749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38936479813813557002161997 14601179930180083875810749)
  ·
    refine ⟨5475442473817531453429031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14601179930180083875810749 5475442473817531453429031)
    ·
      refine ⟨8213163710726297180143547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5475442473817531453429031 8213163710726297180143547)
      ·
        refine ⟨12319745566089445770215321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8213163710726297180143547 12319745566089445770215321)
        ·
          refine ⟨9239809174567084327661491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12319745566089445770215321 9239809174567084327661491)
          ·
            refine ⟨13859713761850626491492237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9239809174567084327661491 13859713761850626491492237)
            ·
              refine ⟨5197392660693984934309589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13859713761850626491492237 5197392660693984934309589)
              ·
                refine ⟨121813890485015271897881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5197392660693984934309589 121813890485015271897881)
                ·
                  rfl

theorem cell21_1601314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_1601314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601314 prefixEnd_1601314 := by exact prefixLift 1601314
  have htrace : WordTrace (prefixWord ++ tailWord_1601314) baseStart_1601314 baseEnd_1601314 := by
    simpa [prefixWord, tailWord_1601314, baseEnd_1601314] using wordTrace_append hprefix tailTrace_1601314
  have hstable : (prefixWord ++ tailWord_1601314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601314).length < 2 ^ (prefixWord ++ tailWord_1601314).sum := by decide
  have hdescent : baseEnd_1601314 < baseStart_1601314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601331 : List Nat := [1, 1, 1, 2, 8, 1, 7]
def baseStart_1601331 : Nat := 118140960795 + 1601331 * 2 ^ 59
def prefixEnd_1601331 : Nat := 4983230072969 + 3 ^ 40 * 1601331 * 2
def baseEnd_1601331 : Nat := 40605061231850840434475

theorem tailTrace_1601331 : CollatzResearch.WordTrace tailWord_1601331 prefixEnd_1601331 40605061231850840434475 := by
  unfold tailWord_1601331
  simp only [CollatzResearch.WordTrace]
  refine ⟨58405339761658747406611847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38936893174439164937741231 58405339761658747406611847)
  ·
    refine ⟨87608009642488121109917771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58405339761658747406611847 87608009642488121109917771)
    ·
      refine ⟨131412014463732181664876657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87608009642488121109917771 131412014463732181664876657)
      ·
        refine ⟨98559010847799136248657493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131412014463732181664876657 98559010847799136248657493)
        ·
          refine ⟨1154988408372646127913955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 98559010847799136248657493 1154988408372646127913955)
          ·
            refine ⟨1732482612558969191870933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154988408372646127913955 1732482612558969191870933)
            ·
              refine ⟨40605061231850840434475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1732482612558969191870933 40605061231850840434475)
              ·
                rfl

theorem cell21_1601331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 7].length) (baseStart_1601331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601331 prefixEnd_1601331 := by exact prefixLift 1601331
  have htrace : WordTrace (prefixWord ++ tailWord_1601331) baseStart_1601331 baseEnd_1601331 := by
    simpa [prefixWord, tailWord_1601331, baseEnd_1601331] using wordTrace_append hprefix tailTrace_1601331
  have hstable : (prefixWord ++ tailWord_1601331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601331).length < 2 ^ (prefixWord ++ tailWord_1601331).sum := by decide
  have hdescent : baseEnd_1601331 < baseStart_1601331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601390 : List Nat := [4, 1, 2, 3, 1, 10]
def baseStart_1601390 : Nat := 118140960795 + 1601390 * 2 ^ 59
def prefixEnd_1601390 : Nat := 4983230072969 + 3 ^ 40 * 1601390 * 2
def baseEnd_1601390 : Nat := 13535519099647650830623

theorem tailTrace_1601390 : CollatzResearch.WordTrace tailWord_1601390 prefixEnd_1601390 13535519099647650830623 := by
  unfold tailWord_1601390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300936458555625060376203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38938327778963333655339749 7300936458555625060376203)
  ·
    refine ⟨10951404687833437590564305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300936458555625060376203 10951404687833437590564305)
    ·
      refine ⟨8213553515875078192923229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10951404687833437590564305 8213553515875078192923229)
      ·
        refine ⟨3080082568453154322346211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8213553515875078192923229 3080082568453154322346211)
        ·
          refine ⟨4620123852679731483519317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080082568453154322346211 4620123852679731483519317)
          ·
            refine ⟨13535519099647650830623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4620123852679731483519317 13535519099647650830623)
            ·
              rfl

theorem cell21_1601390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 10].length) (baseStart_1601390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601390 prefixEnd_1601390 := by exact prefixLift 1601390
  have htrace : WordTrace (prefixWord ++ tailWord_1601390) baseStart_1601390 baseEnd_1601390 := by
    simpa [prefixWord, tailWord_1601390, baseEnd_1601390] using wordTrace_append hprefix tailTrace_1601390
  have hstable : (prefixWord ++ tailWord_1601390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601390).length < 2 ^ (prefixWord ++ tailWord_1601390).sum := by decide
  have hdescent : baseEnd_1601390 < baseStart_1601390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601469 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1601469 : Nat := 118140960795 + 1601469 * 2 ^ 59
def prefixEnd_1601469 : Nat := 4983230072969 + 3 ^ 40 * 1601469 * 2
def baseEnd_1601469 : Nat := 365477044566799990609993

theorem tailTrace_1601469 : CollatzResearch.WordTrace tailWord_1601469 prefixEnd_1601469 365477044566799990609993 := by
  unfold tailWord_1601469
  simp only [CollatzResearch.WordTrace]
  refine ⟨58410373035158796975135461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38940248690105864650090307 58410373035158796975135461)
  ·
    refine ⟨10951944944092274432837899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58410373035158796975135461 10951944944092274432837899)
    ·
      refine ⟨16427917416138411649256849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10951944944092274432837899 16427917416138411649256849)
      ·
        refine ⟨12320938062103808736942637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16427917416138411649256849 12320938062103808736942637)
        ·
          refine ⟨4620351773288928276353489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12320938062103808736942637 4620351773288928276353489)
          ·
            refine ⟨3465263829966696207265117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4620351773288928276353489 3465263829966696207265117)
            ·
              refine ⟨1299473936237511077724419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3465263829966696207265117 1299473936237511077724419)
              ·
                refine ⟨1949210904356266616586629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299473936237511077724419 1949210904356266616586629)
                ·
                  refine ⟨365477044566799990609993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949210904356266616586629 365477044566799990609993)
                  ·
                    rfl

theorem cell21_1601469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1601469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601469 prefixEnd_1601469 := by exact prefixLift 1601469
  have htrace : WordTrace (prefixWord ++ tailWord_1601469) baseStart_1601469 baseEnd_1601469 := by
    simpa [prefixWord, tailWord_1601469, baseEnd_1601469] using wordTrace_append hprefix tailTrace_1601469
  have hstable : (prefixWord ++ tailWord_1601469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601469).length < 2 ^ (prefixWord ++ tailWord_1601469).sum := by decide
  have hdescent : baseEnd_1601469 < baseStart_1601469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601528 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_1601528 : Nat := 118140960795 + 1601528 * 2 ^ 59
def prefixEnd_1601528 : Nat := 4983230072969 + 3 ^ 40 * 1601528 * 2
def baseEnd_1601528 : Nat := 365490509170628999126539

theorem tailTrace_1601528 : CollatzResearch.WordTrace tailWord_1601528 prefixEnd_1601528 365490509170628999126539 := by
  unfold tailWord_1601528
  simp only [CollatzResearch.WordTrace]
  refine ⟨29206262470972525025766619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38941683294630033367688825 29206262470972525025766619)
  ·
    refine ⟨43809393706458787538649929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29206262470972525025766619 43809393706458787538649929)
    ·
      refine ⟨32857045279844090653987447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43809393706458787538649929 32857045279844090653987447)
      ·
        refine ⟨49285567919766135980981171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32857045279844090653987447 49285567919766135980981171)
        ·
          refine ⟨73928351879649203971471757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49285567919766135980981171 73928351879649203971471757)
          ·
            refine ⟨27723131954868451489301909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73928351879649203971471757 27723131954868451489301909)
            ·
              refine ⟨1299521810384458663561027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27723131954868451489301909 1299521810384458663561027)
              ·
                refine ⟨1949282715576687995341541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299521810384458663561027 1949282715576687995341541)
                ·
                  refine ⟨365490509170628999126539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949282715576687995341541 365490509170628999126539)
                  ·
                    rfl

theorem cell21_1601528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_1601528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601528 prefixEnd_1601528 := by exact prefixLift 1601528
  have htrace : WordTrace (prefixWord ++ tailWord_1601528) baseStart_1601528 baseEnd_1601528 := by
    simpa [prefixWord, tailWord_1601528, baseEnd_1601528] using wordTrace_append hprefix tailTrace_1601528
  have hstable : (prefixWord ++ tailWord_1601528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601528).length < 2 ^ (prefixWord ++ tailWord_1601528).sum := by decide
  have hdescent : baseEnd_1601528 < baseStart_1601528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601576 : List Nat := [2, 1, 5, 3, 1, 2, 1, 6]
def baseStart_1601576 : Nat := 118140960795 + 1601576 * 2 ^ 59
def prefixEnd_1601576 : Nat := 4983230072969 + 3 ^ 40 * 1601576 * 2
def baseEnd_1601576 : Nat := 121833821141530527442147

theorem tailTrace_1601576 : CollatzResearch.WordTrace tailWord_1601576 prefixEnd_1601576 121833821141530527442147 := by
  unfold tailWord_1601576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29207137822885577124640291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38942850430514102832853721 29207137822885577124640291)
  ·
    refine ⟨43810706734328365686960437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29207137822885577124640291 43810706734328365686960437)
    ·
      refine ⟨4107253756343284283152541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43810706734328365686960437 4107253756343284283152541)
      ·
        refine ⟨1540220158628731606182203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4107253756343284283152541 1540220158628731606182203)
        ·
          refine ⟨2310330237943097409273305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540220158628731606182203 2310330237943097409273305)
          ·
            refine ⟨1732747678457323056954979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2310330237943097409273305 1732747678457323056954979)
            ·
              refine ⟨2599121517685984585432469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732747678457323056954979 2599121517685984585432469)
              ·
                refine ⟨121833821141530527442147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2599121517685984585432469 121833821141530527442147)
                ·
                  rfl

theorem cell21_1601576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_1601576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601576 prefixEnd_1601576 := by exact prefixLift 1601576
  have htrace : WordTrace (prefixWord ++ tailWord_1601576) baseStart_1601576 baseEnd_1601576 := by
    simpa [prefixWord, tailWord_1601576, baseEnd_1601576] using wordTrace_append hprefix tailTrace_1601576
  have hstable : (prefixWord ++ tailWord_1601576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601576).length < 2 ^ (prefixWord ++ tailWord_1601576).sum := by decide
  have hdescent : baseEnd_1601576 < baseStart_1601576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601587 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 4]
def baseStart_1601587 : Nat := 118140960795 + 1601587 * 2 ^ 59
def prefixEnd_1601587 : Nat := 4983230072969 + 3 ^ 40 * 1601587 * 2
def baseEnd_1601587 : Nat := 365503973774458007643085

theorem tailTrace_1601587 : CollatzResearch.WordTrace tailWord_1601587 prefixEnd_1601587 365503973774458007643085 := by
  unfold tailWord_1601587
  simp only [CollatzResearch.WordTrace]
  refine ⟨58414676848731303127931015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38943117899154202085287343 58414676848731303127931015)
  ·
    refine ⟨87622015273096954691896523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58414676848731303127931015 87622015273096954691896523)
    ·
      refine ⟨131433022909645432037844785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87622015273096954691896523 131433022909645432037844785)
      ·
        refine ⟨98574767182234074028383589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131433022909645432037844785 98574767182234074028383589)
        ·
          refine ⟨18482768846668888880321923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98574767182234074028383589 18482768846668888880321923)
          ·
            refine ⟨27724153270003333320482885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18482768846668888880321923 27724153270003333320482885)
            ·
              refine ⟨5198278738125624997590541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27724153270003333320482885 5198278738125624997590541)
              ·
                refine ⟨1949354526797109374096453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5198278738125624997590541 1949354526797109374096453)
                ·
                  refine ⟨365503973774458007643085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949354526797109374096453 365503973774458007643085)
                  ·
                    rfl

theorem cell21_1601587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_1601587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601587 prefixEnd_1601587 := by exact prefixLift 1601587
  have htrace : WordTrace (prefixWord ++ tailWord_1601587) baseStart_1601587 baseEnd_1601587 := by
    simpa [prefixWord, tailWord_1601587, baseEnd_1601587] using wordTrace_append hprefix tailTrace_1601587
  have hstable : (prefixWord ++ tailWord_1601587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601587).length < 2 ^ (prefixWord ++ tailWord_1601587).sum := by decide
  have hdescent : baseEnd_1601587 < baseStart_1601587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601618 : List Nat := [3, 2, 2, 1, 4, 1, 8]
def baseStart_1601618 : Nat := 118140960795 + 1601618 * 2 ^ 59
def prefixEnd_1601618 : Nat := 4983230072969 + 3 ^ 40 * 1601618 * 2
def baseEnd_1601618 : Nat := 40612338710756538069595

theorem tailTrace_1601618 : CollatzResearch.WordTrace tailWord_1601618 prefixEnd_1601618 40612338710756538069595 := by
  unfold tailWord_1601618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603951877904748855577377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38943871674412663614873005 14603951877904748855577377)
  ·
    refine ⟨10952963908428561641683033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14603951877904748855577377 10952963908428561641683033)
    ·
      refine ⟨8214722931321421231262275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10952963908428561641683033 8214722931321421231262275)
      ·
        refine ⟨12322084396982131846893413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8214722931321421231262275 12322084396982131846893413)
        ·
          refine ⟨2310390824434149721292515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12322084396982131846893413 2310390824434149721292515)
          ·
            refine ⟨3465586236651224581938773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310390824434149721292515 3465586236651224581938773)
            ·
              refine ⟨40612338710756538069595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3465586236651224581938773 40612338710756538069595)
              ·
                rfl

theorem cell21_1601618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 8].length) (baseStart_1601618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601618 prefixEnd_1601618 := by exact prefixLift 1601618
  have htrace : WordTrace (prefixWord ++ tailWord_1601618) baseStart_1601618 baseEnd_1601618 := by
    simpa [prefixWord, tailWord_1601618, baseEnd_1601618] using wordTrace_append hprefix tailTrace_1601618
  have hstable : (prefixWord ++ tailWord_1601618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601618).length < 2 ^ (prefixWord ++ tailWord_1601618).sum := by decide
  have hdescent : baseEnd_1601618 < baseStart_1601618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601632 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_1601632 : Nat := 118140960795 + 1601632 * 2 ^ 59
def prefixEnd_1601632 : Nat := 4983230072969 + 3 ^ 40 * 1601632 * 2
def baseEnd_1601632 : Nat := 365514243387547929392993

theorem tailTrace_1601632 : CollatzResearch.WordTrace tailWord_1601632 prefixEnd_1601632 365514243387547929392993 := by
  unfold tailWord_1601632
  simp only [CollatzResearch.WordTrace]
  refine ⟨29208159066784137906659575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38944212089045517208879433 29208159066784137906659575)
  ·
    refine ⟨43812238600176206859989363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29208159066784137906659575 43812238600176206859989363)
    ·
      refine ⟨65718357900264310289984045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43812238600176206859989363 65718357900264310289984045)
      ·
        refine ⟨24644384212599116358744017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65718357900264310289984045 24644384212599116358744017)
        ·
          refine ⟨18483288159449337269058013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24644384212599116358744017 18483288159449337269058013)
          ·
            refine ⟨6931233059793501475896755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18483288159449337269058013 6931233059793501475896755)
            ·
              refine ⟨10396849589690252213845133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6931233059793501475896755 10396849589690252213845133)
              ·
                refine ⟨3898818596133844580191925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10396849589690252213845133 3898818596133844580191925)
                ·
                  refine ⟨365514243387547929392993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3898818596133844580191925 365514243387547929392993)
                  ·
                    rfl

theorem cell21_1601632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_1601632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601632 prefixEnd_1601632 := by exact prefixLift 1601632
  have htrace : WordTrace (prefixWord ++ tailWord_1601632) baseStart_1601632 baseEnd_1601632 := by
    simpa [prefixWord, tailWord_1601632, baseEnd_1601632] using wordTrace_append hprefix tailTrace_1601632
  have hstable : (prefixWord ++ tailWord_1601632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601632).length < 2 ^ (prefixWord ++ tailWord_1601632).sum := by decide
  have hdescent : baseEnd_1601632 < baseStart_1601632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601686 : List Nat := [5, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1601686 : Nat := 118140960795 + 1601686 * 2 ^ 59
def prefixEnd_1601686 : Nat := 4983230072969 + 3 ^ 40 * 1601686 * 2
def baseEnd_1601686 : Nat := 121842188974418611830961

theorem tailTrace_1601686 : CollatzResearch.WordTrace tailWord_1601686 prefixEnd_1601686 121842188974418611830961 := by
  unfold tailWord_1601686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651142979710790189736557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38945525116915095357189941 3651142979710790189736557)
  ·
    refine ⟨1369178617391546321151209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3651142979710790189736557 1369178617391546321151209)
    ·
      refine ⟨1026883963043659740863407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1369178617391546321151209 1026883963043659740863407)
      ·
        refine ⟨1540325944565489611295111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026883963043659740863407 1540325944565489611295111)
        ·
          refine ⟨2310488916848234416942667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540325944565489611295111 2310488916848234416942667)
          ·
            refine ⟨3465733375272351625414001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310488916848234416942667 3465733375272351625414001)
            ·
              refine ⟨2599300031454263719060501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3465733375272351625414001 2599300031454263719060501)
              ·
                refine ⟨121842188974418611830961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2599300031454263719060501 121842188974418611830961)
                ·
                  rfl

theorem cell21_1601686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1601686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601686 prefixEnd_1601686 := by exact prefixLift 1601686
  have htrace : WordTrace (prefixWord ++ tailWord_1601686) baseStart_1601686 baseEnd_1601686 := by
    simpa [prefixWord, tailWord_1601686, baseEnd_1601686] using wordTrace_append hprefix tailTrace_1601686
  have hstable : (prefixWord ++ tailWord_1601686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601686).length < 2 ^ (prefixWord ++ tailWord_1601686).sum := by decide
  have hdescent : baseEnd_1601686 < baseStart_1601686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601691 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 9]
def baseStart_1601691 : Nat := 118140960795 + 1601691 * 2 ^ 59
def prefixEnd_1601691 : Nat := 4983230072969 + 3 ^ 40 * 1601691 * 2
def baseEnd_1601691 : Nat := 365527707991376937909539

theorem tailTrace_1601691 : CollatzResearch.WordTrace tailWord_1601691 prefixEnd_1601691 365527707991376937909539 := by
  unfold tailWord_1601691
  simp only [CollatzResearch.WordTrace]
  refine ⟨58418470040354528889716927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38945646693569685926477951 58418470040354528889716927)
  ·
    refine ⟨87627705060531793334575391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58418470040354528889716927 87627705060531793334575391)
    ·
      refine ⟨131441557590797690001863087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87627705060531793334575391 131441557590797690001863087)
      ·
        refine ⟨197162336386196535002794631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131441557590797690001863087 197162336386196535002794631)
        ·
          refine ⟨295743504579294802504191947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197162336386196535002794631 295743504579294802504191947)
          ·
            refine ⟨443615256868942203756287921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295743504579294802504191947 443615256868942203756287921)
            ·
              refine ⟨332711442651706652817215941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443615256868942203756287921 332711442651706652817215941)
              ·
                refine ⟨62383395497194997403227989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332711442651706652817215941 62383395497194997403227989)
                ·
                  refine ⟨365527707991376937909539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62383395497194997403227989 365527707991376937909539)
                  ·
                    rfl

theorem cell21_1601691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_1601691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601691 prefixEnd_1601691 := by exact prefixLift 1601691
  have htrace : WordTrace (prefixWord ++ tailWord_1601691) baseStart_1601691 baseEnd_1601691 := by
    simpa [prefixWord, tailWord_1601691, baseEnd_1601691] using wordTrace_append hprefix tailTrace_1601691
  have hstable : (prefixWord ++ tailWord_1601691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601691).length < 2 ^ (prefixWord ++ tailWord_1601691).sum := by decide
  have hdescent : baseEnd_1601691 < baseStart_1601691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601697 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 4]
def baseStart_1601697 : Nat := 118140960795 + 1601697 * 2 ^ 59
def prefixEnd_1601697 : Nat := 4983230072969 + 3 ^ 40 * 1601697 * 2
def baseEnd_1601697 : Nat := 365529077273122260809527

theorem tailTrace_1601697 : CollatzResearch.WordTrace tailWord_1601697 prefixEnd_1601697 365529077273122260809527 := by
  unfold tailWord_1601697
  simp only [CollatzResearch.WordTrace]
  refine ⟨58418688878332791914435345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38945792585555194609623563 58418688878332791914435345)
  ·
    refine ⟨43814016658749593935826509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58418688878332791914435345 43814016658749593935826509)
    ·
      refine ⟨16430256247031097725934941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43814016658749593935826509 16430256247031097725934941)
      ·
        refine ⟨6161346092636661647225603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16430256247031097725934941 6161346092636661647225603)
        ·
          refine ⟨9242019138954992470838405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161346092636661647225603 9242019138954992470838405)
          ·
            refine ⟨1732878588554061088282201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9242019138954992470838405 1732878588554061088282201)
            ·
              refine ⟨1299658941415545816211651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732878588554061088282201 1299658941415545816211651)
              ·
                refine ⟨1949488412123318724317477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299658941415545816211651 1949488412123318724317477)
                ·
                  refine ⟨365529077273122260809527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949488412123318724317477 365529077273122260809527)
                  ·
                    rfl

theorem cell21_1601697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_1601697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601697 prefixEnd_1601697 := by exact prefixLift 1601697
  have htrace : WordTrace (prefixWord ++ tailWord_1601697) baseStart_1601697 baseEnd_1601697 := by
    simpa [prefixWord, tailWord_1601697, baseEnd_1601697] using wordTrace_append hprefix tailTrace_1601697
  have hstable : (prefixWord ++ tailWord_1601697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601697).length < 2 ^ (prefixWord ++ tailWord_1601697).sum := by decide
  have hdescent : baseEnd_1601697 < baseStart_1601697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601722 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_1601722 : Nat := 118140960795 + 1601722 * 2 ^ 59
def prefixEnd_1601722 : Nat := 4983230072969 + 3 ^ 40 * 1601722 * 2
def baseEnd_1601722 : Nat := 365534782613727772892809

theorem tailTrace_1601722 : CollatzResearch.WordTrace tailWord_1601722 prefixEnd_1601722 365534782613727772892809 := by
  unfold tailWord_1601722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14604900175810555296023855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38946400468828147456063613 14604900175810555296023855)
  ·
    refine ⟨21907350263715832944035783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14604900175810555296023855 21907350263715832944035783)
    ·
      refine ⟨32861025395573749416053675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21907350263715832944035783 32861025395573749416053675)
      ·
        refine ⟨49291538093360624124080513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32861025395573749416053675 49291538093360624124080513)
        ·
          refine ⟨36968653570020468093060385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49291538093360624124080513 36968653570020468093060385)
          ·
            refine ⟨27726490177515351069795289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36968653570020468093060385 27726490177515351069795289)
            ·
              refine ⟨20794867633136513302346467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27726490177515351069795289 20794867633136513302346467)
              ·
                refine ⟨31192301449704769953519701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20794867633136513302346467 31192301449704769953519701)
                ·
                  refine ⟨365534782613727772892809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31192301449704769953519701 365534782613727772892809)
                  ·
                    rfl

theorem cell21_1601722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_1601722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601722 prefixEnd_1601722 := by exact prefixLift 1601722
  have htrace : WordTrace (prefixWord ++ tailWord_1601722) baseStart_1601722 baseEnd_1601722 := by
    simpa [prefixWord, tailWord_1601722, baseEnd_1601722] using wordTrace_append hprefix tailTrace_1601722
  have hstable : (prefixWord ++ tailWord_1601722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601722).length < 2 ^ (prefixWord ++ tailWord_1601722).sum := by decide
  have hdescent : baseEnd_1601722 < baseStart_1601722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601725 : List Nat := [1, 4, 1, 2, 1, 1, 1, 7, 3]
def baseStart_1601725 : Nat := 118140960795 + 1601725 * 2 ^ 59
def prefixEnd_1601725 : Nat := 4983230072969 + 3 ^ 40 * 1601725 * 2
def baseEnd_1601725 : Nat := 365535467254600434342803

theorem tailTrace_1601725 : CollatzResearch.WordTrace tailWord_1601725 prefixEnd_1601725 365535467254600434342803 := by
  unfold tailWord_1601725
  simp only [CollatzResearch.WordTrace]
  refine ⟨58419710122231352696454629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38946473414820901797636419 58419710122231352696454629)
  ·
    refine ⟨10953695647918378630585243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58419710122231352696454629 10953695647918378630585243)
    ·
      refine ⟨16430543471877567945877865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10953695647918378630585243 16430543471877567945877865)
      ·
        refine ⟨12322907603908175959408399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16430543471877567945877865 12322907603908175959408399)
        ·
          refine ⟨18484361405862263939112599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12322907603908175959408399 18484361405862263939112599)
          ·
            refine ⟨27726542108793395908668899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18484361405862263939112599 27726542108793395908668899)
            ·
              refine ⟨41589813163190093863003349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27726542108793395908668899 41589813163190093863003349)
              ·
                refine ⟨974761246012267824914141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41589813163190093863003349 974761246012267824914141)
                ·
                  refine ⟨365535467254600434342803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974761246012267824914141 365535467254600434342803)
                  ·
                    rfl

theorem cell21_1601725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_1601725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601725 prefixEnd_1601725 := by exact prefixLift 1601725
  have htrace : WordTrace (prefixWord ++ tailWord_1601725) baseStart_1601725 baseEnd_1601725 := by
    simpa [prefixWord, tailWord_1601725, baseEnd_1601725] using wordTrace_append hprefix tailTrace_1601725
  have hstable : (prefixWord ++ tailWord_1601725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601725).length < 2 ^ (prefixWord ++ tailWord_1601725).sum := by decide
  have hdescent : baseEnd_1601725 < baseStart_1601725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601739 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 4]
def baseStart_1601739 : Nat := 118140960795 + 1601739 * 2 ^ 59
def prefixEnd_1601739 : Nat := 4983230072969 + 3 ^ 40 * 1601739 * 2
def baseEnd_1601739 : Nat := 365538662245339521109441

theorem tailTrace_1601739 : CollatzResearch.WordTrace tailWord_1601739 prefixEnd_1601739 365538662245339521109441 := by
  unfold tailWord_1601739
  simp only [CollatzResearch.WordTrace]
  refine ⟨58420220744180633087464271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38946813829453755391642847 58420220744180633087464271)
  ·
    refine ⟨87630331116270949631196407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58420220744180633087464271 87630331116270949631196407)
    ·
      refine ⟨131445496674406424446794611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87630331116270949631196407 131445496674406424446794611)
      ·
        refine ⟨197168245011609636670191917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131445496674406424446794611 197168245011609636670191917)
        ·
          refine ⟨73938091879353613751321969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197168245011609636670191917 73938091879353613751321969)
          ·
            refine ⟨55453568909515210313491477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73938091879353613751321969 55453568909515210313491477)
            ·
              refine ⟨2599386042633525483444913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55453568909515210313491477 2599386042633525483444913)
              ·
                refine ⟨1949539531975144112583685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599386042633525483444913 1949539531975144112583685)
                ·
                  refine ⟨365538662245339521109441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949539531975144112583685 365538662245339521109441)
                  ·
                    rfl

theorem cell21_1601739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_1601739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601739 prefixEnd_1601739 := by exact prefixLift 1601739
  have htrace : WordTrace (prefixWord ++ tailWord_1601739) baseStart_1601739 baseEnd_1601739 := by
    simpa [prefixWord, tailWord_1601739, baseEnd_1601739] using wordTrace_append hprefix tailTrace_1601739
  have hstable : (prefixWord ++ tailWord_1601739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601739).length < 2 ^ (prefixWord ++ tailWord_1601739).sum := by decide
  have hdescent : baseEnd_1601739 < baseStart_1601739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601742 : List Nat := [4, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_1601742 : Nat := 118140960795 + 1601742 * 2 ^ 59
def prefixEnd_1601742 : Nat := 4983230072969 + 3 ^ 40 * 1601742 * 2
def baseEnd_1601742 : Nat := 365539346886212182559435

theorem tailTrace_1601742 : CollatzResearch.WordTrace tailWord_1601742 prefixEnd_1601742 365539346886212182559435 := by
  unfold tailWord_1601742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302541270396220574977935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38946886775446509733215653 7302541270396220574977935)
  ·
    refine ⟨10953811905594330862466903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7302541270396220574977935 10953811905594330862466903)
    ·
      refine ⟨16430717858391496293700355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10953811905594330862466903 16430717858391496293700355)
      ·
        refine ⟨24646076787587244440550533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16430717858391496293700355 24646076787587244440550533)
        ·
          refine ⟨4621139397672608332603225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24646076787587244440550533 4621139397672608332603225)
          ·
            refine ⟨3465854548254456249452419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621139397672608332603225 3465854548254456249452419)
            ·
              refine ⟨5198781822381684374178629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465854548254456249452419 5198781822381684374178629)
              ·
                refine ⟨974771591696565820158493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5198781822381684374178629 974771591696565820158493)
                ·
                  refine ⟨365539346886212182559435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974771591696565820158493 365539346886212182559435)
                  ·
                    rfl

theorem cell21_1601742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_1601742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601742 prefixEnd_1601742 := by exact prefixLift 1601742
  have htrace : WordTrace (prefixWord ++ tailWord_1601742) baseStart_1601742 baseEnd_1601742 := by
    simpa [prefixWord, tailWord_1601742, baseEnd_1601742] using wordTrace_append hprefix tailTrace_1601742
  have hstable : (prefixWord ++ tailWord_1601742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601742).length < 2 ^ (prefixWord ++ tailWord_1601742).sum := by decide
  have hdescent : baseEnd_1601742 < baseStart_1601742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601753 : List Nat := [1, 2, 1, 2, 3, 1, 5, 6]
def baseStart_1601753 : Nat := 118140960795 + 1601753 * 2 ^ 59
def prefixEnd_1601753 : Nat := 4983230072969 + 3 ^ 40 * 1601753 * 2
def baseEnd_1601753 : Nat := 121847285745359535958693

theorem tailTrace_1601753 : CollatzResearch.WordTrace tailWord_1601753 prefixEnd_1601753 121847285745359535958693 := by
  unfold tailWord_1601753
  simp only [CollatzResearch.WordTrace]
  refine ⟨58420731366129913478473913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38947154244086608985649275 58420731366129913478473913)
  ·
    refine ⟨43815548524597435108855435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58420731366129913478473913 43815548524597435108855435)
    ·
      refine ⟨65723322786896152663283153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43815548524597435108855435 65723322786896152663283153)
      ·
        refine ⟨49292492090172114497462365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65723322786896152663283153 49292492090172114497462365)
        ·
          refine ⟨18484684533814542936548387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49292492090172114497462365 18484684533814542936548387)
          ·
            refine ⟨27727026800721814404822581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18484684533814542936548387 27727026800721814404822581)
            ·
              refine ⟨2599408762567670100452117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27727026800721814404822581 2599408762567670100452117)
              ·
                refine ⟨121847285745359535958693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2599408762567670100452117 121847285745359535958693)
                ·
                  rfl

theorem cell21_1601753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 6].length) (baseStart_1601753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601753 prefixEnd_1601753 := by exact prefixLift 1601753
  have htrace : WordTrace (prefixWord ++ tailWord_1601753) baseStart_1601753 baseEnd_1601753 := by
    simpa [prefixWord, tailWord_1601753, baseEnd_1601753] using wordTrace_append hprefix tailTrace_1601753
  have hstable : (prefixWord ++ tailWord_1601753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601753).length < 2 ^ (prefixWord ++ tailWord_1601753).sum := by decide
  have hdescent : baseEnd_1601753 < baseStart_1601753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601770 : List Nat := [3, 1, 3, 1, 1, 2, 5, 5]
def baseStart_1601770 : Nat := 118140960795 + 1601770 * 2 ^ 59
def prefixEnd_1601770 : Nat := 4983230072969 + 3 ^ 40 * 1601770 * 2
def baseEnd_1601770 : Nat := 121848578955896785364237

theorem tailTrace_1601770 : CollatzResearch.WordTrace tailWord_1601770 prefixEnd_1601770 121848578955896785364237 := by
  unfold tailWord_1601770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605337851767081345460691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38947567604712216921228509 14605337851767081345460691)
  ·
    refine ⟨21908006777650622018191037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14605337851767081345460691 21908006777650622018191037)
    ·
      refine ⟨8215502541618983256821639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21908006777650622018191037 8215502541618983256821639)
      ·
        refine ⟨12323253812428474885232459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8215502541618983256821639 12323253812428474885232459)
        ·
          refine ⟨18484880718642712327848689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12323253812428474885232459 18484880718642712327848689)
          ·
            refine ⟨13863660538982034245886517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18484880718642712327848689 13863660538982034245886517)
            ·
              refine ⟨1299718175529565710551861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13863660538982034245886517 1299718175529565710551861)
              ·
                refine ⟨121848578955896785364237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1299718175529565710551861 121848578955896785364237)
                ·
                  rfl

theorem cell21_1601770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_1601770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601770 prefixEnd_1601770 := by exact prefixLift 1601770
  have htrace : WordTrace (prefixWord ++ tailWord_1601770) baseStart_1601770 baseEnd_1601770 := by
    simpa [prefixWord, tailWord_1601770, baseEnd_1601770] using wordTrace_append hprefix tailTrace_1601770
  have hstable : (prefixWord ++ tailWord_1601770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601770).length < 2 ^ (prefixWord ++ tailWord_1601770).sum := by decide
  have hdescent : baseEnd_1601770 < baseStart_1601770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601801 : List Nat := [1, 2, 1, 1, 3, 4, 2, 4, 3]
def baseStart_1601801 : Nat := 118140960795 + 1601801 * 2 ^ 59
def prefixEnd_1601801 : Nat := 4983230072969 + 3 ^ 40 * 1601801 * 2
def baseEnd_1601801 : Nat := 365552811490041191075981

theorem tailTrace_1601801 : CollatzResearch.WordTrace tailWord_1601801 prefixEnd_1601801 365552811490041191075981 := by
  unfold tailWord_1601801
  simp only [CollatzResearch.WordTrace]
  refine ⟨58422482069956017676221257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38948321379970678450814171 58422482069956017676221257)
  ·
    refine ⟨43816861552467013257165943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58422482069956017676221257 43816861552467013257165943)
    ·
      refine ⟨65725292328700519885748915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43816861552467013257165943 65725292328700519885748915)
      ·
        refine ⟨98587938493050779828623373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65725292328700519885748915 98587938493050779828623373)
        ·
          refine ⟨36970476934894042435733765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98587938493050779828623373 36970476934894042435733765)
          ·
            refine ⟨6931964425292632956700081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36970476934894042435733765 6931964425292632956700081)
            ·
              refine ⟨5198973318969474717525061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931964425292632956700081 5198973318969474717525061)
              ·
                refine ⟨974807497306776509535949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5198973318969474717525061 974807497306776509535949)
                ·
                  refine ⟨365552811490041191075981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974807497306776509535949 365552811490041191075981)
                  ·
                    rfl

theorem cell21_1601801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_1601801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1601801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1601801 prefixEnd_1601801 := by exact prefixLift 1601801
  have htrace : WordTrace (prefixWord ++ tailWord_1601801) baseStart_1601801 baseEnd_1601801 := by
    simpa [prefixWord, tailWord_1601801, baseEnd_1601801] using wordTrace_append hprefix tailTrace_1601801
  have hstable : (prefixWord ++ tailWord_1601801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601801).length < 2 ^ (prefixWord ++ tailWord_1601801).sum := by decide
  have hdescent : baseEnd_1601801 < baseStart_1601801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602029 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1602029 : Nat := 118140960795 + 1602029 * 2 ^ 59
def prefixEnd_1602029 : Nat := 4983230072969 + 3 ^ 40 * 1602029 * 2
def baseEnd_1602029 : Nat := 365604844196363461275515

theorem tailTrace_1602029 : CollatzResearch.WordTrace tailWord_1602029 prefixEnd_1602029 365604844196363461275515 := by
  unfold tailWord_1602029
  simp only [CollatzResearch.WordTrace]
  refine ⟨58430797913130012615521141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38953865275420008410347427 58430797913130012615521141)
  ·
    refine ⟨5477887304355938682705107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58430797913130012615521141 5477887304355938682705107)
    ·
      refine ⟨8216830956533908024057661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5477887304355938682705107 8216830956533908024057661)
      ·
        refine ⟨3081311608700215509021623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8216830956533908024057661 3081311608700215509021623)
        ·
          refine ⟨4621967413050323263532435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081311608700215509021623 4621967413050323263532435)
          ·
            refine ⟨6932951119575484895298653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621967413050323263532435 6932951119575484895298653)
            ·
              refine ⟨2599856669840806835736995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6932951119575484895298653 2599856669840806835736995)
              ·
                refine ⟨3899785004761210253605493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599856669840806835736995 3899785004761210253605493)
                ·
                  refine ⟨365604844196363461275515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3899785004761210253605493 365604844196363461275515)
                  ·
                    rfl

theorem cell21_1602029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1602029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602029 prefixEnd_1602029 := by exact prefixLift 1602029
  have htrace : WordTrace (prefixWord ++ tailWord_1602029) baseStart_1602029 baseEnd_1602029 := by
    simpa [prefixWord, tailWord_1602029, baseEnd_1602029] using wordTrace_append hprefix tailTrace_1602029
  have hstable : (prefixWord ++ tailWord_1602029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602029).length < 2 ^ (prefixWord ++ tailWord_1602029).sum := by decide
  have hdescent : baseEnd_1602029 < baseStart_1602029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602080 : List Nat := [2, 1, 1, 6, 3, 1, 2, 2, 3]
def baseStart_1602080 : Nat := 118140960795 + 1602080 * 2 ^ 59
def prefixEnd_1602080 : Nat := 4983230072969 + 3 ^ 40 * 1602080 * 2
def baseEnd_1602080 : Nat := 365616483091198705925411

theorem tailTrace_1602080 : CollatzResearch.WordTrace tailWord_1602080 prefixEnd_1602080 365616483091198705925411 := by
  unfold tailWord_1602080
  simp only [CollatzResearch.WordTrace]
  refine ⟨29216329017972624162813847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38955105357296832217085129 29216329017972624162813847)
  ·
    refine ⟨43824493526958936244220771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29216329017972624162813847 43824493526958936244220771)
    ·
      refine ⟨65736740290438404366331157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43824493526958936244220771 65736740290438404366331157)
      ·
        refine ⟨3081409701114300204671773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65736740290438404366331157 3081409701114300204671773)
        ·
          refine ⟨1155528637917862576751915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3081409701114300204671773 1155528637917862576751915)
          ·
            refine ⟨1733292956876793865127873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155528637917862576751915 1733292956876793865127873)
            ·
              refine ⟨1299969717657595398845905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733292956876793865127873 1299969717657595398845905)
              ·
                refine ⟨974977288243196549134429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299969717657595398845905 974977288243196549134429)
                ·
                  refine ⟨365616483091198705925411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974977288243196549134429 365616483091198705925411)
                  ·
                    rfl

theorem cell21_1602080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_1602080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602080 prefixEnd_1602080 := by exact prefixLift 1602080
  have htrace : WordTrace (prefixWord ++ tailWord_1602080) baseStart_1602080 baseEnd_1602080 := by
    simpa [prefixWord, tailWord_1602080, baseEnd_1602080] using wordTrace_append hprefix tailTrace_1602080
  have hstable : (prefixWord ++ tailWord_1602080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602080).length < 2 ^ (prefixWord ++ tailWord_1602080).sum := by decide
  have hdescent : baseEnd_1602080 < baseStart_1602080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602181 : List Nat := [1, 3, 1, 1, 4, 2, 3, 3, 3]
def baseStart_1602181 : Nat := 118140960795 + 1602181 * 2 ^ 59
def prefixEnd_1602181 : Nat := 4983230072969 + 3 ^ 40 * 1602181 * 2
def baseEnd_1602181 : Nat := 365639532667244974741871

theorem tailTrace_1602181 : CollatzResearch.WordTrace tailWord_1602181 prefixEnd_1602181 365639532667244974741871 := by
  unfold tailWord_1602181
  simp only [CollatzResearch.WordTrace]
  refine ⟨58436341808579342575054397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38957561205719561716702931 58436341808579342575054397)
  ·
    refine ⟨21913628178217253465645399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58436341808579342575054397 21913628178217253465645399)
    ·
      refine ⟨32870442267325880198468099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21913628178217253465645399 32870442267325880198468099)
      ·
        refine ⟨49305663400988820297702149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32870442267325880198468099 49305663400988820297702149)
        ·
          refine ⟨9244811887685403805819153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49305663400988820297702149 9244811887685403805819153)
          ·
            refine ⟨6933608915764052854364365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9244811887685403805819153 6933608915764052854364365)
            ·
              refine ⟨2600103343411519820386637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6933608915764052854364365 2600103343411519820386637)
              ·
                refine ⟨975038753779319932644989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600103343411519820386637 975038753779319932644989)
                ·
                  refine ⟨365639532667244974741871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975038753779319932644989 365639532667244974741871)
                  ·
                    rfl

theorem cell21_1602181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_1602181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602181 prefixEnd_1602181 := by exact prefixLift 1602181
  have htrace : WordTrace (prefixWord ++ tailWord_1602181) baseStart_1602181 baseEnd_1602181 := by
    simpa [prefixWord, tailWord_1602181, baseEnd_1602181] using wordTrace_append hprefix tailTrace_1602181
  have hstable : (prefixWord ++ tailWord_1602181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602181).length < 2 ^ (prefixWord ++ tailWord_1602181).sum := by decide
  have hdescent : baseEnd_1602181 < baseStart_1602181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602246 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1602246 : Nat := 118140960795 + 1602246 * 2 ^ 59
def prefixEnd_1602246 : Nat := 4983230072969 + 3 ^ 40 * 1602246 * 2
def baseEnd_1602246 : Nat := 365654366552819306158405

theorem tailTrace_1602246 : CollatzResearch.WordTrace tailWord_1602246 prefixEnd_1602246 365654366552819306158405 := by
  unfold tailWord_1602246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826209767291995583630331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38959141702229239117447061 1826209767291995583630331)
  ·
    refine ⟨2739314650937993375445497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826209767291995583630331 2739314650937993375445497)
    ·
      refine ⟨2054485988203495031584123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2739314650937993375445497 2054485988203495031584123)
      ·
        refine ⟨3081728982305242547376185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054485988203495031584123 3081728982305242547376185)
        ·
          refine ⟨2311296736728931910532139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3081728982305242547376185 2311296736728931910532139)
          ·
            refine ⟨3466945105093397865798209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311296736728931910532139 3466945105093397865798209)
            ·
              refine ⟨2600208828820048399348657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3466945105093397865798209 2600208828820048399348657)
              ·
                refine ⟨1950156621615036299511493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2600208828820048399348657 1950156621615036299511493)
                ·
                  refine ⟨365654366552819306158405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1950156621615036299511493 365654366552819306158405)
                  ·
                    rfl

theorem cell21_1602246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1602246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602246 prefixEnd_1602246 := by exact prefixLift 1602246
  have htrace : WordTrace (prefixWord ++ tailWord_1602246) baseStart_1602246 baseEnd_1602246 := by
    simpa [prefixWord, tailWord_1602246, baseEnd_1602246] using wordTrace_append hprefix tailTrace_1602246
  have hstable : (prefixWord ++ tailWord_1602246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602246).length < 2 ^ (prefixWord ++ tailWord_1602246).sum := by decide
  have hdescent : baseEnd_1602246 < baseStart_1602246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602350 : List Nat := [4, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_1602350 : Nat := 118140960795 + 1602350 * 2 ^ 59
def prefixEnd_1602350 : Nat := 4983230072969 + 3 ^ 40 * 1602350 * 2
def baseEnd_1602350 : Nat := 365678100769738236424859

theorem tailTrace_1602350 : CollatzResearch.WordTrace tailWord_1602350 prefixEnd_1602350 365678100769738236424859 := by
  unfold tailWord_1602350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7305313218120885554744563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38961670496644722958637669 7305313218120885554744563)
  ·
    refine ⟨10957969827181328332116845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7305313218120885554744563 10957969827181328332116845)
    ·
      refine ⟨4109238685192998124543817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10957969827181328332116845 4109238685192998124543817)
      ·
        refine ⟨3081929013894748593407863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4109238685192998124543817 3081929013894748593407863)
        ·
          refine ⟨4622893520842122890111795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081929013894748593407863 4622893520842122890111795)
          ·
            refine ⟨6934340281263184335167693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4622893520842122890111795 6934340281263184335167693)
            ·
              refine ⟨2600377605473694125687885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6934340281263184335167693 2600377605473694125687885)
              ·
                refine ⟨975141602052635297132957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600377605473694125687885 975141602052635297132957)
                ·
                  refine ⟨365678100769738236424859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975141602052635297132957 365678100769738236424859)
                  ·
                    rfl

theorem cell21_1602350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_1602350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602350 prefixEnd_1602350 := by exact prefixLift 1602350
  have htrace : WordTrace (prefixWord ++ tailWord_1602350) baseStart_1602350 baseEnd_1602350 := by
    simpa [prefixWord, tailWord_1602350, baseEnd_1602350] using wordTrace_append hprefix tailTrace_1602350
  have hstable : (prefixWord ++ tailWord_1602350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602350).length < 2 ^ (prefixWord ++ tailWord_1602350).sum := by decide
  have hdescent : baseEnd_1602350 < baseStart_1602350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602437 : List Nat := [1, 3, 1, 1, 3, 5, 1, 6]
def baseStart_1602437 : Nat := 118140960795 + 1602437 * 2 ^ 59
def prefixEnd_1602437 : Nat := 4983230072969 + 3 ^ 40 * 1602437 * 2
def baseEnd_1602437 : Nat := 121899318451681806158227

theorem tailTrace_1602437 : CollatzResearch.WordTrace tailWord_1602437 prefixEnd_1602437 121899318451681806158227 := by
  unfold tailWord_1602437
  simp only [CollatzResearch.WordTrace]
  refine ⟨58445678895651898296373565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38963785930434598864249043 58445678895651898296373565)
  ·
    refine ⟨21917129585869461861140087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58445678895651898296373565 21917129585869461861140087)
    ·
      refine ⟨32875694378804192791710131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21917129585869461861140087 32875694378804192791710131)
      ·
        refine ⟨49313541568206289187565197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32875694378804192791710131 49313541568206289187565197)
        ·
          refine ⟨18492578088077358445336949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49313541568206289187565197 18492578088077358445336949)
          ·
            refine ⟨1733679195757252354250339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18492578088077358445336949 1733679195757252354250339)
            ·
              refine ⟨2600518793635878531375509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733679195757252354250339 2600518793635878531375509)
              ·
                refine ⟨121899318451681806158227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2600518793635878531375509 121899318451681806158227)
                ·
                  rfl

theorem cell21_1602437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 6].length) (baseStart_1602437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602437 prefixEnd_1602437 := by exact prefixLift 1602437
  have htrace : WordTrace (prefixWord ++ tailWord_1602437) baseStart_1602437 baseEnd_1602437 := by
    simpa [prefixWord, tailWord_1602437, baseEnd_1602437] using wordTrace_append hprefix tailTrace_1602437
  have hstable : (prefixWord ++ tailWord_1602437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602437).length < 2 ^ (prefixWord ++ tailWord_1602437).sum := by decide
  have hdescent : baseEnd_1602437 < baseStart_1602437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602530 : List Nat := [3, 3, 3, 1, 1, 3, 7]
def baseStart_1602530 : Nat := 118140960795 + 1602530 * 2 ^ 59
def prefixEnd_1602530 : Nat := 4983230072969 + 3 ^ 40 * 1602530 * 2
def baseEnd_1602530 : Nat := 40635464358010880380499

theorem tailTrace_1602530 : CollatzResearch.WordTrace tailWord_1602530 prefixEnd_1602530 40635464358010880380499 := by
  unfold tailWord_1602530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14612267721078743794877261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38966047256209983453006029 14612267721078743794877261)
  ·
    refine ⟨5479600395404528923078973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14612267721078743794877261 5479600395404528923078973)
    ·
      refine ⟨2054850148276698346154615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5479600395404528923078973 2054850148276698346154615)
      ·
        refine ⟨3082275222415047519231923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054850148276698346154615 3082275222415047519231923)
        ·
          refine ⟨4623412833622571278847885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082275222415047519231923 4623412833622571278847885)
          ·
            refine ⟨1733779812608464229567957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4623412833622571278847885 1733779812608464229567957)
            ·
              refine ⟨40635464358010880380499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1733779812608464229567957 40635464358010880380499)
              ·
                rfl

theorem cell21_1602530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 7].length) (baseStart_1602530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602530 prefixEnd_1602530 := by exact prefixLift 1602530
  have htrace : WordTrace (prefixWord ++ tailWord_1602530) baseStart_1602530 baseEnd_1602530 := by
    simpa [prefixWord, tailWord_1602530, baseEnd_1602530] using wordTrace_append hprefix tailTrace_1602530
  have hstable : (prefixWord ++ tailWord_1602530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602530).length < 2 ^ (prefixWord ++ tailWord_1602530).sum := by decide
  have hdescent : baseEnd_1602530 < baseStart_1602530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602572 : List Nat := [2, 2, 1, 2, 3, 2, 2, 7]
def baseStart_1602572 : Nat := 118140960795 + 1602572 * 2 ^ 59
def prefixEnd_1602572 : Nat := 4983230072969 + 3 ^ 40 * 1602572 * 2
def baseEnd_1602572 : Nat := 121909588064771727908135

theorem tailTrace_1602572 : CollatzResearch.WordTrace tailWord_1602572 prefixEnd_1602572 121909588064771727908135 := by
  unfold tailWord_1602572
  simp only [CollatzResearch.WordTrace]
  refine ⟨29225301375081408176268985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38967068500108544235025313 29225301375081408176268985)
  ·
    refine ⟨21918976031311056132201739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29225301375081408176268985 21918976031311056132201739)
    ·
      refine ⟨32878464046966584198302609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21918976031311056132201739 32878464046966584198302609)
      ·
        refine ⟨24658848035224938148726957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32878464046966584198302609 24658848035224938148726957)
        ·
          refine ⟨9247068013209351805772609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24658848035224938148726957 9247068013209351805772609)
          ·
            refine ⟨6935301009907013854329457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9247068013209351805772609 6935301009907013854329457)
            ·
              refine ⟨5201475757430260390747093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935301009907013854329457 5201475757430260390747093)
              ·
                refine ⟨121909588064771727908135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5201475757430260390747093 121909588064771727908135)
                ·
                  rfl

theorem cell21_1602572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_1602572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602572 prefixEnd_1602572 := by exact prefixLift 1602572
  have htrace : WordTrace (prefixWord ++ tailWord_1602572) baseStart_1602572 baseEnd_1602572 := by
    simpa [prefixWord, tailWord_1602572, baseEnd_1602572] using wordTrace_append hprefix tailTrace_1602572
  have hstable : (prefixWord ++ tailWord_1602572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602572).length < 2 ^ (prefixWord ++ tailWord_1602572).sum := by decide
  have hdescent : baseEnd_1602572 < baseStart_1602572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602589 : List Nat := [1, 4, 2, 2, 4, 8]
def baseStart_1602589 : Nat := 118140960795 + 1602589 * 2 ^ 59
def prefixEnd_1602589 : Nat := 4983230072969 + 3 ^ 40 * 1602589 * 2
def baseEnd_1602589 : Nat := 13545653475034330812631

theorem tailTrace_1602589 : CollatzResearch.WordTrace tailWord_1602589 prefixEnd_1602589 13545653475034330812631 := by
  unfold tailWord_1602589
  simp only [CollatzResearch.WordTrace]
  refine ⟨58451222791101228255906821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38967481860734152170604547 58451222791101228255906821)
  ·
    refine ⟨10959604273331480297982529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58451222791101228255906821 10959604273331480297982529)
    ·
      refine ⟨8219703204998610223486897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10959604273331480297982529 8219703204998610223486897)
      ·
        refine ⟨6164777403748957667615173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8219703204998610223486897 6164777403748957667615173)
        ·
          refine ⟨1155895763202929562677845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6164777403748957667615173 1155895763202929562677845)
          ·
            refine ⟨13545653475034330812631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1155895763202929562677845 13545653475034330812631)
            ·
              rfl

theorem cell21_1602589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 8].length) (baseStart_1602589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602589 prefixEnd_1602589 := by exact prefixLift 1602589
  have htrace : WordTrace (prefixWord ++ tailWord_1602589) baseStart_1602589 baseEnd_1602589 := by
    simpa [prefixWord, tailWord_1602589, baseEnd_1602589] using wordTrace_append hprefix tailTrace_1602589
  have hstable : (prefixWord ++ tailWord_1602589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602589).length < 2 ^ (prefixWord ++ tailWord_1602589).sum := by decide
  have hdescent : baseEnd_1602589 < baseStart_1602589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602592 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_1602592 : Nat := 118140960795 + 1602592 * 2 ^ 59
def prefixEnd_1602592 : Nat := 4983230072969 + 3 ^ 40 * 1602592 * 2
def baseEnd_1602592 : Nat := 365733328466799593391031

theorem tailTrace_1602592 : CollatzResearch.WordTrace tailWord_1602592 prefixEnd_1602592 365733328466799593391031 := by
  unfold tailWord_1602592
  simp only [CollatzResearch.WordTrace]
  refine ⟨29225666105045179884133015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38967554806726906512177353 29225666105045179884133015)
  ·
    refine ⟨43838499157567769826199523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29225666105045179884133015 43838499157567769826199523)
    ·
      refine ⟨65757748736351654739299285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43838499157567769826199523 65757748736351654739299285)
      ·
        refine ⟨1541197236008241907952327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 65757748736351654739299285 1541197236008241907952327)
        ·
          refine ⟨2311795854012362861928491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541197236008241907952327 2311795854012362861928491)
          ·
            refine ⟨3467693781018544292892737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311795854012362861928491 3467693781018544292892737)
            ·
              refine ⟨2600770335763908219669553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467693781018544292892737 2600770335763908219669553)
              ·
                refine ⟨1950577751822931164752165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2600770335763908219669553 1950577751822931164752165)
                ·
                  refine ⟨365733328466799593391031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1950577751822931164752165 365733328466799593391031)
                  ·
                    rfl

theorem cell21_1602592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_1602592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602592 prefixEnd_1602592 := by exact prefixLift 1602592
  have htrace : WordTrace (prefixWord ++ tailWord_1602592) baseStart_1602592 baseEnd_1602592 := by
    simpa [prefixWord, tailWord_1602592, baseEnd_1602592] using wordTrace_append hprefix tailTrace_1602592
  have hstable : (prefixWord ++ tailWord_1602592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602592).length < 2 ^ (prefixWord ++ tailWord_1602592).sum := by decide
  have hdescent : baseEnd_1602592 < baseStart_1602592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602637 : List Nat := [1, 6, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1602637 : Nat := 118140960795 + 1602637 * 2 ^ 59
def prefixEnd_1602637 : Nat := 4983230072969 + 3 ^ 40 * 1602637 * 2
def baseEnd_1602637 : Nat := 365743598079889515140939

theorem tailTrace_1602637 : CollatzResearch.WordTrace tailWord_1602637 prefixEnd_1602637 365743598079889515140939 := by
  unfold tailWord_1602637
  simp only [CollatzResearch.WordTrace]
  refine ⟨58452973494927332453654165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38968648996618221635769443 58452973494927332453654165)
  ·
    refine ⟨2739983132574718708765039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58452973494927332453654165 2739983132574718708765039)
    ·
      refine ⟨4109974698862078063147559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2739983132574718708765039 4109974698862078063147559)
      ·
        refine ⟨6164962048293117094721339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4109974698862078063147559 6164962048293117094721339)
        ·
          refine ⟨9247443072439675642082009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6164962048293117094721339 9247443072439675642082009)
          ·
            refine ⟨6935582304329756731561507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9247443072439675642082009 6935582304329756731561507)
            ·
              refine ⟨10403373456494635097342261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6935582304329756731561507 10403373456494635097342261)
              ·
                refine ⟨975316261546372040375837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10403373456494635097342261 975316261546372040375837)
                ·
                  refine ⟨365743598079889515140939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975316261546372040375837 365743598079889515140939)
                  ·
                    rfl

theorem cell21_1602637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1602637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602637 prefixEnd_1602637 := by exact prefixLift 1602637
  have htrace : WordTrace (prefixWord ++ tailWord_1602637) baseStart_1602637 baseEnd_1602637 := by
    simpa [prefixWord, tailWord_1602637, baseEnd_1602637] using wordTrace_append hprefix tailTrace_1602637
  have hstable : (prefixWord ++ tailWord_1602637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602637).length < 2 ^ (prefixWord ++ tailWord_1602637).sum := by decide
  have hdescent : baseEnd_1602637 < baseStart_1602637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602654 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1602654 : Nat := 118140960795 + 1602654 * 2 ^ 59
def prefixEnd_1602654 : Nat := 4983230072969 + 3 ^ 40 * 1602654 * 2
def baseEnd_1602654 : Nat := 365747477711501263357571

theorem tailTrace_1602654 : CollatzResearch.WordTrace tailWord_1602654 prefixEnd_1602654 365747477711501263357571 := by
  unfold tailWord_1602654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306699191983218044627877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38969062357243829571348677 7306699191983218044627877)
  ·
    refine ⟨1370006098496853383367727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7306699191983218044627877 1370006098496853383367727)
    ·
      refine ⟨2055009147745280075051591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370006098496853383367727 2055009147745280075051591)
      ·
        refine ⟨3082513721617920112577387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055009147745280075051591 3082513721617920112577387)
        ·
          refine ⟨4623770582426880168866081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082513721617920112577387 4623770582426880168866081)
          ·
            refine ⟨3467827936820160126649561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4623770582426880168866081 3467827936820160126649561)
            ·
              refine ⟨2600870952615120094987171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467827936820160126649561 2600870952615120094987171)
              ·
                refine ⟨3901306428922680142480757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600870952615120094987171 3901306428922680142480757)
                ·
                  refine ⟨365747477711501263357571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3901306428922680142480757 365747477711501263357571)
                  ·
                    rfl

theorem cell21_1602654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1602654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602654 prefixEnd_1602654 := by exact prefixLift 1602654
  have htrace : WordTrace (prefixWord ++ tailWord_1602654) baseStart_1602654 baseEnd_1602654 := by
    simpa [prefixWord, tailWord_1602654, baseEnd_1602654] using wordTrace_append hprefix tailTrace_1602654
  have hstable : (prefixWord ++ tailWord_1602654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602654).length < 2 ^ (prefixWord ++ tailWord_1602654).sum := by decide
  have hdescent : baseEnd_1602654 < baseStart_1602654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602707 : List Nat := [1, 1, 1, 2, 1, 2, 13]
def baseStart_1602707 : Nat := 118140960795 + 1602707 * 2 ^ 59
def prefixEnd_1602707 : Nat := 4983230072969 + 3 ^ 40 * 1602707 * 2
def baseEnd_1602707 : Nat := 40639952559287216552681

theorem tailTrace_1602707 : CollatzResearch.WordTrace tailWord_1602707 prefixEnd_1602707 40639952559287216552681 := by
  unfold tailWord_1602707
  simp only [CollatzResearch.WordTrace]
  refine ⟨58455526604673734408702375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38970351069782489605801583 58455526604673734408702375)
  ·
    refine ⟨87683289907010601613053563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58455526604673734408702375 87683289907010601613053563)
    ·
      refine ⟨131524934860515902419580345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87683289907010601613053563 131524934860515902419580345)
      ·
        refine ⟨98643701145386926814685259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131524934860515902419580345 98643701145386926814685259)
        ·
          refine ⟨147965551718080390222027889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98643701145386926814685259 147965551718080390222027889)
          ·
            refine ⟨110974163788560292666520917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147965551718080390222027889 110974163788560292666520917)
            ·
              refine ⟨40639952559287216552681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 110974163788560292666520917 40639952559287216552681)
              ·
                rfl

theorem cell21_1602707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 13].length) (baseStart_1602707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602707 prefixEnd_1602707 := by exact prefixLift 1602707
  have htrace : WordTrace (prefixWord ++ tailWord_1602707) baseStart_1602707 baseEnd_1602707 := by
    simpa [prefixWord, tailWord_1602707, baseEnd_1602707] using wordTrace_append hprefix tailTrace_1602707
  have hstable : (prefixWord ++ tailWord_1602707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602707).length < 2 ^ (prefixWord ++ tailWord_1602707).sum := by decide
  have hdescent : baseEnd_1602707 < baseStart_1602707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602724 : List Nat := [2, 3, 1, 2, 3, 1, 1, 8]
def baseStart_1602724 : Nat := 118140960795 + 1602724 * 2 ^ 59
def prefixEnd_1602724 : Nat := 4983230072969 + 3 ^ 40 * 1602724 * 2
def baseEnd_1602724 : Nat := 121921150888398899063587

theorem tailTrace_1602724 : CollatzResearch.WordTrace tailWord_1602724 prefixEnd_1602724 121921150888398899063587 := by
  unfold tailWord_1602724
  simp only [CollatzResearch.WordTrace]
  refine ⟨29228073322806073156035613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38970764430408097541380817 29228073322806073156035613)
  ·
    refine ⟨10960527496052277433513355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29228073322806073156035613 10960527496052277433513355)
    ·
      refine ⟨16440791244078416150270033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10960527496052277433513355 16440791244078416150270033)
      ·
        refine ⟨12330593433058812112702525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16440791244078416150270033 12330593433058812112702525)
        ·
          refine ⟨4623972537397054542263447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12330593433058812112702525 4623972537397054542263447)
          ·
            refine ⟨6935958806095581813395171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623972537397054542263447 6935958806095581813395171)
            ·
              refine ⟨10403938209143372720092757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6935958806095581813395171 10403938209143372720092757)
              ·
                refine ⟨121921150888398899063587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10403938209143372720092757 121921150888398899063587)
                ·
                  rfl

theorem cell21_1602724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_1602724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602724 prefixEnd_1602724 := by exact prefixLift 1602724
  have htrace : WordTrace (prefixWord ++ tailWord_1602724) baseStart_1602724 baseEnd_1602724 := by
    simpa [prefixWord, tailWord_1602724, baseEnd_1602724] using wordTrace_append hprefix tailTrace_1602724
  have hstable : (prefixWord ++ tailWord_1602724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602724).length < 2 ^ (prefixWord ++ tailWord_1602724).sum := by decide
  have hdescent : baseEnd_1602724 < baseStart_1602724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602727 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 4]
def baseStart_1602727 : Nat := 118140960795 + 1602727 * 2 ^ 59
def prefixEnd_1602727 : Nat := 4983230072969 + 3 ^ 40 * 1602727 * 2
def baseEnd_1602727 : Nat := 365764137306069358640755

theorem tailTrace_1602727 : CollatzResearch.WordTrace tailWord_1602727 prefixEnd_1602727 365764137306069358640755 := by
  unfold tailWord_1602727
  simp only [CollatzResearch.WordTrace]
  refine ⟨58456256064601277824430435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38970837376400851882953623 58456256064601277824430435)
  ·
    refine ⟨87684384096901916736645653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58456256064601277824430435 87684384096901916736645653)
    ·
      refine ⟨4110205504542277347030265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87684384096901916736645653 4110205504542277347030265)
      ·
        refine ⟨3082654128406708010272699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4110205504542277347030265 3082654128406708010272699)
        ·
          refine ⟨4623981192610062015409049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082654128406708010272699 4623981192610062015409049)
          ·
            refine ⟨3467985894457546511556787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4623981192610062015409049 3467985894457546511556787)
            ·
              refine ⟨5201978841686319767335181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3467985894457546511556787 5201978841686319767335181)
              ·
                refine ⟨1950742065632369912750693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5201978841686319767335181 1950742065632369912750693)
                ·
                  refine ⟨365764137306069358640755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1950742065632369912750693 365764137306069358640755)
                  ·
                    rfl

theorem cell21_1602727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_1602727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602727 prefixEnd_1602727 := by exact prefixLift 1602727
  have htrace : WordTrace (prefixWord ++ tailWord_1602727) baseStart_1602727 baseEnd_1602727 := by
    simpa [prefixWord, tailWord_1602727, baseEnd_1602727] using wordTrace_append hprefix tailTrace_1602727
  have hstable : (prefixWord ++ tailWord_1602727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602727).length < 2 ^ (prefixWord ++ tailWord_1602727).sum := by decide
  have hdescent : baseEnd_1602727 < baseStart_1602727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602758 : List Nat := [6, 1, 2, 2, 10]
def baseStart_1602758 : Nat := 118140960795 + 1602758 * 2 ^ 59
def prefixEnd_1602758 : Nat := 4983230072969 + 3 ^ 40 * 1602758 * 2
def baseEnd_1602758 : Nat := 4515693974424940662025

theorem tailTrace_1602758 : CollatzResearch.WordTrace tailWord_1602758 prefixEnd_1602758 4515693974424940662025 := by
  unfold tailWord_1602758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826793335234030316212779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38971591151659313412539285 1826793335234030316212779)
  ·
    refine ⟨2740190002851045474319169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826793335234030316212779 2740190002851045474319169)
    ·
      refine ⟨2055142502138284105739377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2740190002851045474319169 2055142502138284105739377)
      ·
        refine ⟨1541356876603713079304533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2055142502138284105739377 1541356876603713079304533)
        ·
          refine ⟨4515693974424940662025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1541356876603713079304533 4515693974424940662025)
          ·
            rfl

theorem cell21_1602758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 10].length) (baseStart_1602758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602758 prefixEnd_1602758 := by exact prefixLift 1602758
  have htrace : WordTrace (prefixWord ++ tailWord_1602758) baseStart_1602758 baseEnd_1602758 := by
    simpa [prefixWord, tailWord_1602758, baseEnd_1602758] using wordTrace_append hprefix tailTrace_1602758
  have hstable : (prefixWord ++ tailWord_1602758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602758).length < 2 ^ (prefixWord ++ tailWord_1602758).sum := by decide
  have hdescent : baseEnd_1602758 < baseStart_1602758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602865 : List Nat := [1, 2, 2, 3, 3, 3, 1, 3, 3]
def baseStart_1602865 : Nat := 118140960795 + 1602865 * 2 ^ 59
def prefixEnd_1602865 : Nat := 4983230072969 + 3 ^ 40 * 1602865 * 2
def baseEnd_1602865 : Nat := 365795630786211785340473

theorem tailTrace_1602865 : CollatzResearch.WordTrace tailWord_1602865 prefixEnd_1602865 365795630786211785340473 := by
  unfold tailWord_1602865
  simp only [CollatzResearch.WordTrace]
  refine ⟨58461289338101327392954049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38974192892067551595302699 58461289338101327392954049)
  ·
    refine ⟨43845967003575995544715537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58461289338101327392954049 43845967003575995544715537)
    ·
      refine ⟨32884475252681996658536653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43845967003575995544715537 32884475252681996658536653)
      ·
        refine ⟨12331678219755748746951245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32884475252681996658536653 12331678219755748746951245)
        ·
          refine ⟨4624379332408405780106717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12331678219755748746951245 4624379332408405780106717)
          ·
            refine ⟨1734142249653152167540019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4624379332408405780106717 1734142249653152167540019)
            ·
              refine ⟨2601213374479728251310029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734142249653152167540019 2601213374479728251310029)
              ·
                refine ⟨975455015429898094241261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2601213374479728251310029 975455015429898094241261)
                ·
                  refine ⟨365795630786211785340473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975455015429898094241261 365795630786211785340473)
                  ·
                    rfl

theorem cell21_1602865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_1602865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602865 prefixEnd_1602865 := by exact prefixLift 1602865
  have htrace : WordTrace (prefixWord ++ tailWord_1602865) baseStart_1602865 baseEnd_1602865 := by
    simpa [prefixWord, tailWord_1602865, baseEnd_1602865] using wordTrace_append hprefix tailTrace_1602865
  have hstable : (prefixWord ++ tailWord_1602865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602865).length < 2 ^ (prefixWord ++ tailWord_1602865).sum := by decide
  have hdescent : baseEnd_1602865 < baseStart_1602865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602876 : List Nat := [2, 2, 2, 2, 1, 5, 7]
def baseStart_1602876 : Nat := 118140960795 + 1602876 * 2 ^ 59
def prefixEnd_1602876 : Nat := 4983230072969 + 3 ^ 40 * 1602876 * 2
def baseEnd_1602876 : Nat := 40644237904008690073013

theorem tailTrace_1602876 : CollatzResearch.WordTrace tailWord_1602876 prefixEnd_1602876 40644237904008690073013 := by
  unfold tailWord_1602876
  simp only [CollatzResearch.WordTrace]
  refine ⟨29230845270530738135802241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38974460360707650847736321 29230845270530738135802241)
  ·
    refine ⟨21923133952898053601851681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29230845270530738135802241 21923133952898053601851681)
    ·
      refine ⟨16442350464673540201388761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21923133952898053601851681 16442350464673540201388761)
      ·
        refine ⟨12331762848505155151041571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16442350464673540201388761 12331762848505155151041571)
        ·
          refine ⟨18497644272757732726562357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12331762848505155151041571 18497644272757732726562357)
          ·
            refine ⟨1734154150571037443115221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18497644272757732726562357 1734154150571037443115221)
            ·
              refine ⟨40644237904008690073013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1734154150571037443115221 40644237904008690073013)
              ·
                rfl

theorem cell21_1602876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 7].length) (baseStart_1602876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602876 prefixEnd_1602876 := by exact prefixLift 1602876
  have htrace : WordTrace (prefixWord ++ tailWord_1602876) baseStart_1602876 baseEnd_1602876 := by
    simpa [prefixWord, tailWord_1602876, baseEnd_1602876] using wordTrace_append hprefix tailTrace_1602876
  have hstable : (prefixWord ++ tailWord_1602876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602876).length < 2 ^ (prefixWord ++ tailWord_1602876).sum := by decide
  have hdescent : baseEnd_1602876 < baseStart_1602876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602952 : List Nat := [2, 1, 3, 3, 1, 2, 3, 6]
def baseStart_1602952 : Nat := 118140960795 + 1602952 * 2 ^ 59
def prefixEnd_1602952 : Nat := 4983230072969 + 3 ^ 40 * 1602952 * 2
def baseEnd_1602952 : Nat := 121938495123839655796765

theorem tailTrace_1602952 : CollatzResearch.WordTrace tailWord_1602952 prefixEnd_1602952 121938495123839655796765 := by
  unfold tailWord_1602952
  simp only [CollatzResearch.WordTrace]
  refine ⟨29232231244393070625685555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38976308325857427500914073 29232231244393070625685555)
  ·
    refine ⟨43848346866589605938528333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29232231244393070625685555 43848346866589605938528333)
    ·
      refine ⟨16443130074971102226948125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43848346866589605938528333 16443130074971102226948125)
      ·
        refine ⟨6166173778114163335105547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16443130074971102226948125 6166173778114163335105547)
        ·
          refine ⟨9249260667171245002658321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166173778114163335105547 9249260667171245002658321)
          ·
            refine ⟨6936945500378433751993741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9249260667171245002658321 6936945500378433751993741)
            ·
              refine ⟨2601354562641912656997653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6936945500378433751993741 2601354562641912656997653)
              ·
                refine ⟨121938495123839655796765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2601354562641912656997653 121938495123839655796765)
                ·
                  rfl

theorem cell21_1602952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_1602952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1602952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1602952 prefixEnd_1602952 := by exact prefixLift 1602952
  have htrace : WordTrace (prefixWord ++ tailWord_1602952) baseStart_1602952 baseEnd_1602952 := by
    simpa [prefixWord, tailWord_1602952, baseEnd_1602952] using wordTrace_append hprefix tailTrace_1602952
  have hstable : (prefixWord ++ tailWord_1602952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602952).length < 2 ^ (prefixWord ++ tailWord_1602952).sum := by decide
  have hdescent : baseEnd_1602952 < baseStart_1602952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603158 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1603158 : Nat := 118140960795 + 1603158 * 2 ^ 59
def prefixEnd_1603158 : Nat := 4983230072969 + 3 ^ 40 * 1603158 * 2
def baseEnd_1603158 : Nat := 365862497378108386956541

theorem tailTrace_1603158 : CollatzResearch.WordTrace tailWord_1603158 prefixEnd_1603158 365862497378108386956541 := by
  unfold tailWord_1603158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654498495377489902085633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38981317284026558955580085 3654498495377489902085633)
  ·
    refine ⟨2740873871533117426564225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3654498495377489902085633 2740873871533117426564225)
    ·
      refine ⟨2055655403649838069923169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2740873871533117426564225 2055655403649838069923169)
      ·
        refine ⟨1541741552737378552442377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2055655403649838069923169 1541741552737378552442377)
        ·
          refine ⟨1156306164553033914331783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1541741552737378552442377 1156306164553033914331783)
          ·
            refine ⟨1734459246829550871497675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156306164553033914331783 1734459246829550871497675)
            ·
              refine ⟨2601688870244326307246513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734459246829550871497675 2601688870244326307246513)
              ·
                refine ⟨1951266652683244730434885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601688870244326307246513 1951266652683244730434885)
                ·
                  refine ⟨365862497378108386956541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951266652683244730434885 365862497378108386956541)
                  ·
                    rfl

theorem cell21_1603158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1603158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603158 prefixEnd_1603158 := by exact prefixLift 1603158
  have htrace : WordTrace (prefixWord ++ tailWord_1603158) baseStart_1603158 baseEnd_1603158 := by
    simpa [prefixWord, tailWord_1603158, baseEnd_1603158] using wordTrace_append hprefix tailTrace_1603158
  have hstable : (prefixWord ++ tailWord_1603158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603158).length < 2 ^ (prefixWord ++ tailWord_1603158).sum := by decide
  have hdescent : baseEnd_1603158 < baseStart_1603158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603197 : List Nat := [1, 4, 1, 1, 4, 3, 2, 5]
def baseStart_1603197 : Nat := 118140960795 + 1603197 * 2 ^ 59
def prefixEnd_1603197 : Nat := 4983230072969 + 3 ^ 40 * 1603197 * 2
def baseEnd_1603197 : Nat := 121957132569817661935487

theorem tailTrace_1603197 : CollatzResearch.WordTrace tailWord_1603197 prefixEnd_1603197 121957132569817661935487 := by
  unfold tailWord_1603197
  simp only [CollatzResearch.WordTrace]
  refine ⟨58473398372898548094039845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38982265581932365396026563 58473398372898548094039845)
  ·
    refine ⟨10963762194918477767632471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58473398372898548094039845 10963762194918477767632471)
    ·
      refine ⟨16445643292377716651448707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10963762194918477767632471 16445643292377716651448707)
      ·
        refine ⟨24668464938566574977173061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16445643292377716651448707 24668464938566574977173061)
        ·
          refine ⟨4625337175981232808219949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24668464938566574977173061 4625337175981232808219949)
          ·
            refine ⟨1734501440992962303082481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4625337175981232808219949 1734501440992962303082481)
            ·
              refine ⟨1300876080744721727311861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734501440992962303082481 1300876080744721727311861)
              ·
                refine ⟨121957132569817661935487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1300876080744721727311861 121957132569817661935487)
                ·
                  rfl

theorem cell21_1603197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 5].length) (baseStart_1603197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603197 prefixEnd_1603197 := by exact prefixLift 1603197
  have htrace : WordTrace (prefixWord ++ tailWord_1603197) baseStart_1603197 baseEnd_1603197 := by
    simpa [prefixWord, tailWord_1603197, baseEnd_1603197] using wordTrace_append hprefix tailTrace_1603197
  have hstable : (prefixWord ++ tailWord_1603197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603197).length < 2 ^ (prefixWord ++ tailWord_1603197).sum := by decide
  have hdescent : baseEnd_1603197 < baseStart_1603197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603228 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_1603228 : Nat := 118140960795 + 1603228 * 2 ^ 59
def prefixEnd_1603228 : Nat := 4983230072969 + 3 ^ 40 * 1603228 * 2
def baseEnd_1603228 : Nat := 365878472331803820789731

theorem tailTrace_1603228 : CollatzResearch.WordTrace tailWord_1603228 prefixEnd_1603228 365878472331803820789731 := by
  unfold tailWord_1603228
  simp only [CollatzResearch.WordTrace]
  refine ⟨29237264517893120194209169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38983019357190826925612225 29237264517893120194209169)
  ·
    refine ⟨21927948388419840145656877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29237264517893120194209169 21927948388419840145656877)
    ·
      refine ⟨8222980645657440054621329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21927948388419840145656877 8222980645657440054621329)
      ·
        refine ⟨6167235484243080040965997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8222980645657440054621329 6167235484243080040965997)
        ·
          refine ⟨2312713306591155015362249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6167235484243080040965997 2312713306591155015362249)
          ·
            refine ⟨1734534979943366261521687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312713306591155015362249 1734534979943366261521687)
            ·
              refine ⟨2601802469915049392282531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734534979943366261521687 2601802469915049392282531)
              ·
                refine ⟨3902703704872574088423797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601802469915049392282531 3902703704872574088423797)
                ·
                  refine ⟨365878472331803820789731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3902703704872574088423797 365878472331803820789731)
                  ·
                    rfl

theorem cell21_1603228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_1603228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603228 prefixEnd_1603228 := by exact prefixLift 1603228
  have htrace : WordTrace (prefixWord ++ tailWord_1603228) baseStart_1603228 baseEnd_1603228 := by
    simpa [prefixWord, tailWord_1603228, baseEnd_1603228] using wordTrace_append hprefix tailTrace_1603228
  have hstable : (prefixWord ++ tailWord_1603228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603228).length < 2 ^ (prefixWord ++ tailWord_1603228).sum := by decide
  have hdescent : baseEnd_1603228 < baseStart_1603228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603287 : List Nat := [1, 1, 3, 2, 1, 3, 3, 4, 3]
def baseStart_1603287 : Nat := 118140960795 + 1603287 * 2 ^ 59
def prefixEnd_1603287 : Nat := 4983230072969 + 3 ^ 40 * 1603287 * 2
def baseEnd_1603287 : Nat := 365891936935632829306277

theorem tailTrace_1603287 : CollatzResearch.WordTrace tailWord_1603287 prefixEnd_1603287 365891936935632829306277 := by
  unfold tailWord_1603287
  simp only [CollatzResearch.WordTrace]
  refine ⟨58476680942572493464816115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38984453961714995643210743 58476680942572493464816115)
  ·
    refine ⟨87715021413858740197224173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58476680942572493464816115 87715021413858740197224173)
    ·
      refine ⟨32893133030197027573959065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87715021413858740197224173 32893133030197027573959065)
      ·
        refine ⟨24669849772647770680469299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32893133030197027573959065 24669849772647770680469299)
        ·
          refine ⟨37004774658971656020703949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24669849772647770680469299 37004774658971656020703949)
          ·
            refine ⟨13876790497114371007763981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37004774658971656020703949 13876790497114371007763981)
            ·
              refine ⟨5203796436417889127911493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13876790497114371007763981 5203796436417889127911493)
              ·
                refine ⟨975711831828354211483405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5203796436417889127911493 975711831828354211483405)
                ·
                  refine ⟨365891936935632829306277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975711831828354211483405 365891936935632829306277)
                  ·
                    rfl

theorem cell21_1603287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 3].length) (baseStart_1603287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603287 prefixEnd_1603287 := by exact prefixLift 1603287
  have htrace : WordTrace (prefixWord ++ tailWord_1603287) baseStart_1603287 baseEnd_1603287 := by
    simpa [prefixWord, tailWord_1603287, baseEnd_1603287] using wordTrace_append hprefix tailTrace_1603287
  have hstable : (prefixWord ++ tailWord_1603287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603287).length < 2 ^ (prefixWord ++ tailWord_1603287).sum := by decide
  have hdescent : baseEnd_1603287 < baseStart_1603287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603301 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 4]
def baseStart_1603301 : Nat := 118140960795 + 1603301 * 2 ^ 59
def prefixEnd_1603301 : Nat := 4983230072969 + 3 ^ 40 * 1603301 * 2
def baseEnd_1603301 : Nat := 365895131926371916072915

theorem tailTrace_1603301 : CollatzResearch.WordTrace tailWord_1603301 prefixEnd_1603301 365895131926371916072915 := by
  unfold tailWord_1603301
  simp only [CollatzResearch.WordTrace]
  refine ⟨58477191564521773855825757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38984794376347849237217171 58477191564521773855825757)
  ·
    refine ⟨21928946836695665195934659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58477191564521773855825757 21928946836695665195934659)
    ·
      refine ⟨32893420255043497793901989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21928946836695665195934659 32893420255043497793901989)
      ·
        refine ⟨6167516297820655836356623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32893420255043497793901989 6167516297820655836356623)
        ·
          refine ⟨9251274446730983754534935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6167516297820655836356623 9251274446730983754534935)
          ·
            refine ⟨13876911670096475631802403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9251274446730983754534935 13876911670096475631802403)
            ·
              refine ⟨20815367505144713447703605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13876911670096475631802403 20815367505144713447703605)
              ·
                refine ⟨1951440703607316885722213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20815367505144713447703605 1951440703607316885722213)
                ·
                  refine ⟨365895131926371916072915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951440703607316885722213 365895131926371916072915)
                  ·
                    rfl

theorem cell21_1603301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_1603301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603301 prefixEnd_1603301 := by exact prefixLift 1603301
  have htrace : WordTrace (prefixWord ++ tailWord_1603301) baseStart_1603301 baseEnd_1603301 := by
    simpa [prefixWord, tailWord_1603301, baseEnd_1603301] using wordTrace_append hprefix tailTrace_1603301
  have hstable : (prefixWord ++ tailWord_1603301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603301).length < 2 ^ (prefixWord ++ tailWord_1603301).sum := by decide
  have hdescent : baseEnd_1603301 < baseStart_1603301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603335 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 4]
def baseStart_1603335 : Nat := 118140960795 + 1603335 * 2 ^ 59
def prefixEnd_1603335 : Nat := 4983230072969 + 3 ^ 40 * 1603335 * 2
def baseEnd_1603335 : Nat := 365902891189595412506179

theorem tailTrace_1603335 : CollatzResearch.WordTrace tailWord_1603335 prefixEnd_1603335 365902891189595412506179 := by
  unfold tailWord_1603335
  simp only [CollatzResearch.WordTrace]
  refine ⟨58478431646398597662563459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38985621097599065108375639 58478431646398597662563459)
  ·
    refine ⟨87717647469597896493845189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58478431646398597662563459 87717647469597896493845189)
    ·
      refine ⟨16447058900549605592595973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87717647469597896493845189 16447058900549605592595973)
      ·
        refine ⟨3083823543853051048611745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16447058900549605592595973 3083823543853051048611745)
        ·
          refine ⟨2312867657889788286458809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3083823543853051048611745 2312867657889788286458809)
          ·
            refine ⟨1734650743417341214844107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312867657889788286458809 1734650743417341214844107)
            ·
              refine ⟨2601976115126011822266161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734650743417341214844107 2601976115126011822266161)
              ·
                refine ⟨1951482086344508866699621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601976115126011822266161 1951482086344508866699621)
                ·
                  refine ⟨365902891189595412506179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951482086344508866699621 365902891189595412506179)
                  ·
                    rfl

theorem cell21_1603335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 4].length) (baseStart_1603335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603335 prefixEnd_1603335 := by exact prefixLift 1603335
  have htrace : WordTrace (prefixWord ++ tailWord_1603335) baseStart_1603335 baseEnd_1603335 := by
    simpa [prefixWord, tailWord_1603335, baseEnd_1603335] using wordTrace_append hprefix tailTrace_1603335
  have hstable : (prefixWord ++ tailWord_1603335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603335).length < 2 ^ (prefixWord ++ tailWord_1603335).sum := by decide
  have hdescent : baseEnd_1603335 < baseStart_1603335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603481 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 7]
def baseStart_1603481 : Nat := 118140960795 + 1603481 * 2 ^ 59
def prefixEnd_1603481 : Nat := 4983230072969 + 3 ^ 40 * 1603481 * 2
def baseEnd_1603481 : Nat := 365936210378731603072547

theorem tailTrace_1603481 : CollatzResearch.WordTrace tailWord_1603481 prefixEnd_1603481 365936210378731603072547 := by
  unfold tailWord_1603481
  simp only [CollatzResearch.WordTrace]
  refine ⟨58483756703869664597378297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38989171135913109731585531 58483756703869664597378297)
  ·
    refine ⟨43862817527902248448033723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58483756703869664597378297 43862817527902248448033723)
    ·
      refine ⟨65794226291853372672050585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43862817527902248448033723 65794226291853372672050585)
      ·
        refine ⟨49345669718890029504037939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65794226291853372672050585 49345669718890029504037939)
        ·
          refine ⟨74018504578335044256056909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49345669718890029504037939 74018504578335044256056909)
          ·
            refine ⟨27756939216875641596021341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74018504578335044256056909 27756939216875641596021341)
            ·
              refine ⟨10408852206328365598508003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27756939216875641596021341 10408852206328365598508003)
              ·
                refine ⟨15613278309492548397762005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408852206328365598508003 15613278309492548397762005)
                ·
                  refine ⟨365936210378731603072547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15613278309492548397762005 365936210378731603072547)
                  ·
                    rfl

theorem cell21_1603481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_1603481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603481 prefixEnd_1603481 := by exact prefixLift 1603481
  have htrace : WordTrace (prefixWord ++ tailWord_1603481) baseStart_1603481 baseEnd_1603481 := by
    simpa [prefixWord, tailWord_1603481, baseEnd_1603481] using wordTrace_append hprefix tailTrace_1603481
  have hstable : (prefixWord ++ tailWord_1603481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603481).length < 2 ^ (prefixWord ++ tailWord_1603481).sum := by decide
  have hdescent : baseEnd_1603481 < baseStart_1603481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603512 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_1603512 : Nat := 118140960795 + 1603512 * 2 ^ 59
def prefixEnd_1603512 : Nat := 4983230072969 + 3 ^ 40 * 1603512 * 2
def baseEnd_1603512 : Nat := 365943285001082438055817

theorem tailTrace_1603512 : CollatzResearch.WordTrace tailWord_1603512 prefixEnd_1603512 365943285001082438055817 := by
  unfold tailWord_1603512
  simp only [CollatzResearch.WordTrace]
  refine ⟨29242443683378678445878395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38989924911171571261171193 29242443683378678445878395)
  ·
    refine ⟨43863665525068017668817593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29242443683378678445878395 43863665525068017668817593)
    ·
      refine ⟨32897749143801013251613195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43863665525068017668817593 32897749143801013251613195)
      ·
        refine ⟨49346623715701519877419793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32897749143801013251613195 49346623715701519877419793)
        ·
          refine ⟨37009967786776139908064845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49346623715701519877419793 37009967786776139908064845)
          ·
            refine ⟨13878737920041052465524317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37009967786776139908064845 13878737920041052465524317)
            ·
              refine ⟨5204526720015394674571619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13878737920041052465524317 5204526720015394674571619)
              ·
                refine ⟨7806790080023092011857429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204526720015394674571619 7806790080023092011857429)
                ·
                  refine ⟨365943285001082438055817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7806790080023092011857429 365943285001082438055817)
                  ·
                    rfl

theorem cell21_1603512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_1603512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603512 prefixEnd_1603512 := by exact prefixLift 1603512
  have htrace : WordTrace (prefixWord ++ tailWord_1603512) baseStart_1603512 baseEnd_1603512 := by
    simpa [prefixWord, tailWord_1603512, baseEnd_1603512] using wordTrace_append hprefix tailTrace_1603512
  have hstable : (prefixWord ++ tailWord_1603512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603512).length < 2 ^ (prefixWord ++ tailWord_1603512).sum := by decide
  have hdescent : baseEnd_1603512 < baseStart_1603512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603549 : List Nat := [1, 4, 3, 1, 3, 2, 1, 3, 3]
def baseStart_1603549 : Nat := 118140960795 + 1603549 * 2 ^ 59
def prefixEnd_1603549 : Nat := 4983230072969 + 3 ^ 40 * 1603549 * 2
def baseEnd_1603549 : Nat := 365951728905178595939075

theorem tailTrace_1603549 : CollatzResearch.WordTrace tailWord_1603549 prefixEnd_1603549 365951728905178595939075 := by
  unfold tailWord_1603549
  simp only [CollatzResearch.WordTrace]
  refine ⟨58486236867623312210853701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38990824578415541473902467 58486236867623312210853701)
  ·
    refine ⟨10966169412679371039535069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58486236867623312210853701 10966169412679371039535069)
    ·
      refine ⟨4112313529754764139825651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10966169412679371039535069 4112313529754764139825651)
      ·
        refine ⟨6168470294632146209738477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112313529754764139825651 6168470294632146209738477)
        ·
          refine ⟨2313176360487054828651929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6168470294632146209738477 2313176360487054828651929)
          ·
            refine ⟨1734882270365291121488947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2313176360487054828651929 1734882270365291121488947)
            ·
              refine ⟨2602323405547936682233421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734882270365291121488947 2602323405547936682233421)
              ·
                refine ⟨975871277080476255837533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2602323405547936682233421 975871277080476255837533)
                ·
                  refine ⟨365951728905178595939075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975871277080476255837533 365951728905178595939075)
                  ·
                    rfl

theorem cell21_1603549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_1603549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603549 prefixEnd_1603549 := by exact prefixLift 1603549
  have htrace : WordTrace (prefixWord ++ tailWord_1603549) baseStart_1603549 baseEnd_1603549 := by
    simpa [prefixWord, tailWord_1603549, baseEnd_1603549] using wordTrace_append hprefix tailTrace_1603549
  have hstable : (prefixWord ++ tailWord_1603549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603549).length < 2 ^ (prefixWord ++ tailWord_1603549).sum := by decide
  have hdescent : baseEnd_1603549 < baseStart_1603549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603698 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1603698 : Nat := 118140960795 + 1603698 * 2 ^ 59
def prefixEnd_1603698 : Nat := 4983230072969 + 3 ^ 40 * 1603698 * 2
def baseEnd_1603698 : Nat := 365985732735187447955437

theorem tailTrace_1603698 : CollatzResearch.WordTrace tailWord_1603698 prefixEnd_1603698 365985732735187447955437 := by
  unfold tailWord_1603698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14622917836020877664506937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38994447562722340438685165 14622917836020877664506937)
  ·
    refine ⟨10967188377015658248380203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14622917836020877664506937 10967188377015658248380203)
    ·
      refine ⟨16450782565523487372570305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10967188377015658248380203 16450782565523487372570305)
      ·
        refine ⟨12338086924142615529427729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16450782565523487372570305 12338086924142615529427729)
        ·
          refine ⟨9253565193106961647070797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12338086924142615529427729 9253565193106961647070797)
          ·
            refine ⟨3470086947415110617651549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9253565193106961647070797 3470086947415110617651549)
            ·
              refine ⟨1301282605280666481619331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3470086947415110617651549 1301282605280666481619331)
              ·
                refine ⟨1951923907920999722428997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301282605280666481619331 1951923907920999722428997)
                ·
                  refine ⟨365985732735187447955437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951923907920999722428997 365985732735187447955437)
                  ·
                    rfl

theorem cell21_1603698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1603698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603698 prefixEnd_1603698 := by exact prefixLift 1603698
  have htrace : WordTrace (prefixWord ++ tailWord_1603698) baseStart_1603698 baseEnd_1603698 := by
    simpa [prefixWord, tailWord_1603698, baseEnd_1603698] using wordTrace_append hprefix tailTrace_1603698
  have hstable : (prefixWord ++ tailWord_1603698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603698).length < 2 ^ (prefixWord ++ tailWord_1603698).sum := by decide
  have hdescent : baseEnd_1603698 < baseStart_1603698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603740 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1603740 : Nat := 118140960795 + 1603740 * 2 ^ 59
def prefixEnd_1603740 : Nat := 4983230072969 + 3 ^ 40 * 1603740 * 2
def baseEnd_1603740 : Nat := 365995317707404708255351

theorem tailTrace_1603740 : CollatzResearch.WordTrace tailWord_1603740 prefixEnd_1603740 365995317707404708255351 := by
  unfold tailWord_1603740
  simp only [CollatzResearch.WordTrace]
  refine ⟨29246601604965675915528337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38995468806620901220704449 29246601604965675915528337)
  ·
    refine ⟨21934951203724256936646253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29246601604965675915528337 21934951203724256936646253)
    ·
      refine ⟨8225606701396596351242345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21934951203724256936646253 8225606701396596351242345)
      ·
        refine ⟨6169205026047447263431759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8225606701396596351242345 6169205026047447263431759)
        ·
          refine ⟨9253807539071170895147639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169205026047447263431759 9253807539071170895147639)
          ·
            refine ⟨13880711308606756342721459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253807539071170895147639 13880711308606756342721459)
            ·
              refine ⟨20821066962910134514082189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13880711308606756342721459 20821066962910134514082189)
              ·
                refine ⟨7807900111091300442780821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20821066962910134514082189 7807900111091300442780821)
                ·
                  refine ⟨365995317707404708255351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7807900111091300442780821 365995317707404708255351)
                  ·
                    rfl

theorem cell21_1603740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1603740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603740 prefixEnd_1603740 := by exact prefixLift 1603740
  have htrace : WordTrace (prefixWord ++ tailWord_1603740) baseStart_1603740 baseEnd_1603740 := by
    simpa [prefixWord, tailWord_1603740, baseEnd_1603740] using wordTrace_append hprefix tailTrace_1603740
  have hstable : (prefixWord ++ tailWord_1603740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603740).length < 2 ^ (prefixWord ++ tailWord_1603740).sum := by decide
  have hdescent : baseEnd_1603740 < baseStart_1603740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603743 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 5]
def baseStart_1603743 : Nat := 118140960795 + 1603743 * 2 ^ 59
def prefixEnd_1603743 : Nat := 4983230072969 + 3 ^ 40 * 1603743 * 2
def baseEnd_1603743 : Nat := 365996002348277369705345

theorem tailTrace_1603743 : CollatzResearch.WordTrace tailWord_1603743 prefixEnd_1603743 365996002348277369705345 := by
  unfold tailWord_1603743
  simp only [CollatzResearch.WordTrace]
  refine ⟨58493312628920483343415883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38995541752613655562277255 58493312628920483343415883)
  ·
    refine ⟨87739968943380725015123825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58493312628920483343415883 87739968943380725015123825)
    ·
      refine ⟨65804976707535543761342869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87739968943380725015123825 65804976707535543761342869)
      ·
        refine ⟨3084608283165728613812947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65804976707535543761342869 3084608283165728613812947)
        ·
          refine ⟨4626912424748592920719421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3084608283165728613812947 4626912424748592920719421)
          ·
            refine ⟨1735092159280722345269783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4626912424748592920719421 1735092159280722345269783)
            ·
              refine ⟨2602638238921083517904675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735092159280722345269783 2602638238921083517904675)
              ·
                refine ⟨3903957358381625276857013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602638238921083517904675 3903957358381625276857013)
                ·
                  refine ⟨365996002348277369705345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3903957358381625276857013 365996002348277369705345)
                  ·
                    rfl

theorem cell21_1603743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 5].length) (baseStart_1603743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603743 prefixEnd_1603743 := by exact prefixLift 1603743
  have htrace : WordTrace (prefixWord ++ tailWord_1603743) baseStart_1603743 baseEnd_1603743 := by
    simpa [prefixWord, tailWord_1603743, baseEnd_1603743] using wordTrace_append hprefix tailTrace_1603743
  have hstable : (prefixWord ++ tailWord_1603743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603743).length < 2 ^ (prefixWord ++ tailWord_1603743).sum := by decide
  have hdescent : baseEnd_1603743 < baseStart_1603743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603788 : List Nat := [2, 2, 1, 6, 2, 8]
def baseStart_1603788 : Nat := 118140960795 + 1603788 * 2 ^ 59
def prefixEnd_1603788 : Nat := 4983230072969 + 3 ^ 40 * 1603788 * 2
def baseEnd_1603788 : Nat := 13555787850421010794639

theorem tailTrace_1603788 : CollatzResearch.WordTrace tailWord_1603788 prefixEnd_1603788 13555787850421010794639 := by
  unfold tailWord_1603788
  simp only [CollatzResearch.WordTrace]
  refine ⟨29247476956878728014402009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38996635942504970685869345 29247476956878728014402009)
  ·
    refine ⟨21935607717659046010801507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29247476956878728014402009 21935607717659046010801507)
    ·
      refine ⟨32903411576488569016202261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21935607717659046010801507 32903411576488569016202261)
      ·
        refine ⟨1542347417647901672634481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32903411576488569016202261 1542347417647901672634481)
        ·
          refine ⟨1156760563235926254475861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1542347417647901672634481 1156760563235926254475861)
          ·
            refine ⟨13555787850421010794639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1156760563235926254475861 13555787850421010794639)
            ·
              rfl

theorem cell21_1603788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 8].length) (baseStart_1603788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603788 prefixEnd_1603788 := by exact prefixLift 1603788
  have htrace : WordTrace (prefixWord ++ tailWord_1603788) baseStart_1603788 baseEnd_1603788 := by
    simpa [prefixWord, tailWord_1603788, baseEnd_1603788] using wordTrace_append hprefix tailTrace_1603788
  have hstable : (prefixWord ++ tailWord_1603788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603788).length < 2 ^ (prefixWord ++ tailWord_1603788).sum := by decide
  have hdescent : baseEnd_1603788 < baseStart_1603788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603861 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 5]
def baseStart_1603861 : Nat := 118140960795 + 1603861 * 2 ^ 59
def prefixEnd_1603861 : Nat := 4983230072969 + 3 ^ 40 * 1603861 * 2
def baseEnd_1603861 : Nat := 366022931555935386738437

theorem tailTrace_1603861 : CollatzResearch.WordTrace tailWord_1603861 prefixEnd_1603861 366022931555935386738437 := by
  unfold tailWord_1603861
  simp only [CollatzResearch.WordTrace]
  refine ⟨58497616442492989496211437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38998410961661992997474291 58497616442492989496211437)
  ·
    refine ⟨21936606165934871061079289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58497616442492989496211437 21936606165934871061079289)
    ·
      refine ⟨16452454624451153295809467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21936606165934871061079289 16452454624451153295809467)
      ·
        refine ⟨24678681936676729943714201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16452454624451153295809467 24678681936676729943714201)
        ·
          refine ⟨18509011452507547457785651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24678681936676729943714201 18509011452507547457785651)
          ·
            refine ⟨27763517178761321186678477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18509011452507547457785651 27763517178761321186678477)
            ·
              refine ⟨10411318942035495445004429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27763517178761321186678477 10411318942035495445004429)
              ·
                refine ⟨3904244603263310791876661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10411318942035495445004429 3904244603263310791876661)
                ·
                  refine ⟨366022931555935386738437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3904244603263310791876661 366022931555935386738437)
                  ·
                    rfl

theorem cell21_1603861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_1603861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603861 prefixEnd_1603861 := by exact prefixLift 1603861
  have htrace : WordTrace (prefixWord ++ tailWord_1603861) baseStart_1603861 baseEnd_1603861 := by
    simpa [prefixWord, tailWord_1603861, baseEnd_1603861] using wordTrace_append hprefix tailTrace_1603861
  have hstable : (prefixWord ++ tailWord_1603861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603861).length < 2 ^ (prefixWord ++ tailWord_1603861).sum := by decide
  have hdescent : baseEnd_1603861 < baseStart_1603861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603951 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 6]
def baseStart_1603951 : Nat := 118140960795 + 1603951 * 2 ^ 59
def prefixEnd_1603951 : Nat := 4983230072969 + 3 ^ 40 * 1603951 * 2
def baseEnd_1603951 : Nat := 366043470782115230238253

theorem tailTrace_1603951 : CollatzResearch.WordTrace tailWord_1603951 prefixEnd_1603951 366043470782115230238253 := by
  unfold tailWord_1603951
  simp only [CollatzResearch.WordTrace]
  refine ⟨58500899012166934866987707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39000599341444623244658471 58500899012166934866987707)
  ·
    refine ⟨87751348518250402300481561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58500899012166934866987707 87751348518250402300481561)
    ·
      refine ⟨65813511388687801725361171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87751348518250402300481561 65813511388687801725361171)
      ·
        refine ⟨98720267083031702588041757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65813511388687801725361171 98720267083031702588041757)
        ·
          refine ⟨37020100156136888470515659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98720267083031702588041757 37020100156136888470515659)
          ·
            refine ⟨55530150234205332705773489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37020100156136888470515659 55530150234205332705773489)
            ·
              refine ⟨41647612675653999529330117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55530150234205332705773489 41647612675653999529330117)
              ·
                refine ⟨7808927376685124911749397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41647612675653999529330117 7808927376685124911749397)
                ·
                  refine ⟨366043470782115230238253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7808927376685124911749397 366043470782115230238253)
                  ·
                    rfl

theorem cell21_1603951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_1603951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603951 prefixEnd_1603951 := by exact prefixLift 1603951
  have htrace : WordTrace (prefixWord ++ tailWord_1603951) baseStart_1603951 baseEnd_1603951 := by
    simpa [prefixWord, tailWord_1603951, baseEnd_1603951] using wordTrace_append hprefix tailTrace_1603951
  have hstable : (prefixWord ++ tailWord_1603951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603951).length < 2 ^ (prefixWord ++ tailWord_1603951).sum := by decide
  have hdescent : baseEnd_1603951 < baseStart_1603951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603971 : List Nat := [1, 1, 1, 3, 6, 1, 1, 4, 3]
def baseStart_1603971 : Nat := 118140960795 + 1603971 * 2 ^ 59
def prefixEnd_1603971 : Nat := 4983230072969 + 3 ^ 40 * 1603971 * 2
def baseEnd_1603971 : Nat := 366048035054599639904879

theorem tailTrace_1603971 : CollatzResearch.WordTrace tailWord_1603971 prefixEnd_1603971 366048035054599639904879 := by
  unfold tailWord_1603971
  simp only [CollatzResearch.WordTrace]
  refine ⟨58501628472094478282715767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39001085648062985521810511 58501628472094478282715767)
  ·
    refine ⟨87752442708141717424073651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58501628472094478282715767 87752442708141717424073651)
    ·
      refine ⟨131628664062212576136110477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87752442708141717424073651 131628664062212576136110477)
      ·
        refine ⟨49360749023329716051041429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131628664062212576136110477 49360749023329716051041429)
        ·
          refine ⟨2313785110468580439892567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49360749023329716051041429 2313785110468580439892567)
          ·
            refine ⟨3470677665702870659838851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313785110468580439892567 3470677665702870659838851)
            ·
              refine ⟨5206016498554305989758277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470677665702870659838851 5206016498554305989758277)
              ·
                refine ⟨976128093478932373079677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5206016498554305989758277 976128093478932373079677)
                ·
                  refine ⟨366048035054599639904879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976128093478932373079677 366048035054599639904879)
                  ·
                    rfl

theorem cell21_1603971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 3].length) (baseStart_1603971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603971 prefixEnd_1603971 := by exact prefixLift 1603971
  have htrace : WordTrace (prefixWord ++ tailWord_1603971) baseStart_1603971 baseEnd_1603971 := by
    simpa [prefixWord, tailWord_1603971, baseEnd_1603971] using wordTrace_append hprefix tailTrace_1603971
  have hstable : (prefixWord ++ tailWord_1603971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603971).length < 2 ^ (prefixWord ++ tailWord_1603971).sum := by decide
  have hdescent : baseEnd_1603971 < baseStart_1603971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603999 : List Nat := [1, 1, 2, 5, 1, 1, 5, 5]
def baseStart_1603999 : Nat := 118140960795 + 1603999 * 2 ^ 59
def prefixEnd_1603999 : Nat := 4983230072969 + 3 ^ 40 * 1603999 * 2
def baseEnd_1603999 : Nat := 122018141678692604479385

theorem tailTrace_1603999 : CollatzResearch.WordTrace tailWord_1603999 prefixEnd_1603999 122018141678692604479385 := by
  unfold tailWord_1603999
  simp only [CollatzResearch.WordTrace]
  refine ⟨58502649715993039064735051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39001766477328692709823367 58502649715993039064735051)
  ·
    refine ⟨87753974573989558597102577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58502649715993039064735051 87753974573989558597102577)
    ·
      refine ⟨65815480930492168947826933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87753974573989558597102577 65815480930492168947826933)
      ·
        refine ⟨6170201337233640838858775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65815480930492168947826933 6170201337233640838858775)
        ·
          refine ⟨9255302005850461258288163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6170201337233640838858775 9255302005850461258288163)
          ·
            refine ⟨13882953008775691887432245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255302005850461258288163 13882953008775691887432245)
            ·
              refine ⟨1301526844572721114446773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13882953008775691887432245 1301526844572721114446773)
              ·
                refine ⟨122018141678692604479385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1301526844572721114446773 122018141678692604479385)
                ·
                  rfl

theorem cell21_1603999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 5].length) (baseStart_1603999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1603999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1603999 prefixEnd_1603999 := by exact prefixLift 1603999
  have htrace : WordTrace (prefixWord ++ tailWord_1603999) baseStart_1603999 baseEnd_1603999 := by
    simpa [prefixWord, tailWord_1603999, baseEnd_1603999] using wordTrace_append hprefix tailTrace_1603999
  have hstable : (prefixWord ++ tailWord_1603999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603999).length < 2 ^ (prefixWord ++ tailWord_1603999).sum := by decide
  have hdescent : baseEnd_1603999 < baseStart_1603999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604050 : List Nat := [3, 2, 2, 4, 2, 1, 2, 5]
def baseStart_1604050 : Nat := 118140960795 + 1604050 * 2 ^ 59
def prefixEnd_1604050 : Nat := 4983230072969 + 3 ^ 40 * 1604050 * 2
def baseEnd_1604050 : Nat := 122022021310304352696017

theorem tailTrace_1604050 : CollatzResearch.WordTrace tailWord_1604050 prefixEnd_1604050 122022021310304352696017 := by
  unfold tailWord_1604050
  simp only [CollatzResearch.WordTrace]
  refine ⟨14626127459702068693710401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39003006559205516516561069 14626127459702068693710401)
  ·
    refine ⟨10969595594776551520282801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14626127459702068693710401 10969595594776551520282801)
    ·
      refine ⟨8227196696082413640212101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10969595594776551520282801 8227196696082413640212101)
      ·
        refine ⟨1542599380515452557539769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8227196696082413640212101 1542599380515452557539769)
        ·
          refine ⟨1156949535386589418154827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1542599380515452557539769 1156949535386589418154827)
          ·
            refine ⟨1735424303079884127232241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156949535386589418154827 1735424303079884127232241)
            ·
              refine ⟨1301568227309913095424181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735424303079884127232241 1301568227309913095424181)
              ·
                refine ⟨122022021310304352696017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1301568227309913095424181 122022021310304352696017)
                ·
                  rfl

theorem cell21_1604050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_1604050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604050 prefixEnd_1604050 := by exact prefixLift 1604050
  have htrace : WordTrace (prefixWord ++ tailWord_1604050) baseStart_1604050 baseEnd_1604050 := by
    simpa [prefixWord, tailWord_1604050, baseEnd_1604050] using wordTrace_append hprefix tailTrace_1604050
  have hstable : (prefixWord ++ tailWord_1604050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604050).length < 2 ^ (prefixWord ++ tailWord_1604050).sum := by decide
  have hdescent : baseEnd_1604050 < baseStart_1604050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604058 : List Nat := [3, 1, 1, 2, 3, 1, 3, 7]
def baseStart_1604058 : Nat := 118140960795 + 1604058 * 2 ^ 59
def prefixEnd_1604058 : Nat := 4983230072969 + 3 ^ 40 * 1604058 * 2
def baseEnd_1604058 : Nat := 122022629879968940651567

theorem tailTrace_1604058 : CollatzResearch.WordTrace tailWord_1604058 prefixEnd_1604058 122022629879968940651567 := by
  unfold tailWord_1604058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14626200405694823035283207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39003201081852861427421885 14626200405694823035283207)
  ·
    refine ⟨21939300608542234552924811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14626200405694823035283207 21939300608542234552924811)
    ·
      refine ⟨32908950912813351829387217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21939300608542234552924811 32908950912813351829387217)
      ·
        refine ⟨24681713184610013872040413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32908950912813351829387217 24681713184610013872040413)
        ·
          refine ⟨9255642444228755202015155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24681713184610013872040413 9255642444228755202015155)
          ·
            refine ⟨13883463666343132803022733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255642444228755202015155 13883463666343132803022733)
            ·
              refine ⟨5206298874878674801133525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13883463666343132803022733 5206298874878674801133525)
              ·
                refine ⟨122022629879968940651567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5206298874878674801133525 122022629879968940651567)
                ·
                  rfl

theorem cell21_1604058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_1604058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604058 prefixEnd_1604058 := by exact prefixLift 1604058
  have htrace : WordTrace (prefixWord ++ tailWord_1604058) baseStart_1604058 baseEnd_1604058 := by
    simpa [prefixWord, tailWord_1604058, baseEnd_1604058] using wordTrace_append hprefix tailTrace_1604058
  have hstable : (prefixWord ++ tailWord_1604058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604058).length < 2 ^ (prefixWord ++ tailWord_1604058).sum := by decide
  have hdescent : baseEnd_1604058 < baseStart_1604058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604089 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 5]
def baseStart_1604089 : Nat := 118140960795 + 1604089 * 2 ^ 59
def prefixEnd_1604089 : Nat := 4983230072969 + 3 ^ 40 * 1604089 * 2
def baseEnd_1604089 : Nat := 366074964262257656937971

theorem tailTrace_1604089 : CollatzResearch.WordTrace tailWord_1604089 prefixEnd_1604089 366074964262257656937971 := by
  unfold tailWord_1604089
  simp only [CollatzResearch.WordTrace]
  refine ⟨58505932285666984435511321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39003954857111322957007547 58505932285666984435511321)
  ·
    refine ⟨43879449214250238326633491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58505932285666984435511321 43879449214250238326633491)
    ·
      refine ⟨65819173821375357489950237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43879449214250238326633491 65819173821375357489950237)
      ·
        refine ⟨24682190183015759058731339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65819173821375357489950237 24682190183015759058731339)
        ·
          refine ⟨37023285274523638588097009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24682190183015759058731339 37023285274523638588097009)
          ·
            refine ⟨27767463955892728941072757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37023285274523638588097009 27767463955892728941072757)
            ·
              refine ⟨2603199745864943338225571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27767463955892728941072757 2603199745864943338225571)
              ·
                refine ⟨3904799618797415007338357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603199745864943338225571 3904799618797415007338357)
                ·
                  refine ⟨366074964262257656937971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3904799618797415007338357 366074964262257656937971)
                  ·
                    rfl

theorem cell21_1604089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_1604089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604089 prefixEnd_1604089 := by exact prefixLift 1604089
  have htrace : WordTrace (prefixWord ++ tailWord_1604089) baseStart_1604089 baseEnd_1604089 := by
    simpa [prefixWord, tailWord_1604089, baseEnd_1604089] using wordTrace_append hprefix tailTrace_1604089
  have hstable : (prefixWord ++ tailWord_1604089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604089).length < 2 ^ (prefixWord ++ tailWord_1604089).sum := by decide
  have hdescent : baseEnd_1604089 < baseStart_1604089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604165 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 5]
def baseStart_1604165 : Nat := 118140960795 + 1604165 * 2 ^ 59
def prefixEnd_1604165 : Nat := 4983230072969 + 3 ^ 40 * 1604165 * 2
def baseEnd_1604165 : Nat := 366092308497698413671149

theorem tailTrace_1604165 : CollatzResearch.WordTrace tailWord_1604165 prefixEnd_1604165 366092308497698413671149 := by
  unfold tailWord_1604165
  simp only [CollatzResearch.WordTrace]
  refine ⟨58508704233391649415277949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39005802822261099610185299 58508704233391649415277949)
  ·
    refine ⟨21940764087521868530729231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58508704233391649415277949 21940764087521868530729231)
    ·
      refine ⟨32911146131282802796093847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21940764087521868530729231 32911146131282802796093847)
      ·
        refine ⟨49366719196924204194140771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32911146131282802796093847 49366719196924204194140771)
        ·
          refine ⟨74050078795386306291211157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49366719196924204194140771 74050078795386306291211157)
          ·
            refine ⟨3471097443533733107400523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74050078795386306291211157 3471097443533733107400523)
            ·
              refine ⟨5206646165300599661100785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3471097443533733107400523 5206646165300599661100785)
              ·
                refine ⟨3904984623975449745825589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5206646165300599661100785 3904984623975449745825589)
                ·
                  refine ⟨366092308497698413671149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3904984623975449745825589 366092308497698413671149)
                  ·
                    rfl

theorem cell21_1604165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_1604165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604165 prefixEnd_1604165 := by exact prefixLift 1604165
  have htrace : WordTrace (prefixWord ++ tailWord_1604165) baseStart_1604165 baseEnd_1604165 := by
    simpa [prefixWord, tailWord_1604165, baseEnd_1604165] using wordTrace_append hprefix tailTrace_1604165
  have hstable : (prefixWord ++ tailWord_1604165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604165).length < 2 ^ (prefixWord ++ tailWord_1604165).sum := by decide
  have hdescent : baseEnd_1604165 < baseStart_1604165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604286 : List Nat := [4, 2, 1, 1, 2, 1, 1, 9]
def baseStart_1604286 : Nat := 118140960795 + 1604286 * 2 ^ 59
def prefixEnd_1604286 : Nat := 4983230072969 + 3 ^ 40 * 1604286 * 2
def baseEnd_1604286 : Nat := 122039974115409697384745

theorem tailTrace_1604286 : CollatzResearch.WordTrace tailWord_1604286 prefixEnd_1604286 122039974115409697384745 := by
  unfold tailWord_1604286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314139683244160885054089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39008744977302191386955141 7314139683244160885054089)
  ·
    refine ⟨5485604762433120663790567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7314139683244160885054089 5485604762433120663790567)
    ·
      refine ⟨8228407143649680995685851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5485604762433120663790567 8228407143649680995685851)
      ·
        refine ⟨12342610715474521493528777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8228407143649680995685851 12342610715474521493528777)
        ·
          refine ⟨9256958036605891120146583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12342610715474521493528777 9256958036605891120146583)
          ·
            refine ⟨13885437054908836680219875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256958036605891120146583 13885437054908836680219875)
            ·
              refine ⟨20828155582363255020329813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13885437054908836680219875 20828155582363255020329813)
              ·
                refine ⟨122039974115409697384745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20828155582363255020329813 122039974115409697384745)
                ·
                  rfl

theorem cell21_1604286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_1604286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604286 prefixEnd_1604286 := by exact prefixLift 1604286
  have htrace : WordTrace (prefixWord ++ tailWord_1604286) baseStart_1604286 baseEnd_1604286 := by
    simpa [prefixWord, tailWord_1604286, baseEnd_1604286] using wordTrace_append hprefix tailTrace_1604286
  have hstable : (prefixWord ++ tailWord_1604286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604286).length < 2 ^ (prefixWord ++ tailWord_1604286).sum := by decide
  have hdescent : baseEnd_1604286 < baseStart_1604286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604309 : List Nat := [1, 3, 2, 5, 1, 2, 2, 2, 3]
def baseStart_1604309 : Nat := 118140960795 + 1604309 * 2 ^ 59
def prefixEnd_1604309 : Nat := 4983230072969 + 3 ^ 40 * 1604309 * 2
def baseEnd_1604309 : Nat := 366125171259586163270855

theorem tailTrace_1604309 : CollatzResearch.WordTrace tailWord_1604309 prefixEnd_1604309 366125171259586163270855 := by
  unfold tailWord_1604309
  simp only [CollatzResearch.WordTrace]
  refine ⟨58513956344869962008519981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39009304229913308005679987 58513956344869962008519981)
  ·
    refine ⟨21942733629326235753194993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58513956344869962008519981 21942733629326235753194993)
    ·
      refine ⟨16457050221994676814896245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21942733629326235753194993 16457050221994676814896245)
      ·
        refine ⟨1542848458312000951396523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16457050221994676814896245 1542848458312000951396523)
        ·
          refine ⟨2314272687468001427094785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542848458312000951396523 2314272687468001427094785)
          ·
            refine ⟨1735704515601001070321089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2314272687468001427094785 1735704515601001070321089)
            ·
              refine ⟨1301778386700750802740817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735704515601001070321089 1301778386700750802740817)
              ·
                refine ⟨976333790025563102055613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301778386700750802740817 976333790025563102055613)
                ·
                  refine ⟨366125171259586163270855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976333790025563102055613 366125171259586163270855)
                  ·
                    rfl

theorem cell21_1604309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_1604309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604309 prefixEnd_1604309 := by exact prefixLift 1604309
  have htrace : WordTrace (prefixWord ++ tailWord_1604309) baseStart_1604309 baseEnd_1604309 := by
    simpa [prefixWord, tailWord_1604309, baseEnd_1604309] using wordTrace_append hprefix tailTrace_1604309
  have hstable : (prefixWord ++ tailWord_1604309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604309).length < 2 ^ (prefixWord ++ tailWord_1604309).sum := by decide
  have hdescent : baseEnd_1604309 < baseStart_1604309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604345 : List Nat := [1, 2, 1, 3, 1, 1, 1, 11]
def baseStart_1604345 : Nat := 118140960795 + 1604345 * 2 ^ 59
def prefixEnd_1604345 : Nat := 4983230072969 + 3 ^ 40 * 1604345 * 2
def baseEnd_1604345 : Nat := 122044462316686033556927

theorem tailTrace_1604345 : CollatzResearch.WordTrace tailWord_1604345 prefixEnd_1604345 122044462316686033556927 := by
  unfold tailWord_1604345
  simp only [CollatzResearch.WordTrace]
  refine ⟨58515269372739540156830489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39010179581826360104553659 58515269372739540156830489)
  ·
    refine ⟨43886452029554655117622867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58515269372739540156830489 43886452029554655117622867)
    ·
      refine ⟨65829678044331982676434301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43886452029554655117622867 65829678044331982676434301)
      ·
        refine ⟨24686129266624493503662863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65829678044331982676434301 24686129266624493503662863)
        ·
          refine ⟨37029193899936740255494295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24686129266624493503662863 37029193899936740255494295)
          ·
            refine ⟨55543790849905110383241443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37029193899936740255494295 55543790849905110383241443)
            ·
              refine ⟨83315686274857665574862165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55543790849905110383241443 83315686274857665574862165)
              ·
                refine ⟨122044462316686033556927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 83315686274857665574862165 122044462316686033556927)
                ·
                  rfl

theorem cell21_1604345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 11].length) (baseStart_1604345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604345 prefixEnd_1604345 := by exact prefixLift 1604345
  have htrace : WordTrace (prefixWord ++ tailWord_1604345) baseStart_1604345 baseEnd_1604345 := by
    simpa [prefixWord, tailWord_1604345, baseEnd_1604345] using wordTrace_append hprefix tailTrace_1604345
  have hstable : (prefixWord ++ tailWord_1604345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604345).length < 2 ^ (prefixWord ++ tailWord_1604345).sum := by decide
  have hdescent : baseEnd_1604345 < baseStart_1604345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604441 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 4]
def baseStart_1604441 : Nat := 118140960795 + 1604441 * 2 ^ 59
def prefixEnd_1604441 : Nat := 4983230072969 + 3 ^ 40 * 1604441 * 2
def baseEnd_1604441 : Nat := 366155295457983267070585

theorem tailTrace_1604441 : CollatzResearch.WordTrace tailWord_1604441 prefixEnd_1604441 366155295457983267070585 := by
  unfold tailWord_1604441
  simp only [CollatzResearch.WordTrace]
  refine ⟨58518770780391748552325177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39012513853594499034883451 58518770780391748552325177)
  ·
    refine ⟨43889078085293811414243883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58518770780391748552325177 43889078085293811414243883)
    ·
      refine ⟨65833617127940717121365825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43889078085293811414243883 65833617127940717121365825)
      ·
        refine ⟨49375212845955537841024369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65833617127940717121365825 49375212845955537841024369)
        ·
          refine ⟨37031409634466653380768277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49375212845955537841024369 37031409634466653380768277)
          ·
            refine ⟨1735847326615624377223513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37031409634466653380768277 1735847326615624377223513)
            ·
              refine ⟨1301885494961718282917635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735847326615624377223513 1301885494961718282917635)
              ·
                refine ⟨1952828242442577424376453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301885494961718282917635 1952828242442577424376453)
                ·
                  refine ⟨366155295457983267070585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1952828242442577424376453 366155295457983267070585)
                  ·
                    rfl

theorem cell21_1604441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_1604441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604441 prefixEnd_1604441 := by exact prefixLift 1604441
  have htrace : WordTrace (prefixWord ++ tailWord_1604441) baseStart_1604441 baseEnd_1604441 := by
    simpa [prefixWord, tailWord_1604441, baseEnd_1604441] using wordTrace_append hprefix tailTrace_1604441
  have hstable : (prefixWord ++ tailWord_1604441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604441).length < 2 ^ (prefixWord ++ tailWord_1604441).sum := by decide
  have hdescent : baseEnd_1604441 < baseStart_1604441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604478 : List Nat := [4, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_1604478 : Nat := 118140960795 + 1604478 * 2 ^ 59
def prefixEnd_1604478 : Nat := 4983230072969 + 3 ^ 40 * 1604478 * 2
def baseEnd_1604478 : Nat := 366163739362079424953843

theorem tailTrace_1604478 : CollatzResearch.WordTrace tailWord_1604478 prefixEnd_1604478 366163739362079424953843 := by
  unfold tailWord_1604478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315015035157212983927761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39013413520838469247614725 7315015035157212983927761)
  ·
    refine ⟨5486261276367909737945821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7315015035157212983927761 5486261276367909737945821)
    ·
      refine ⟨2057347978637966151729683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5486261276367909737945821 2057347978637966151729683)
      ·
        refine ⟨3086021967956949227594525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057347978637966151729683 3086021967956949227594525)
        ·
          refine ⟨1157258237983855960347947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3086021967956949227594525 1157258237983855960347947)
          ·
            refine ⟨1735887356975783940521921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157258237983855960347947 1735887356975783940521921)
            ·
              refine ⟨1301915517731837955391441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735887356975783940521921 1301915517731837955391441)
              ·
                refine ⟨976436638298878466543581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301915517731837955391441 976436638298878466543581)
                ·
                  refine ⟨366163739362079424953843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976436638298878466543581 366163739362079424953843)
                  ·
                    rfl

theorem cell21_1604478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_1604478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604478 prefixEnd_1604478 := by exact prefixLift 1604478
  have htrace : WordTrace (prefixWord ++ tailWord_1604478) baseStart_1604478 baseEnd_1604478 := by
    simpa [prefixWord, tailWord_1604478, baseEnd_1604478] using wordTrace_append hprefix tailTrace_1604478
  have hstable : (prefixWord ++ tailWord_1604478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604478).length < 2 ^ (prefixWord ++ tailWord_1604478).sum := by decide
  have hdescent : baseEnd_1604478 < baseStart_1604478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604500 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1604500 : Nat := 118140960795 + 1604500 * 2 ^ 59
def prefixEnd_1604500 : Nat := 4983230072969 + 3 ^ 40 * 1604500 * 2
def baseEnd_1604500 : Nat := 366168760061812275587131

theorem tailTrace_1604500 : CollatzResearch.WordTrace tailWord_1604500 prefixEnd_1604500 366168760061812275587131 := by
  unfold tailWord_1604500
  simp only [CollatzResearch.WordTrace]
  refine ⟨29260461343589000814361477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39013948458118667752481969 29260461343589000814361477)
  ·
    refine ⟨5486336501922937652692777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29260461343589000814361477 5486336501922937652692777)
    ·
      refine ⟨4114752376442203239519583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5486336501922937652692777 4114752376442203239519583)
      ·
        refine ⟨6172128564663304859279375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114752376442203239519583 6172128564663304859279375)
        ·
          refine ⟨9258192846994957288919063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6172128564663304859279375 9258192846994957288919063)
          ·
            refine ⟨13887289270492435933378595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9258192846994957288919063 13887289270492435933378595)
            ·
              refine ⟨20830933905738653900067893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13887289270492435933378595 20830933905738653900067893)
              ·
                refine ⟨1952900053662998803131365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20830933905738653900067893 1952900053662998803131365)
                ·
                  refine ⟨366168760061812275587131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1952900053662998803131365 366168760061812275587131)
                  ·
                    rfl

theorem cell21_1604500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1604500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604500 prefixEnd_1604500 := by exact prefixLift 1604500
  have htrace : WordTrace (prefixWord ++ tailWord_1604500) baseStart_1604500 baseEnd_1604500 := by
    simpa [prefixWord, tailWord_1604500, baseEnd_1604500] using wordTrace_append hprefix tailTrace_1604500
  have hstable : (prefixWord ++ tailWord_1604500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604500).length < 2 ^ (prefixWord ++ tailWord_1604500).sum := by decide
  have hdescent : baseEnd_1604500 < baseStart_1604500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604610 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1604610 : Nat := 118140960795 + 1604610 * 2 ^ 59
def prefixEnd_1604610 : Nat := 4983230072969 + 3 ^ 40 * 1604610 * 2
def baseEnd_1604610 : Nat := 366193863560476528753573

theorem tailTrace_1604610 : CollatzResearch.WordTrace tailWord_1604610 prefixEnd_1604610 366193863560476528753573 := by
  unfold tailWord_1604610
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631233679194872603806821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39016623144519660276818189 14631233679194872603806821)
  ·
    refine ⟨2743356314849038613213779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14631233679194872603806821 2743356314849038613213779)
    ·
      refine ⟨4115034472273557919820669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2743356314849038613213779 4115034472273557919820669)
      ·
        refine ⟨1543137927102584219932751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4115034472273557919820669 1543137927102584219932751)
        ·
          refine ⟨2314706890653876329899127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543137927102584219932751 2314706890653876329899127)
          ·
            refine ⟨3472060335980814494848691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314706890653876329899127 3472060335980814494848691)
            ·
              refine ⟨5208090503971221742273037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472060335980814494848691 5208090503971221742273037)
              ·
                refine ⟨1953033938989208153352389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5208090503971221742273037 1953033938989208153352389)
                ·
                  refine ⟨366193863560476528753573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953033938989208153352389 366193863560476528753573)
                  ·
                    rfl

theorem cell21_1604610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1604610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604610 prefixEnd_1604610 := by exact prefixLift 1604610
  have htrace : WordTrace (prefixWord ++ tailWord_1604610) baseStart_1604610 baseEnd_1604610 := by
    simpa [prefixWord, tailWord_1604610, baseEnd_1604610] using wordTrace_append hprefix tailTrace_1604610
  have hstable : (prefixWord ++ tailWord_1604610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604610).length < 2 ^ (prefixWord ++ tailWord_1604610).sum := by decide
  have hdescent : baseEnd_1604610 < baseStart_1604610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604680 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_1604680 : Nat := 118140960795 + 1604680 * 2 ^ 59
def prefixEnd_1604680 : Nat := 4983230072969 + 3 ^ 40 * 1604680 * 2
def baseEnd_1604680 : Nat := 366209838514171962586763

theorem tailTrace_1604680 : CollatzResearch.WordTrace tailWord_1604680 prefixEnd_1604680 366209838514171962586763 := by
  unfold tailWord_1604680
  simp only [CollatzResearch.WordTrace]
  refine ⟨29263743913262946185137747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39018325217683928246850329 29263743913262946185137747)
  ·
    refine ⟨43895615869894419277706621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29263743913262946185137747 43895615869894419277706621)
    ·
      refine ⟨16460855951210407229139983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43895615869894419277706621 16460855951210407229139983)
      ·
        refine ⟨24691283926815610843709975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16460855951210407229139983 24691283926815610843709975)
        ·
          refine ⟨37036925890223416265564963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24691283926815610843709975 37036925890223416265564963)
          ·
            refine ⟨55555388835335124398347445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37036925890223416265564963 55555388835335124398347445)
            ·
              refine ⟨5208317703312667912345073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55555388835335124398347445 5208317703312667912345073)
              ·
                refine ⟨3906238277484500934258805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5208317703312667912345073 3906238277484500934258805)
                ·
                  refine ⟨366209838514171962586763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3906238277484500934258805 366209838514171962586763)
                  ·
                    rfl

theorem cell21_1604680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_1604680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604680 prefixEnd_1604680 := by exact prefixLift 1604680
  have htrace : WordTrace (prefixWord ++ tailWord_1604680) baseStart_1604680 baseEnd_1604680 := by
    simpa [prefixWord, tailWord_1604680, baseEnd_1604680] using wordTrace_append hprefix tailTrace_1604680
  have hstable : (prefixWord ++ tailWord_1604680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604680).length < 2 ^ (prefixWord ++ tailWord_1604680).sum := by decide
  have hdescent : baseEnd_1604680 < baseStart_1604680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604711 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 6]
def baseStart_1604711 : Nat := 118140960795 + 1604711 * 2 ^ 59
def prefixEnd_1604711 : Nat := 4983230072969 + 3 ^ 40 * 1604711 * 2
def baseEnd_1604711 : Nat := 366216913136522797570033

theorem tailTrace_1604711 : CollatzResearch.WordTrace tailWord_1604711 prefixEnd_1604711 366216913136522797570033 := by
  unfold tailWord_1604711
  simp only [CollatzResearch.WordTrace]
  refine ⟨58528618489413584664653987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39019078992942389776435991 58528618489413584664653987)
  ·
    refine ⟨87792927734120376996980981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58528618489413584664653987 87792927734120376996980981)
    ·
      refine ⟨8230586975073785343466967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87792927734120376996980981 8230586975073785343466967)
      ·
        refine ⟨12345880462610678015200451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8230586975073785343466967 12345880462610678015200451)
        ·
          refine ⟨18518820693916017022800677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12345880462610678015200451 18518820693916017022800677)
          ·
            refine ⟨3472278880109253191775127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18518820693916017022800677 3472278880109253191775127)
            ·
              refine ⟨5208418320163879787662691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472278880109253191775127 5208418320163879787662691)
              ·
                refine ⟨7812627480245819681494037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208418320163879787662691 7812627480245819681494037)
                ·
                  refine ⟨366216913136522797570033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7812627480245819681494037 366216913136522797570033)
                  ·
                    rfl

theorem cell21_1604711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_1604711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604711 prefixEnd_1604711 := by exact prefixLift 1604711
  have htrace : WordTrace (prefixWord ++ tailWord_1604711) baseStart_1604711 baseEnd_1604711 := by
    simpa [prefixWord, tailWord_1604711, baseEnd_1604711] using wordTrace_append hprefix tailTrace_1604711
  have hstable : (prefixWord ++ tailWord_1604711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604711).length < 2 ^ (prefixWord ++ tailWord_1604711).sum := by decide
  have hdescent : baseEnd_1604711 < baseStart_1604711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604714 : List Nat := [3, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_1604714 : Nat := 118140960795 + 1604714 * 2 ^ 59
def prefixEnd_1604714 : Nat := 4983230072969 + 3 ^ 40 * 1604714 * 2
def baseEnd_1604714 : Nat := 366217597777395459020027

theorem tailTrace_1604714 : CollatzResearch.WordTrace tailWord_1604714 prefixEnd_1604714 366217597777395459020027 := by
  unfold tailWord_1604714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632181977100679044253299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39019151938935144118008797 14632181977100679044253299)
  ·
    refine ⟨21948272965651018566379949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14632181977100679044253299 21948272965651018566379949)
    ·
      refine ⟨8230602362119131962392481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21948272965651018566379949 8230602362119131962392481)
      ·
        refine ⟨6172951771589348971794361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8230602362119131962392481 6172951771589348971794361)
        ·
          refine ⟨4629713828692011728845771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6172951771589348971794361 4629713828692011728845771)
          ·
            refine ⟨6944570743038017593268657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629713828692011728845771 6944570743038017593268657)
            ·
              refine ⟨5208428057278513194951493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6944570743038017593268657 5208428057278513194951493)
              ·
                refine ⟨976580260739721224053405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5208428057278513194951493 976580260739721224053405)
                ·
                  refine ⟨366217597777395459020027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976580260739721224053405 366217597777395459020027)
                  ·
                    rfl

theorem cell21_1604714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_1604714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604714 prefixEnd_1604714 := by exact prefixLift 1604714
  have htrace : WordTrace (prefixWord ++ tailWord_1604714) baseStart_1604714 baseEnd_1604714 := by
    simpa [prefixWord, tailWord_1604714, baseEnd_1604714] using wordTrace_append hprefix tailTrace_1604714
  have hstable : (prefixWord ++ tailWord_1604714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604714).length < 2 ^ (prefixWord ++ tailWord_1604714).sum := by decide
  have hdescent : baseEnd_1604714 < baseStart_1604714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604734 : List Nat := [4, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1604734 : Nat := 118140960795 + 1604734 * 2 ^ 59
def prefixEnd_1604734 : Nat := 4983230072969 + 3 ^ 40 * 1604734 * 2
def baseEnd_1604734 : Nat := 122074054016626622895551

theorem tailTrace_1604734 : CollatzResearch.WordTrace tailWord_1604734 prefixEnd_1604734 122074054016626622895551 := by
  unfold tailWord_1604734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316182171041282449092657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39019638245553506395160837 7316182171041282449092657)
  ·
    refine ⟨5487136628280961836819493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7316182171041282449092657 5487136628280961836819493)
    ·
      refine ⟨1028838117802680344403655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5487136628280961836819493 1028838117802680344403655)
      ·
        refine ⟨1543257176704020516605483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028838117802680344403655 1543257176704020516605483)
        ·
          refine ⟨2314885765056030774908225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543257176704020516605483 2314885765056030774908225)
          ·
            refine ⟨1736164323792023081181169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2314885765056030774908225 1736164323792023081181169)
            ·
              refine ⟨1302123242844017310885877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736164323792023081181169 1302123242844017310885877)
              ·
                refine ⟨122074054016626622895551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1302123242844017310885877 122074054016626622895551)
                ·
                  rfl

theorem cell21_1604734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1604734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604734 prefixEnd_1604734 := by exact prefixLift 1604734
  have htrace : WordTrace (prefixWord ++ tailWord_1604734) baseStart_1604734 baseEnd_1604734 := by
    simpa [prefixWord, tailWord_1604734, baseEnd_1604734] using wordTrace_append hprefix tailTrace_1604734
  have hstable : (prefixWord ++ tailWord_1604734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604734).length < 2 ^ (prefixWord ++ tailWord_1604734).sum := by decide
  have hdescent : baseEnd_1604734 < baseStart_1604734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604773 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 5]
def baseStart_1604773 : Nat := 118140960795 + 1604773 * 2 ^ 59
def prefixEnd_1604773 : Nat := 4983230072969 + 3 ^ 40 * 1604773 * 2
def baseEnd_1604773 : Nat := 366231062381224467536573

theorem tailTrace_1604773 : CollatzResearch.WordTrace tailWord_1604773 prefixEnd_1604773 366231062381224467536573 := by
  unfold tailWord_1604773
  simp only [CollatzResearch.WordTrace]
  refine ⟨58530879815188969253410973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39020586543459312835607315 58530879815188969253410973)
  ·
    refine ⟨21949079930695863470029115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58530879815188969253410973 21949079930695863470029115)
    ·
      refine ⟨32923619896043795205043673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21949079930695863470029115 32923619896043795205043673)
      ·
        refine ⟨24692714922032846403782755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32923619896043795205043673 24692714922032846403782755)
        ·
          refine ⟨37039072383049269605674133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24692714922032846403782755 37039072383049269605674133)
          ·
            refine ⟨1736206517955434512765975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37039072383049269605674133 1736206517955434512765975)
            ·
              refine ⟨2604309776933151769148963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736206517955434512765975 2604309776933151769148963)
              ·
                refine ⟨3906464665399727653723445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604309776933151769148963 3906464665399727653723445)
                ·
                  refine ⟨366231062381224467536573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3906464665399727653723445 366231062381224467536573)
                  ·
                    rfl

theorem cell21_1604773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_1604773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604773 prefixEnd_1604773 := by exact prefixLift 1604773
  have htrace : WordTrace (prefixWord ++ tailWord_1604773) baseStart_1604773 baseEnd_1604773 := by
    simpa [prefixWord, tailWord_1604773, baseEnd_1604773] using wordTrace_append hprefix tailTrace_1604773
  have hstable : (prefixWord ++ tailWord_1604773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604773).length < 2 ^ (prefixWord ++ tailWord_1604773).sum := by decide
  have hdescent : baseEnd_1604773 < baseStart_1604773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604815 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 9]
def baseStart_1604815 : Nat := 118140960795 + 1604815 * 2 ^ 59
def prefixEnd_1604815 : Nat := 4983230072969 + 3 ^ 40 * 1604815 * 2
def baseEnd_1604815 : Nat := 366240647353441727836487

theorem tailTrace_1604815 : CollatzResearch.WordTrace tailWord_1604815 prefixEnd_1604815 366240647353441727836487 := by
  unfold tailWord_1604815
  simp only [CollatzResearch.WordTrace]
  refine ⟨58532411681036810426439899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39021607787357873617626599 58532411681036810426439899)
  ·
    refine ⟨87798617521555215639659849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58532411681036810426439899 87798617521555215639659849)
    ·
      refine ⟨65848963141166411729744887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87798617521555215639659849 65848963141166411729744887)
      ·
        refine ⟨98773444711749617594617331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65848963141166411729744887 98773444711749617594617331)
        ·
          refine ⟨148160167067624426391925997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98773444711749617594617331 148160167067624426391925997)
          ·
            refine ⟨55560062650359159896972249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148160167067624426391925997 55560062650359159896972249)
            ·
              refine ⟨41670046987769369922729187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55560062650359159896972249 41670046987769369922729187)
              ·
                refine ⟨62505070481654054884093781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41670046987769369922729187 62505070481654054884093781)
                ·
                  refine ⟨366240647353441727836487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62505070481654054884093781 366240647353441727836487)
                  ·
                    rfl

theorem cell21_1604815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_1604815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604815 prefixEnd_1604815 := by exact prefixLift 1604815
  have htrace : WordTrace (prefixWord ++ tailWord_1604815) baseStart_1604815 baseEnd_1604815 := by
    simpa [prefixWord, tailWord_1604815, baseEnd_1604815] using wordTrace_append hprefix tailTrace_1604815
  have hstable : (prefixWord ++ tailWord_1604815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604815).length < 2 ^ (prefixWord ++ tailWord_1604815).sum := by decide
  have hdescent : baseEnd_1604815 < baseStart_1604815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604824 : List Nat := [2, 1, 2, 2, 6, 1, 2, 2, 3]
def baseStart_1604824 : Nat := 118140960795 + 1604824 * 2 ^ 59
def prefixEnd_1604824 : Nat := 4983230072969 + 3 ^ 40 * 1604824 * 2
def baseEnd_1604824 : Nat := 366242701276059712186469

theorem tailTrace_1604824 : CollatzResearch.WordTrace tailWord_1604824 prefixEnd_1604824 366242701276059712186469 := by
  unfold tailWord_1604824
  simp only [CollatzResearch.WordTrace]
  refine ⟨29266369969002102481758763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39021826625336136642345017 29266369969002102481758763)
  ·
    refine ⟨43899554953503153722638145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29266369969002102481758763 43899554953503153722638145)
    ·
      refine ⟨32924666215127365291978609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43899554953503153722638145 32924666215127365291978609)
      ·
        refine ⟨24693499661345523968983957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32924666215127365291978609 24693499661345523968983957)
        ·
          refine ⟨1157507796625571436046123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24693499661345523968983957 1157507796625571436046123)
          ·
            refine ⟨1736261694938357154069185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157507796625571436046123 1736261694938357154069185)
            ·
              refine ⟨1302196271203767865551889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736261694938357154069185 1302196271203767865551889)
              ·
                refine ⟨976647203402825899163917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302196271203767865551889 976647203402825899163917)
                ·
                  refine ⟨366242701276059712186469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976647203402825899163917 366242701276059712186469)
                  ·
                    rfl

theorem cell21_1604824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_1604824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604824 prefixEnd_1604824 := by exact prefixLift 1604824
  have htrace : WordTrace (prefixWord ++ tailWord_1604824) baseStart_1604824 baseEnd_1604824 := by
    simpa [prefixWord, tailWord_1604824, baseEnd_1604824] using wordTrace_append hprefix tailTrace_1604824
  have hstable : (prefixWord ++ tailWord_1604824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604824).length < 2 ^ (prefixWord ++ tailWord_1604824).sum := by decide
  have hdescent : baseEnd_1604824 < baseStart_1604824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604922 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1604922 : Nat := 118140960795 + 1604922 * 2 ^ 59
def prefixEnd_1604922 : Nat := 4983230072969 + 3 ^ 40 * 1604922 * 2
def baseEnd_1604922 : Nat := 366265066211233319552935

theorem tailTrace_1604922 : CollatzResearch.WordTrace tailWord_1604922 prefixEnd_1604922 366265066211233319552935 := by
  unfold tailWord_1604922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14634078572912291925146255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39024209527766111800390013 14634078572912291925146255)
  ·
    refine ⟨21951117859368437887719383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14634078572912291925146255 21951117859368437887719383)
    ·
      refine ⟨32926676789052656831579075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21951117859368437887719383 32926676789052656831579075)
      ·
        refine ⟨49390015183578985247368613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32926676789052656831579075 49390015183578985247368613)
        ·
          refine ⟨9260627846921059733881615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49390015183578985247368613 9260627846921059733881615)
          ·
            refine ⟨13890941770381589600822423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260627846921059733881615 13890941770381589600822423)
            ·
              refine ⟨20836412655572384401233635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13890941770381589600822423 20836412655572384401233635)
              ·
                refine ⟨31254618983358576601850453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20836412655572384401233635 31254618983358576601850453)
                ·
                  refine ⟨366265066211233319552935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31254618983358576601850453 366265066211233319552935)
                  ·
                    rfl

theorem cell21_1604922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1604922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604922 prefixEnd_1604922 := by exact prefixLift 1604922
  have htrace : WordTrace (prefixWord ++ tailWord_1604922) baseStart_1604922 baseEnd_1604922 := by
    simpa [prefixWord, tailWord_1604922, baseEnd_1604922] using wordTrace_append hprefix tailTrace_1604922
  have hstable : (prefixWord ++ tailWord_1604922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604922).length < 2 ^ (prefixWord ++ tailWord_1604922).sum := by decide
  have hdescent : baseEnd_1604922 < baseStart_1604922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604942 : List Nat := [4, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_1604942 : Nat := 118140960795 + 1604942 * 2 ^ 59
def prefixEnd_1604942 : Nat := 4983230072969 + 3 ^ 40 * 1604942 * 2
def baseEnd_1604942 : Nat := 366269630483717729219561

theorem tailTrace_1604942 : CollatzResearch.WordTrace tailWord_1604942 prefixEnd_1604942 366269630483717729219561 := by
  unfold tailWord_1604942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317130468947088889539135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39024695834384474077542053 7317130468947088889539135)
  ·
    refine ⟨10975695703420633334308703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7317130468947088889539135 10975695703420633334308703)
    ·
      refine ⟨16463543555130950001463055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10975695703420633334308703 16463543555130950001463055)
      ·
        refine ⟨24695315332696425002194583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16463543555130950001463055 24695315332696425002194583)
        ·
          refine ⟨37042972999044637503291875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24695315332696425002194583 37042972999044637503291875)
          ·
            refine ⟨55564459498566956254937813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37042972999044637503291875 55564459498566956254937813)
            ·
              refine ⟨1302292019497663037225105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55564459498566956254937813 1302292019497663037225105)
              ·
                refine ⟨976719014623247277918829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302292019497663037225105 976719014623247277918829)
                ·
                  refine ⟨366269630483717729219561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976719014623247277918829 366269630483717729219561)
                  ·
                    rfl

theorem cell21_1604942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_1604942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604942 prefixEnd_1604942 := by exact prefixLift 1604942
  have htrace : WordTrace (prefixWord ++ tailWord_1604942) baseStart_1604942 baseEnd_1604942 := by
    simpa [prefixWord, tailWord_1604942, baseEnd_1604942] using wordTrace_append hprefix tailTrace_1604942
  have hstable : (prefixWord ++ tailWord_1604942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604942).length < 2 ^ (prefixWord ++ tailWord_1604942).sum := by decide
  have hdescent : baseEnd_1604942 < baseStart_1604942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604990 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_1604990 : Nat := 118140960795 + 1604990 * 2 ^ 59
def prefixEnd_1604990 : Nat := 4983230072969 + 3 ^ 40 * 1604990 * 2
def baseEnd_1604990 : Nat := 366280584737680312419463

theorem tailTrace_1604990 : CollatzResearch.WordTrace tailWord_1604990 prefixEnd_1604990 366280584737680312419463 := by
  unfold tailWord_1604990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317349306925351914257553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39025862970268543542706949 7317349306925351914257553)
  ·
    refine ⟨5488011980194013935693165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7317349306925351914257553 5488011980194013935693165)
    ·
      refine ⟨2058004492572755225884937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5488011980194013935693165 2058004492572755225884937)
      ·
        refine ⟨1543503369429566419413703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2058004492572755225884937 1543503369429566419413703)
        ·
          refine ⟨2315255054144349629120555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543503369429566419413703 2315255054144349629120555)
          ·
            refine ⟨3472882581216524443680833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315255054144349629120555 3472882581216524443680833)
            ·
              refine ⟨2604661935912393332760625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472882581216524443680833 2604661935912393332760625)
              ·
                refine ⟨1953496451934294999570469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604661935912393332760625 1953496451934294999570469)
                ·
                  refine ⟨366280584737680312419463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953496451934294999570469 366280584737680312419463)
                  ·
                    rfl

theorem cell21_1604990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_1604990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1604990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1604990 prefixEnd_1604990 := by exact prefixLift 1604990
  have htrace : WordTrace (prefixWord ++ tailWord_1604990) baseStart_1604990 baseEnd_1604990 := by
    simpa [prefixWord, tailWord_1604990, baseEnd_1604990] using wordTrace_append hprefix tailTrace_1604990
  have hstable : (prefixWord ++ tailWord_1604990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604990).length < 2 ^ (prefixWord ++ tailWord_1604990).sum := by decide
  have hdescent : baseEnd_1604990 < baseStart_1604990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605049 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 4]
def baseStart_1605049 : Nat := 118140960795 + 1605049 * 2 ^ 59
def prefixEnd_1605049 : Nat := 4983230072969 + 3 ^ 40 * 1605049 * 2
def baseEnd_1605049 : Nat := 366294049341509320936009

theorem tailTrace_1605049 : CollatzResearch.WordTrace tailWord_1605049 prefixEnd_1605049 366294049341509320936009 := by
  unfold tailWord_1605049
  simp only [CollatzResearch.WordTrace]
  refine ⟨58540946362189068390458201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39027297574792712260305467 58540946362189068390458201)
  ·
    refine ⟨43905709771641801292843651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58540946362189068390458201 43905709771641801292843651)
    ·
      refine ⟨65858564657462701939265477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43905709771641801292843651 65858564657462701939265477)
      ·
        refine ⟨12348480873274256613612277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65858564657462701939265477 12348480873274256613612277)
        ·
          refine ⟨1157670081869461557526151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12348480873274256613612277 1157670081869461557526151)
          ·
            refine ⟨1736505122804192336289227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157670081869461557526151 1736505122804192336289227)
            ·
              refine ⟨2604757684206288504433841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736505122804192336289227 2604757684206288504433841)
              ·
                refine ⟨1953568263154716378325381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604757684206288504433841 1953568263154716378325381)
                ·
                  refine ⟨366294049341509320936009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953568263154716378325381 366294049341509320936009)
                  ·
                    rfl

theorem cell21_1605049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_1605049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605049 prefixEnd_1605049 := by exact prefixLift 1605049
  have htrace : WordTrace (prefixWord ++ tailWord_1605049) baseStart_1605049 baseEnd_1605049 := by
    simpa [prefixWord, tailWord_1605049, baseEnd_1605049] using wordTrace_append hprefix tailTrace_1605049
  have hstable : (prefixWord ++ tailWord_1605049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605049).length < 2 ^ (prefixWord ++ tailWord_1605049).sum := by decide
  have hdescent : baseEnd_1605049 < baseStart_1605049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605105 : List Nat := [1, 2, 2, 2, 3, 4, 7]
def baseStart_1605105 : Nat := 118140960795 + 1605105 * 2 ^ 59
def prefixEnd_1605105 : Nat := 4983230072969 + 3 ^ 40 * 1605105 * 2
def baseEnd_1605105 : Nat := 40700758811607296444729

theorem tailTrace_1605105 : CollatzResearch.WordTrace tailWord_1605105 prefixEnd_1605105 40700758811607296444729 := by
  unfold tailWord_1605105
  simp only [CollatzResearch.WordTrace]
  refine ⟨58542988849986189954496769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39028659233324126636331179 58542988849986189954496769)
  ·
    refine ⟨43907241637489642465872577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58542988849986189954496769 43907241637489642465872577)
    ·
      refine ⟨32930431228117231849404433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43907241637489642465872577 32930431228117231849404433)
      ·
        refine ⟨24697823421087923887053325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32930431228117231849404433 24697823421087923887053325)
        ·
          refine ⟨9261683782907971457644997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24697823421087923887053325 9261683782907971457644997)
          ·
            refine ⟨1736565709295244648308437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9261683782907971457644997 1736565709295244648308437)
            ·
              refine ⟨40700758811607296444729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1736565709295244648308437 40700758811607296444729)
              ·
                rfl

theorem cell21_1605105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 7].length) (baseStart_1605105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605105 prefixEnd_1605105 := by exact prefixLift 1605105
  have htrace : WordTrace (prefixWord ++ tailWord_1605105) baseStart_1605105 baseEnd_1605105 := by
    simpa [prefixWord, tailWord_1605105, baseEnd_1605105] using wordTrace_append hprefix tailTrace_1605105
  have hstable : (prefixWord ++ tailWord_1605105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605105).length < 2 ^ (prefixWord ++ tailWord_1605105).sum := by decide
  have hdescent : baseEnd_1605105 < baseStart_1605105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605119 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 5]
def baseStart_1605119 : Nat := 118140960795 + 1605119 * 2 ^ 59
def prefixEnd_1605119 : Nat := 4983230072969 + 3 ^ 40 * 1605119 * 2
def baseEnd_1605119 : Nat := 366310024295204754769199

theorem tailTrace_1605119 : CollatzResearch.WordTrace tailWord_1605119 prefixEnd_1605119 366310024295204754769199 := by
  unfold tailWord_1605119
  simp only [CollatzResearch.WordTrace]
  refine ⟨58543499471935470345506411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39028999647956980230337607 58543499471935470345506411)
  ·
    refine ⟨87815249207903205518259617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58543499471935470345506411 87815249207903205518259617)
    ·
      refine ⟨65861436905927404138694713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87815249207903205518259617 65861436905927404138694713)
      ·
        refine ⟨49396077679445553104021035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65861436905927404138694713 49396077679445553104021035)
        ·
          refine ⟨74094116519168329656031553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49396077679445553104021035 74094116519168329656031553)
          ·
            refine ⟨55570587389376247242023665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74094116519168329656031553 55570587389376247242023665)
            ·
              refine ⟨41677940542032185431517749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55570587389376247242023665 41677940542032185431517749)
              ·
                refine ⟨3907306925815517384204789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41677940542032185431517749 3907306925815517384204789)
                ·
                  refine ⟨366310024295204754769199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3907306925815517384204789 366310024295204754769199)
                  ·
                    rfl

theorem cell21_1605119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_1605119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605119 prefixEnd_1605119 := by exact prefixLift 1605119
  have htrace : WordTrace (prefixWord ++ tailWord_1605119) baseStart_1605119 baseEnd_1605119 := by
    simpa [prefixWord, tailWord_1605119, baseEnd_1605119] using wordTrace_append hprefix tailTrace_1605119
  have hstable : (prefixWord ++ tailWord_1605119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605119).length < 2 ^ (prefixWord ++ tailWord_1605119).sum := by decide
  have hdescent : baseEnd_1605119 < baseStart_1605119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605122 : List Nat := [3, 4, 1, 2, 1, 1, 1, 8]
def baseStart_1605122 : Nat := 118140960795 + 1605122 * 2 ^ 59
def prefixEnd_1605122 : Nat := 4983230072969 + 3 ^ 40 * 1605122 * 2
def baseEnd_1605122 : Nat := 122103569645359138739731

theorem tailTrace_1605122 : CollatzResearch.WordTrace tailWord_1605122 prefixEnd_1605122 122103569645359138739731 := by
  unfold tailWord_1605122
  simp only [CollatzResearch.WordTrace]
  refine ⟨14635902222731150464466405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39029072593949734571910413 14635902222731150464466405)
  ·
    refine ⟨2744231666762090712087451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14635902222731150464466405 2744231666762090712087451)
    ·
      refine ⟨4116347500143136068131177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744231666762090712087451 4116347500143136068131177)
      ·
        refine ⟨3087260625107352051098383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116347500143136068131177 3087260625107352051098383)
        ·
          refine ⟨4630890937661028076647575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087260625107352051098383 4630890937661028076647575)
          ·
            refine ⟨6946336406491542114971363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630890937661028076647575 6946336406491542114971363)
            ·
              refine ⟨10419504609737313172457045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946336406491542114971363 10419504609737313172457045)
              ·
                refine ⟨122103569645359138739731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10419504609737313172457045 122103569645359138739731)
                ·
                  rfl

theorem cell21_1605122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_1605122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605122 prefixEnd_1605122 := by exact prefixLift 1605122
  have htrace : WordTrace (prefixWord ++ tailWord_1605122) baseStart_1605122 baseEnd_1605122 := by
    simpa [prefixWord, tailWord_1605122, baseEnd_1605122] using wordTrace_append hprefix tailTrace_1605122
  have hstable : (prefixWord ++ tailWord_1605122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605122).length < 2 ^ (prefixWord ++ tailWord_1605122).sum := by decide
  have hdescent : baseEnd_1605122 < baseStart_1605122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605229 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1605229 : Nat := 118140960795 + 1605229 * 2 ^ 59
def prefixEnd_1605229 : Nat := 4983230072969 + 3 ^ 40 * 1605229 * 2
def baseEnd_1605229 : Nat := 366335127793869007935641

theorem tailTrace_1605229 : CollatzResearch.WordTrace tailWord_1605229 prefixEnd_1605229 366335127793869007935641 := by
  unfold tailWord_1605229
  simp only [CollatzResearch.WordTrace]
  refine ⟨58547511501536959132010741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39031674334357972754673827 58547511501536959132010741)
  ·
    refine ⟨5488829203269089918626007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58547511501536959132010741 5488829203269089918626007)
    ·
      refine ⟨8233243804903634877939011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488829203269089918626007 8233243804903634877939011)
      ·
        refine ⟨12349865707355452316908517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233243804903634877939011 12349865707355452316908517)
        ·
          refine ⟨2315599820129147309420347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12349865707355452316908517 2315599820129147309420347)
          ·
            refine ⟨3473399730193720964130521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315599820129147309420347 3473399730193720964130521)
            ·
              refine ⟨2605049797645290723097891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3473399730193720964130521 2605049797645290723097891)
              ·
                refine ⟨3907574696467936084646837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605049797645290723097891 3907574696467936084646837)
                ·
                  refine ⟨366335127793869007935641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3907574696467936084646837 366335127793869007935641)
                  ·
                    rfl

theorem cell21_1605229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1605229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605229 prefixEnd_1605229 := by exact prefixLift 1605229
  have htrace : WordTrace (prefixWord ++ tailWord_1605229) baseStart_1605229 baseEnd_1605229 := by
    simpa [prefixWord, tailWord_1605229, baseEnd_1605229] using wordTrace_append hprefix tailTrace_1605229
  have hstable : (prefixWord ++ tailWord_1605229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605229).length < 2 ^ (prefixWord ++ tailWord_1605229).sum := by decide
  have hdescent : baseEnd_1605229 < baseStart_1605229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605243 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 4]
def baseStart_1605243 : Nat := 118140960795 + 1605243 * 2 ^ 59
def prefixEnd_1605243 : Nat := 4983230072969 + 3 ^ 40 * 1605243 * 2
def baseEnd_1605243 : Nat := 366338322784608094702279

theorem tailTrace_1605243 : CollatzResearch.WordTrace tailWord_1605243 prefixEnd_1605243 366338322784608094702279 := by
  unfold tailWord_1605243
  simp only [CollatzResearch.WordTrace]
  refine ⟨58548022123486239523020383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39032014748990826348680255 58548022123486239523020383)
  ·
    refine ⟨87822033185229359284530575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58548022123486239523020383 87822033185229359284530575)
    ·
      refine ⟨131733049777844038926795863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87822033185229359284530575 131733049777844038926795863)
      ·
        refine ⟨197599574666766058390193795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131733049777844038926795863 197599574666766058390193795)
        ·
          refine ⟨296399362000149087585290693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197599574666766058390193795 296399362000149087585290693)
          ·
            refine ⟨55574880375027953922242005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296399362000149087585290693 55574880375027953922242005)
            ·
              refine ⟨1302536258789717670052547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55574880375027953922242005 1302536258789717670052547)
              ·
                refine ⟨1953804388184576505078821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302536258789717670052547 1953804388184576505078821)
                ·
                  refine ⟨366338322784608094702279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953804388184576505078821 366338322784608094702279)
                  ·
                    rfl

theorem cell21_1605243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 4].length) (baseStart_1605243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605243 prefixEnd_1605243 := by exact prefixLift 1605243
  have htrace : WordTrace (prefixWord ++ tailWord_1605243) baseStart_1605243 baseEnd_1605243 := by
    simpa [prefixWord, tailWord_1605243, baseEnd_1605243] using wordTrace_append hprefix tailTrace_1605243
  have hstable : (prefixWord ++ tailWord_1605243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605243).length < 2 ^ (prefixWord ++ tailWord_1605243).sum := by decide
  have hdescent : baseEnd_1605243 < baseStart_1605243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605257 : List Nat := [1, 2, 1, 1, 4, 1, 6, 5]
def baseStart_1605257 : Nat := 118140960795 + 1605257 * 2 ^ 59
def prefixEnd_1605257 : Nat := 4983230072969 + 3 ^ 40 * 1605257 * 2
def baseEnd_1605257 : Nat := 122113839258449060489639

theorem tailTrace_1605257 : CollatzResearch.WordTrace tailWord_1605257 prefixEnd_1605257 122113839258449060489639 := by
  unfold tailWord_1605257
  simp only [CollatzResearch.WordTrace]
  refine ⟨58548532745435519914030025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39032355163623679942686683 58548532745435519914030025)
  ·
    refine ⟨43911399559076639935522519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58548532745435519914030025 43911399559076639935522519)
    ·
      refine ⟨65867099338614959903283779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43911399559076639935522519 65867099338614959903283779)
      ·
        refine ⟨98800649007922439854925669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65867099338614959903283779 98800649007922439854925669)
        ·
          refine ⟨18525121688985457472798563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98800649007922439854925669 18525121688985457472798563)
          ·
            refine ⟨27787682533478186209197845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18525121688985457472798563 27787682533478186209197845)
            ·
              refine ⟨1302547618756789978556149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27787682533478186209197845 1302547618756789978556149)
              ·
                refine ⟨122113839258449060489639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1302547618756789978556149 122113839258449060489639)
                ·
                  rfl

theorem cell21_1605257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 5].length) (baseStart_1605257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605257 prefixEnd_1605257 := by exact prefixLift 1605257
  have htrace : WordTrace (prefixWord ++ tailWord_1605257) baseStart_1605257 baseEnd_1605257 := by
    simpa [prefixWord, tailWord_1605257, baseEnd_1605257] using wordTrace_append hprefix tailTrace_1605257
  have hstable : (prefixWord ++ tailWord_1605257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605257).length < 2 ^ (prefixWord ++ tailWord_1605257).sum := by decide
  have hdescent : baseEnd_1605257 < baseStart_1605257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605294 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1605294 : Nat := 118140960795 + 1605294 * 2 ^ 59
def prefixEnd_1605294 : Nat := 4983230072969 + 3 ^ 40 * 1605294 * 2
def baseEnd_1605294 : Nat := 366349961679443339352175

theorem tailTrace_1605294 : CollatzResearch.WordTrace tailWord_1605294 prefixEnd_1605294 366349961679443339352175 := by
  unfold tailWord_1605294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318735280787684404140867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39033254830867650155417957 7318735280787684404140867)
  ·
    refine ⟨10978102921181526606211301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7318735280787684404140867 10978102921181526606211301)
    ·
      refine ⟨2058394297721536238664619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10978102921181526606211301 2058394297721536238664619)
      ·
        refine ⟨3087591446582304357996929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058394297721536238664619 3087591446582304357996929)
        ·
          refine ⟨2315693584936728268497697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3087591446582304357996929 2315693584936728268497697)
          ·
            refine ⟨1736770188702546201373273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315693584936728268497697 1736770188702546201373273)
            ·
              refine ⟨1302577641526909651029955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736770188702546201373273 1302577641526909651029955)
              ·
                refine ⟨1953866462290364476544933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302577641526909651029955 1953866462290364476544933)
                ·
                  refine ⟨366349961679443339352175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953866462290364476544933 366349961679443339352175)
                  ·
                    rfl

theorem cell21_1605294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1605294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605294 prefixEnd_1605294 := by exact prefixLift 1605294
  have htrace : WordTrace (prefixWord ++ tailWord_1605294) baseStart_1605294 baseEnd_1605294 := by
    simpa [prefixWord, tailWord_1605294, baseEnd_1605294] using wordTrace_append hprefix tailTrace_1605294
  have hstable : (prefixWord ++ tailWord_1605294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605294).length < 2 ^ (prefixWord ++ tailWord_1605294).sum := by decide
  have hdescent : baseEnd_1605294 < baseStart_1605294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605412 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_1605412 : Nat := 118140960795 + 1605412 * 2 ^ 59
def prefixEnd_1605412 : Nat := 4983230072969 + 3 ^ 40 * 1605412 * 2
def baseEnd_1605412 : Nat := 366376890887101356385267

theorem tailTrace_1605412 : CollatzResearch.WordTrace tailWord_1605412 prefixEnd_1605412 366376890887101356385267 := by
  unfold tailWord_1605412
  simp only [CollatzResearch.WordTrace]
  refine ⟨29277093029936990692961245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39036124039915987590614993 29277093029936990692961245)
  ·
    refine ⟨10978909886226371509860467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29277093029936990692961245 10978909886226371509860467)
    ·
      refine ⟨16468364829339557264790701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10978909886226371509860467 16468364829339557264790701)
      ·
        refine ⟨6175636811002333974296513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16468364829339557264790701 6175636811002333974296513)
        ·
          refine ⟨4631727608251750480722385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175636811002333974296513 4631727608251750480722385)
          ·
            refine ⟨3473795706188812860541789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4631727608251750480722385 3473795706188812860541789)
            ·
              refine ⟨1302673389820804822703171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3473795706188812860541789 1302673389820804822703171)
              ·
                refine ⟨1954010084731207234054757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302673389820804822703171 1954010084731207234054757)
                ·
                  refine ⟨366376890887101356385267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954010084731207234054757 366376890887101356385267)
                  ·
                    rfl

theorem cell21_1605412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_1605412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605412 prefixEnd_1605412 := by exact prefixLift 1605412
  have htrace : WordTrace (prefixWord ++ tailWord_1605412) baseStart_1605412 baseEnd_1605412 := by
    simpa [prefixWord, tailWord_1605412, baseEnd_1605412] using wordTrace_append hprefix tailTrace_1605412
  have hstable : (prefixWord ++ tailWord_1605412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605412).length < 2 ^ (prefixWord ++ tailWord_1605412).sum := by decide
  have hdescent : baseEnd_1605412 < baseStart_1605412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605426 : List Nat := [3, 2, 1, 1, 3, 4, 2, 5]
def baseStart_1605426 : Nat := 118140960795 + 1605426 * 2 ^ 59
def prefixEnd_1605426 : Nat := 4983230072969 + 3 ^ 40 * 1605426 * 2
def baseEnd_1605426 : Nat := 122126695292613481050635

theorem tailTrace_1605426 : CollatzResearch.WordTrace tailWord_1605426 prefixEnd_1605426 122126695292613481050635 := by
  unfold tailWord_1605426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638674170455815444233033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39036464454548841184621421 14638674170455815444233033)
  ·
    refine ⟨10979005627841861583174775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14638674170455815444233033 10979005627841861583174775)
    ·
      refine ⟨16468508441762792374762163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10979005627841861583174775 16468508441762792374762163)
      ·
        refine ⟨24702762662644188562143245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16468508441762792374762163 24702762662644188562143245)
        ·
          refine ⟨9263535998491570710803717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24702762662644188562143245 9263535998491570710803717)
          ·
            refine ⟨1736912999717169508275697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9263535998491570710803717 1736912999717169508275697)
            ·
              refine ⟨1302684749787877131206773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736912999717169508275697 1302684749787877131206773)
              ·
                refine ⟨122126695292613481050635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1302684749787877131206773 122126695292613481050635)
                ·
                  rfl

theorem cell21_1605426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_1605426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605426 prefixEnd_1605426 := by exact prefixLift 1605426
  have htrace : WordTrace (prefixWord ++ tailWord_1605426) baseStart_1605426 baseEnd_1605426 := by
    simpa [prefixWord, tailWord_1605426, baseEnd_1605426] using wordTrace_append hprefix tailTrace_1605426
  have hstable : (prefixWord ++ tailWord_1605426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605426).length < 2 ^ (prefixWord ++ tailWord_1605426).sum := by decide
  have hdescent : baseEnd_1605426 < baseStart_1605426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605471 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 4]
def baseStart_1605471 : Nat := 118140960795 + 1605471 * 2 ^ 59
def prefixEnd_1605471 : Nat := 4983230072969 + 3 ^ 40 * 1605471 * 2
def baseEnd_1605471 : Nat := 366390355490930364901813

theorem tailTrace_1605471 : CollatzResearch.WordTrace tailWord_1605471 prefixEnd_1605471 366390355490930364901813 := by
  unfold tailWord_1605471
  simp only [CollatzResearch.WordTrace]
  refine ⟨58556337966660234462320267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39037558644440156308213511 58556337966660234462320267)
  ·
    refine ⟨87834506949990351693480401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58556337966660234462320267 87834506949990351693480401)
    ·
      refine ⟨65875880212492763770110301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87834506949990351693480401 65875880212492763770110301)
      ·
        refine ⟨24703455079684786413791363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65875880212492763770110301 24703455079684786413791363)
        ·
          refine ⟨37055182619527179620687045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24703455079684786413791363 37055182619527179620687045)
          ·
            refine ⟨6947846741161346178878821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37055182619527179620687045 6947846741161346178878821)
            ·
              refine ⟨1302721263967752408539779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6947846741161346178878821 1302721263967752408539779)
              ·
                refine ⟨1954081895951628612809669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302721263967752408539779 1954081895951628612809669)
                ·
                  refine ⟨366390355490930364901813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954081895951628612809669 366390355490930364901813)
                  ·
                    rfl

theorem cell21_1605471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 4].length) (baseStart_1605471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605471 prefixEnd_1605471 := by exact prefixLift 1605471
  have htrace : WordTrace (prefixWord ++ tailWord_1605471) baseStart_1605471 baseEnd_1605471 := by
    simpa [prefixWord, tailWord_1605471, baseEnd_1605471] using wordTrace_append hprefix tailTrace_1605471
  have hstable : (prefixWord ++ tailWord_1605471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605471).length < 2 ^ (prefixWord ++ tailWord_1605471).sum := by decide
  have hdescent : baseEnd_1605471 < baseStart_1605471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605682 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1605682 : Nat := 118140960795 + 1605682 * 2 ^ 59
def prefixEnd_1605682 : Nat := 4983230072969 + 3 ^ 40 * 1605682 * 2
def baseEnd_1605682 : Nat := 366438508565640886884715

theorem tailTrace_1605682 : CollatzResearch.WordTrace tailWord_1605682 prefixEnd_1605682 366438508565640886884715 := by
  unfold tailWord_1605682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641008442223954374562825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39042689179263878332167533 14641008442223954374562825)
  ·
    refine ⟨10980756331667965780922119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14641008442223954374562825 10980756331667965780922119)
    ·
      refine ⟨16471134497501948671383179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10980756331667965780922119 16471134497501948671383179)
      ·
        refine ⟨24706701746252923007074769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16471134497501948671383179 24706701746252923007074769)
        ·
          refine ⟨18530026309689692255306077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24706701746252923007074769 18530026309689692255306077)
          ·
            refine ⟨6948759866133634595739779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18530026309689692255306077 6948759866133634595739779)
            ·
              refine ⟨10423139799200451893609669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6948759866133634595739779 10423139799200451893609669)
              ·
                refine ⟨1954338712350084730051813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10423139799200451893609669 1954338712350084730051813)
                ·
                  refine ⟨366438508565640886884715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954338712350084730051813 366438508565640886884715)
                  ·
                    rfl

theorem cell21_1605682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1605682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605682 prefixEnd_1605682 := by exact prefixLift 1605682
  have htrace : WordTrace (prefixWord ++ tailWord_1605682) baseStart_1605682 baseEnd_1605682 := by
    simpa [prefixWord, tailWord_1605682, baseEnd_1605682] using wordTrace_append hprefix tailTrace_1605682
  have hstable : (prefixWord ++ tailWord_1605682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605682).length < 2 ^ (prefixWord ++ tailWord_1605682).sum := by decide
  have hdescent : baseEnd_1605682 < baseStart_1605682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605685 : List Nat := [1, 3, 3, 1, 1, 1, 6, 2, 3]
def baseStart_1605685 : Nat := 118140960795 + 1605685 * 2 ^ 59
def prefixEnd_1605685 : Nat := 4983230072969 + 3 ^ 40 * 1605685 * 2
def baseEnd_1605685 : Nat := 366439193206513548334709

theorem tailTrace_1605685 : CollatzResearch.WordTrace tailWord_1605685 prefixEnd_1605685 366439193206513548334709 := by
  unfold tailWord_1605685
  simp only [CollatzResearch.WordTrace]
  refine ⟨58564143187884949010610509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39042762125256632673740339 58564143187884949010610509)
  ·
    refine ⟨21961553695456855878978941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58564143187884949010610509 21961553695456855878978941)
    ·
      refine ⟨8235582635796320954617103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21961553695456855878978941 8235582635796320954617103)
      ·
        refine ⟨12353373953694481431925655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8235582635796320954617103 12353373953694481431925655)
        ·
          refine ⟨18530060930541722147888483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12353373953694481431925655 18530060930541722147888483)
          ·
            refine ⟨27795091395812583221832725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18530060930541722147888483 27795091395812583221832725)
            ·
              refine ⟨1302894909178714838523409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27795091395812583221832725 1302894909178714838523409)
              ·
                refine ⟨977171181884036128892557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302894909178714838523409 977171181884036128892557)
                ·
                  refine ⟨366439193206513548334709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977171181884036128892557 366439193206513548334709)
                  ·
                    rfl

theorem cell21_1605685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_1605685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605685 prefixEnd_1605685 := by exact prefixLift 1605685
  have htrace : WordTrace (prefixWord ++ tailWord_1605685) baseStart_1605685 baseEnd_1605685 := by
    simpa [prefixWord, tailWord_1605685, baseEnd_1605685] using wordTrace_append hprefix tailTrace_1605685
  have hstable : (prefixWord ++ tailWord_1605685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605685).length < 2 ^ (prefixWord ++ tailWord_1605685).sum := by decide
  have hdescent : baseEnd_1605685 < baseStart_1605685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605696 : List Nat := [2, 1, 1, 2, 2, 4, 3, 6]
def baseStart_1605696 : Nat := 118140960795 + 1605696 * 2 ^ 59
def prefixEnd_1605696 : Nat := 4983230072969 + 3 ^ 40 * 1605696 * 2
def baseEnd_1605696 : Nat := 122147234518793324550451

theorem tailTrace_1605696 : CollatzResearch.WordTrace tailWord_1605696 prefixEnd_1605696 122147234518793324550451 := by
  unfold tailWord_1605696
  simp only [CollatzResearch.WordTrace]
  refine ⟨29282272195422548944630471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39043029593896731926173961 29282272195422548944630471)
  ·
    refine ⟨43923408293133823416945707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29282272195422548944630471 43923408293133823416945707)
    ·
      refine ⟨65885112439700735125418561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43923408293133823416945707 65885112439700735125418561)
      ·
        refine ⟨49413834329775551344063921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65885112439700735125418561 49413834329775551344063921)
        ·
          refine ⟨37060375747331663508047941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49413834329775551344063921 37060375747331663508047941)
          ·
            refine ⟨6948820452624686907758989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37060375747331663508047941 6948820452624686907758989)
            ·
              refine ⟨2605807669734257590409621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6948820452624686907758989 2605807669734257590409621)
              ·
                refine ⟨122147234518793324550451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2605807669734257590409621 122147234518793324550451)
                ·
                  rfl

theorem cell21_1605696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_1605696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605696 prefixEnd_1605696 := by exact prefixLift 1605696
  have htrace : WordTrace (prefixWord ++ tailWord_1605696) baseStart_1605696 baseEnd_1605696 := by
    simpa [prefixWord, tailWord_1605696, baseEnd_1605696] using wordTrace_append hprefix tailTrace_1605696
  have hstable : (prefixWord ++ tailWord_1605696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605696).length < 2 ^ (prefixWord ++ tailWord_1605696).sum := by decide
  have hdescent : baseEnd_1605696 < baseStart_1605696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605744 : List Nat := [2, 1, 1, 1, 5, 2, 2, 4, 3]
def baseStart_1605744 : Nat := 118140960795 + 1605744 * 2 ^ 59
def prefixEnd_1605744 : Nat := 4983230072969 + 3 ^ 40 * 1605744 * 2
def baseEnd_1605744 : Nat := 366452657810342556851255

theorem tailTrace_1605744 : CollatzResearch.WordTrace tailWord_1605744 prefixEnd_1605744 366452657810342556851255 := by
  unfold tailWord_1605744
  simp only [CollatzResearch.WordTrace]
  refine ⟨29283147547335601043504143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39044196729780801391338857 29283147547335601043504143)
  ·
    refine ⟨43924721321003401565256215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29283147547335601043504143 43924721321003401565256215)
    ·
      refine ⟨65887081981505102347884323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43924721321003401565256215 65887081981505102347884323)
      ·
        refine ⟨98830622972257653521826485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65887081981505102347884323 98830622972257653521826485)
        ·
          refine ⟨9265370903649155017671233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98830622972257653521826485 9265370903649155017671233)
          ·
            refine ⟨6949028177736866263253425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9265370903649155017671233 6949028177736866263253425)
            ·
              refine ⟨5211771133302649697440069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6949028177736866263253425 5211771133302649697440069)
              ·
                refine ⟨977207087494246818270013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5211771133302649697440069 977207087494246818270013)
                ·
                  refine ⟨366452657810342556851255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977207087494246818270013 366452657810342556851255)
                  ·
                    rfl

theorem cell21_1605744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_1605744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605744 prefixEnd_1605744 := by exact prefixLift 1605744
  have htrace : WordTrace (prefixWord ++ tailWord_1605744) baseStart_1605744 baseEnd_1605744 := by
    simpa [prefixWord, tailWord_1605744, baseEnd_1605744] using wordTrace_append hprefix tailTrace_1605744
  have hstable : (prefixWord ++ tailWord_1605744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605744).length < 2 ^ (prefixWord ++ tailWord_1605744).sum := by decide
  have hdescent : baseEnd_1605744 < baseStart_1605744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605809 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 4]
def baseStart_1605809 : Nat := 118140960795 + 1605809 * 2 ^ 59
def prefixEnd_1605809 : Nat := 4983230072969 + 3 ^ 40 * 1605809 * 2
def baseEnd_1605809 : Nat := 366467491695916888267789

theorem tailTrace_1605809 : CollatzResearch.WordTrace tailWord_1605809 prefixEnd_1605809 366467491695916888267789 := by
  unfold tailWord_1605809
  simp only [CollatzResearch.WordTrace]
  refine ⟨58568665839435718188124481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39045777226290478792082987 58568665839435718188124481)
  ·
    refine ⟨43926499379576788641093361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58568665839435718188124481 43926499379576788641093361)
    ·
      refine ⟨32944874534682591480820021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43926499379576788641093361 32944874534682591480820021)
      ·
        refine ⟨3088581987626492951326877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32944874534682591480820021 3088581987626492951326877)
        ·
          refine ⟨1158218245359934856747579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3088581987626492951326877 1158218245359934856747579)
          ·
            refine ⟨1737327368039902285121369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158218245359934856747579 1737327368039902285121369)
            ·
              refine ⟨1302995526029926713841027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737327368039902285121369 1302995526029926713841027)
              ·
                refine ⟨1954493289044890070761541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302995526029926713841027 1954493289044890070761541)
                ·
                  refine ⟨366467491695916888267789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954493289044890070761541 366467491695916888267789)
                  ·
                    rfl

theorem cell21_1605809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_1605809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605809 prefixEnd_1605809 := by exact prefixLift 1605809
  have htrace : WordTrace (prefixWord ++ tailWord_1605809) baseStart_1605809 baseEnd_1605809 := by
    simpa [prefixWord, tailWord_1605809, baseEnd_1605809] using wordTrace_append hprefix tailTrace_1605809
  have hstable : (prefixWord ++ tailWord_1605809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605809).length < 2 ^ (prefixWord ++ tailWord_1605809).sum := by decide
  have hdescent : baseEnd_1605809 < baseStart_1605809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605896 : List Nat := [2, 1, 3, 2, 3, 1, 1, 5, 3]
def baseStart_1605896 : Nat := 118140960795 + 1605896 * 2 ^ 59
def prefixEnd_1605896 : Nat := 4983230072969 + 3 ^ 40 * 1605896 * 2
def baseEnd_1605896 : Nat := 366487346281224070317611

theorem tailTrace_1605896 : CollatzResearch.WordTrace tailWord_1605896 prefixEnd_1605896 366487346281224070317611 := by
  unfold tailWord_1605896
  simp only [CollatzResearch.WordTrace]
  refine ⟨29285919495060266023270771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39047892660080354697694361 29285919495060266023270771)
  ·
    refine ⟨43928879242590399034906157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29285919495060266023270771 43928879242590399034906157)
    ·
      refine ⟨16473329715971399638089809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43928879242590399034906157 16473329715971399638089809)
      ·
        refine ⟨12354997286978549728567357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16473329715971399638089809 12354997286978549728567357)
        ·
          refine ⟨4633123982616956148212759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12354997286978549728567357 4633123982616956148212759)
          ·
            refine ⟨6949685973925434222319139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633123982616956148212759 6949685973925434222319139)
            ·
              refine ⟨10424528960888151333478709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6949685973925434222319139 10424528960888151333478709)
              ·
                refine ⟨977299590083264187513629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10424528960888151333478709 977299590083264187513629)
                ·
                  refine ⟨366487346281224070317611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977299590083264187513629 366487346281224070317611)
                  ·
                    rfl

theorem cell21_1605896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_1605896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605896 prefixEnd_1605896 := by exact prefixLift 1605896
  have htrace : WordTrace (prefixWord ++ tailWord_1605896) baseStart_1605896 baseEnd_1605896 := by
    simpa [prefixWord, tailWord_1605896, baseEnd_1605896] using wordTrace_append hprefix tailTrace_1605896
  have hstable : (prefixWord ++ tailWord_1605896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605896).length < 2 ^ (prefixWord ++ tailWord_1605896).sum := by decide
  have hdescent : baseEnd_1605896 < baseStart_1605896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605969 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 6]
def baseStart_1605969 : Nat := 118140960795 + 1605969 * 2 ^ 59
def prefixEnd_1605969 : Nat := 4983230072969 + 3 ^ 40 * 1605969 * 2
def baseEnd_1605969 : Nat := 366504005875792165600795

theorem tailTrace_1605969 : CollatzResearch.WordTrace tailWord_1605969 prefixEnd_1605969 366504005875792165600795 := by
  unfold tailWord_1605969
  simp only [CollatzResearch.WordTrace]
  refine ⟨58574501518856065513948961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39049667679237377009299307 58574501518856065513948961)
  ·
    refine ⟨43930876139142049135461721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58574501518856065513948961 43930876139142049135461721)
    ·
      refine ⟨32948157104356536851596291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43930876139142049135461721 32948157104356536851596291)
      ·
        refine ⟨49422235656534805277394437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32948157104356536851596291 49422235656534805277394437)
        ·
          refine ⟨9266669185600275989511457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49422235656534805277394437 9266669185600275989511457)
          ·
            refine ⟨6950001889200206992133593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9266669185600275989511457 6950001889200206992133593)
            ·
              refine ⟨5212501416900155244100195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6950001889200206992133593 5212501416900155244100195)
              ·
                refine ⟨7818752125350232866150293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5212501416900155244100195 7818752125350232866150293)
                ·
                  refine ⟨366504005875792165600795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7818752125350232866150293 366504005875792165600795)
                  ·
                    rfl

theorem cell21_1605969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_1605969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605969 prefixEnd_1605969 := by exact prefixLift 1605969
  have htrace : WordTrace (prefixWord ++ tailWord_1605969) baseStart_1605969 baseEnd_1605969 := by
    simpa [prefixWord, tailWord_1605969, baseEnd_1605969] using wordTrace_append hprefix tailTrace_1605969
  have hstable : (prefixWord ++ tailWord_1605969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605969).length < 2 ^ (prefixWord ++ tailWord_1605969).sum := by decide
  have hdescent : baseEnd_1605969 < baseStart_1605969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605972 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1605972 : Nat := 118140960795 + 1605972 * 2 ^ 59
def prefixEnd_1605972 : Nat := 4983230072969 + 3 ^ 40 * 1605972 * 2
def baseEnd_1605972 : Nat := 366504690516664827050789

theorem tailTrace_1605972 : CollatzResearch.WordTrace tailWord_1605972 prefixEnd_1605972 366504690516664827050789 := by
  unfold tailWord_1605972
  simp only [CollatzResearch.WordTrace]
  refine ⟨29287305468922598513154085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39049740625230131350872113 29287305468922598513154085)
  ·
    refine ⟨5491369775422987221216391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29287305468922598513154085 5491369775422987221216391)
    ·
      refine ⟨8237054663134480831824587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5491369775422987221216391 8237054663134480831824587)
      ·
        refine ⟨12355581994701721247736881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8237054663134480831824587 12355581994701721247736881)
        ·
          refine ⟨9266686496026290935802661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12355581994701721247736881 9266686496026290935802661)
          ·
            refine ⟨1737503718004929550462999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9266686496026290935802661 1737503718004929550462999)
            ·
              refine ⟨2606255577007394325694499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737503718004929550462999 2606255577007394325694499)
              ·
                refine ⟨3909383365511091488541749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606255577007394325694499 3909383365511091488541749)
                ·
                  refine ⟨366504690516664827050789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3909383365511091488541749 366504690516664827050789)
                  ·
                    rfl

theorem cell21_1605972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1605972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605972 prefixEnd_1605972 := by exact prefixLift 1605972
  have htrace : WordTrace (prefixWord ++ tailWord_1605972) baseStart_1605972 baseEnd_1605972 := by
    simpa [prefixWord, tailWord_1605972, baseEnd_1605972] using wordTrace_append hprefix tailTrace_1605972
  have hstable : (prefixWord ++ tailWord_1605972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605972).length < 2 ^ (prefixWord ++ tailWord_1605972).sum := by decide
  have hdescent : baseEnd_1605972 < baseStart_1605972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605983 : List Nat := [1, 1, 2, 3, 1, 2, 3, 8]
def baseStart_1605983 : Nat := 118140960795 + 1605983 * 2 ^ 59
def prefixEnd_1605983 : Nat := 4983230072969 + 3 ^ 40 * 1605983 * 2
def baseEnd_1605983 : Nat := 122169066955510417455811

theorem tailTrace_1605983 : CollatzResearch.WordTrace tailWord_1605983 prefixEnd_1605983 122169066955510417455811 := by
  unfold tailWord_1605983
  simp only [CollatzResearch.WordTrace]
  refine ⟨58575012140805345904958603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39050008093870230603305735 58575012140805345904958603)
  ·
    refine ⟨87862518211208018857437905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58575012140805345904958603 87862518211208018857437905)
    ·
      refine ⟨65896888658406014143078429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87862518211208018857437905 65896888658406014143078429)
      ·
        refine ⟨24711333246902255303654411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65896888658406014143078429 24711333246902255303654411)
        ·
          refine ⟨37066999870353382955481617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24711333246902255303654411 37066999870353382955481617)
          ·
            refine ⟨27800249902765037216611213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37066999870353382955481617 27800249902765037216611213)
            ·
              refine ⟨10425093713536888956229205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27800249902765037216611213 10425093713536888956229205)
              ·
                refine ⟨122169066955510417455811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10425093713536888956229205 122169066955510417455811)
                ·
                  rfl

theorem cell21_1605983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_1605983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1605983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1605983 prefixEnd_1605983 := by exact prefixLift 1605983
  have htrace : WordTrace (prefixWord ++ tailWord_1605983) baseStart_1605983 baseEnd_1605983 := by
    simpa [prefixWord, tailWord_1605983, baseEnd_1605983] using wordTrace_append hprefix tailTrace_1605983
  have hstable : (prefixWord ++ tailWord_1605983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605983).length < 2 ^ (prefixWord ++ tailWord_1605983).sum := by decide
  have hdescent : baseEnd_1605983 < baseStart_1605983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606076 : List Nat := [2, 2, 2, 4, 1, 2, 8]
def baseStart_1606076 : Nat := 118140960795 + 1606076 * 2 ^ 59
def prefixEnd_1606076 : Nat := 4983230072969 + 3 ^ 40 * 1606076 * 2
def baseEnd_1606076 : Nat := 40725380525953750813027

theorem tailTrace_1606076 : CollatzResearch.WordTrace tailWord_1606076 prefixEnd_1606076 40725380525953750813027 := by
  unfold tailWord_1606076
  simp only [CollatzResearch.WordTrace]
  refine ⟨29289202064734211394047041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39052269419645615192062721 29289202064734211394047041)
  ·
    refine ⟨21966901548550658545535281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29289202064734211394047041 21966901548550658545535281)
    ·
      refine ⟨16475176161412993909151461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21966901548550658545535281 16475176161412993909151461)
      ·
        refine ⟨3089095530264936357965899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16475176161412993909151461 3089095530264936357965899)
        ·
          refine ⟨4633643295397404536948849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089095530264936357965899 4633643295397404536948849)
          ·
            refine ⟨3475232471548053402711637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4633643295397404536948849 3475232471548053402711637)
            ·
              refine ⟨40725380525953750813027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3475232471548053402711637 40725380525953750813027)
              ·
                rfl

theorem cell21_1606076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 8].length) (baseStart_1606076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606076 prefixEnd_1606076 := by exact prefixLift 1606076
  have htrace : WordTrace (prefixWord ++ tailWord_1606076) baseStart_1606076 baseEnd_1606076 := by
    simpa [prefixWord, tailWord_1606076, baseEnd_1606076] using wordTrace_append hprefix tailTrace_1606076
  have hstable : (prefixWord ++ tailWord_1606076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606076).length < 2 ^ (prefixWord ++ tailWord_1606076).sum := by decide
  have hdescent : baseEnd_1606076 < baseStart_1606076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606155 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 4]
def baseStart_1606155 : Nat := 118140960795 + 1606155 * 2 ^ 59
def prefixEnd_1606155 : Nat := 4983230072969 + 3 ^ 40 * 1606155 * 2
def baseEnd_1606155 : Nat := 366546453609897175500415

theorem tailTrace_1606155 : CollatzResearch.WordTrace tailWord_1606155 prefixEnd_1606155 366546453609897175500415 := by
  unfold tailWord_1606155
  simp only [CollatzResearch.WordTrace]
  refine ⟨58581285496182219280219919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39054190330788146186813279 58581285496182219280219919)
  ·
    refine ⟨87871928244273328920329879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58581285496182219280219919 87871928244273328920329879)
    ·
      refine ⟨131807892366409993380494819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87871928244273328920329879 131807892366409993380494819)
      ·
        refine ⟨197711838549614990070742229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131807892366409993380494819 197711838549614990070742229)
        ·
          refine ⟨4633871216006601329783021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 197711838549614990070742229 4633871216006601329783021)
          ·
            refine ⟨1737701706002475498668633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4633871216006601329783021 1737701706002475498668633)
            ·
              refine ⟨1303276279501856624001475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737701706002475498668633 1303276279501856624001475)
              ·
                refine ⟨1954914419252784936002213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303276279501856624001475 1954914419252784936002213)
                ·
                  refine ⟨366546453609897175500415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954914419252784936002213 366546453609897175500415)
                  ·
                    rfl

theorem cell21_1606155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 4].length) (baseStart_1606155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606155 prefixEnd_1606155 := by exact prefixLift 1606155
  have htrace : WordTrace (prefixWord ++ tailWord_1606155) baseStart_1606155 baseEnd_1606155 := by
    simpa [prefixWord, tailWord_1606155, baseEnd_1606155] using wordTrace_append hprefix tailTrace_1606155
  have hstable : (prefixWord ++ tailWord_1606155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606155).length < 2 ^ (prefixWord ++ tailWord_1606155).sum := by decide
  have hdescent : baseEnd_1606155 < baseStart_1606155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606189 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1606189 : Nat := 118140960795 + 1606189 * 2 ^ 59
def prefixEnd_1606189 : Nat := 4983230072969 + 3 ^ 40 * 1606189 * 2
def baseEnd_1606189 : Nat := 366554212873120671933679

theorem tailTrace_1606189 : CollatzResearch.WordTrace tailWord_1606189 prefixEnd_1606189 366554212873120671933679 := by
  unfold tailWord_1606189
  simp only [CollatzResearch.WordTrace]
  refine ⟨58582525578059043086957621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39055017052039362057971747 58582525578059043086957621)
  ·
    refine ⟨5492111772943035289402277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58582525578059043086957621 5492111772943035289402277)
    ·
      refine ⟨1029770957426819116762927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5492111772943035289402277 1029770957426819116762927)
      ·
        refine ⟨1544656436140228675144391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029770957426819116762927 1544656436140228675144391)
        ·
          refine ⟨2316984654210343012716587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544656436140228675144391 2316984654210343012716587)
          ·
            refine ⟨3475476981315514519074881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316984654210343012716587 3475476981315514519074881)
            ·
              refine ⟨2606607735986635889306161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475476981315514519074881 2606607735986635889306161)
              ·
                refine ⟨1954955801989976916979621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606607735986635889306161 1954955801989976916979621)
                ·
                  refine ⟨366554212873120671933679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954955801989976916979621 366554212873120671933679)
                  ·
                    rfl

theorem cell21_1606189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1606189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606189 prefixEnd_1606189 := by exact prefixLift 1606189
  have htrace : WordTrace (prefixWord ++ tailWord_1606189) baseStart_1606189 baseEnd_1606189 := by
    simpa [prefixWord, tailWord_1606189, baseEnd_1606189] using wordTrace_append hprefix tailTrace_1606189
  have hstable : (prefixWord ++ tailWord_1606189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606189).length < 2 ^ (prefixWord ++ tailWord_1606189).sum := by decide
  have hdescent : baseEnd_1606189 < baseStart_1606189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606248 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 4]
def baseStart_1606248 : Nat := 118140960795 + 1606248 * 2 ^ 59
def prefixEnd_1606248 : Nat := 4983230072969 + 3 ^ 40 * 1606248 * 2
def baseEnd_1606248 : Nat := 366567677476949680450225

theorem tailTrace_1606248 : CollatzResearch.WordTrace tailWord_1606248 prefixEnd_1606248 366567677476949680450225 := by
  unfold tailWord_1606248
  simp only [CollatzResearch.WordTrace]
  refine ⟨29292338742422648081677699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39056451656563530775570265 29292338742422648081677699)
  ·
    refine ⟨43938508113633972122516549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29292338742422648081677699 43938508113633972122516549)
    ·
      refine ⟨8238470271306369772971853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43938508113633972122516549 8238470271306369772971853)
      ·
        refine ⟨3089426351739888664864445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8238470271306369772971853 3089426351739888664864445)
        ·
          refine ⟨1158534881902458249324167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3089426351739888664864445 1158534881902458249324167)
          ·
            refine ⟨1737802322853687373986251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158534881902458249324167 1737802322853687373986251)
            ·
              refine ⟨2606703484280531060979377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737802322853687373986251 2606703484280531060979377)
              ·
                refine ⟨1955027613210398295734533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606703484280531060979377 1955027613210398295734533)
                ·
                  refine ⟨366567677476949680450225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1955027613210398295734533 366567677476949680450225)
                  ·
                    rfl

theorem cell21_1606248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_1606248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606248 prefixEnd_1606248 := by exact prefixLift 1606248
  have htrace : WordTrace (prefixWord ++ tailWord_1606248) baseStart_1606248 baseEnd_1606248 := by
    simpa [prefixWord, tailWord_1606248, baseEnd_1606248] using wordTrace_append hprefix tailTrace_1606248
  have hstable : (prefixWord ++ tailWord_1606248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606248).length < 2 ^ (prefixWord ++ tailWord_1606248).sum := by decide
  have hdescent : baseEnd_1606248 < baseStart_1606248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606304 : List Nat := [2, 1, 1, 4, 4, 2, 7]
def baseStart_1606304 : Nat := 118140960795 + 1606304 * 2 ^ 59
def prefixEnd_1606304 : Nat := 4983230072969 + 3 ^ 40 * 1606304 * 2
def baseEnd_1606304 : Nat := 40731161937767336390753

theorem tailTrace_1606304 : CollatzResearch.WordTrace tailWord_1606304 prefixEnd_1606304 40731161937767336390753 := by
  unfold tailWord_1606304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29293359986321208863696983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39057813315094945151595977 29293359986321208863696983)
  ·
    refine ⟨43940039979481813295545475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29293359986321208863696983 43940039979481813295545475)
    ·
      refine ⟨65910059969222719943318213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43940039979481813295545475 65910059969222719943318213)
      ·
        refine ⟨12358136244229259989372165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65910059969222719943318213 12358136244229259989372165)
        ·
          refine ⟨2317150545792986248007281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12358136244229259989372165 2317150545792986248007281)
          ·
            refine ⟨1737862909344739686005461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2317150545792986248007281 1737862909344739686005461)
            ·
              refine ⟨40731161937767336390753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1737862909344739686005461 40731161937767336390753)
              ·
                rfl

theorem cell21_1606304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 7].length) (baseStart_1606304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606304 prefixEnd_1606304 := by exact prefixLift 1606304
  have htrace : WordTrace (prefixWord ++ tailWord_1606304) baseStart_1606304 baseEnd_1606304 := by
    simpa [prefixWord, tailWord_1606304, baseEnd_1606304] using wordTrace_append hprefix tailTrace_1606304
  have hstable : (prefixWord ++ tailWord_1606304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606304).length < 2 ^ (prefixWord ++ tailWord_1606304).sum := by decide
  have hdescent : baseEnd_1606304 < baseStart_1606304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606321 : List Nat := [1, 2, 2, 6, 1, 1, 2, 6]
def baseStart_1606321 : Nat := 118140960795 + 1606321 * 2 ^ 59
def prefixEnd_1606321 : Nat := 4983230072969 + 3 ^ 40 * 1606321 * 2
def baseEnd_1606321 : Nat := 122194779023839258577803

theorem tailTrace_1606321 : CollatzResearch.WordTrace tailWord_1606321 prefixEnd_1606321 122194779023839258577803 := by
  unfold tailWord_1606321
  simp only [CollatzResearch.WordTrace]
  refine ⟨58587340013580829630762817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39058226675720553087175211 58587340013580829630762817)
  ·
    refine ⟨43940505010185622223072113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58587340013580829630762817 43940505010185622223072113)
    ·
      refine ⟨32955378757639216667304085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43940505010185622223072113 32955378757639216667304085)
      ·
        refine ⟨1544783379264338281279879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32955378757639216667304085 1544783379264338281279879)
        ·
          refine ⟨2317175068896507421919819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544783379264338281279879 2317175068896507421919819)
          ·
            refine ⟨3475762603344761132879729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317175068896507421919819 3475762603344761132879729)
            ·
              refine ⟨2606821952508570849659797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475762603344761132879729 2606821952508570849659797)
              ·
                refine ⟨122194779023839258577803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2606821952508570849659797 122194779023839258577803)
                ·
                  rfl

theorem cell21_1606321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 6].length) (baseStart_1606321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606321 prefixEnd_1606321 := by exact prefixLift 1606321
  have htrace : WordTrace (prefixWord ++ tailWord_1606321) baseStart_1606321 baseEnd_1606321 := by
    simpa [prefixWord, tailWord_1606321, baseEnd_1606321] using wordTrace_append hprefix tailTrace_1606321
  have hstable : (prefixWord ++ tailWord_1606321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606321).length < 2 ^ (prefixWord ++ tailWord_1606321).sum := by decide
  have hdescent : baseEnd_1606321 < baseStart_1606321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606369 : List Nat := [1, 2, 3, 1, 4, 3, 2, 2, 3]
def baseStart_1606369 : Nat := 118140960795 + 1606369 * 2 ^ 59
def prefixEnd_1606369 : Nat := 4983230072969 + 3 ^ 40 * 1606369 * 2
def baseEnd_1606369 : Nat := 366595291325480358933311

theorem tailTrace_1606369 : CollatzResearch.WordTrace tailWord_1606369 prefixEnd_1606369 366595291325480358933311 := by
  unfold tailWord_1606369
  simp only [CollatzResearch.WordTrace]
  refine ⟨58589090717406933828510161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39059393811604622552340107 58589090717406933828510161)
  ·
    refine ⟨43941818038055200371382621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58589090717406933828510161 43941818038055200371382621)
    ·
      refine ⟨16478181764270700139268483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43941818038055200371382621 16478181764270700139268483)
      ·
        refine ⟨24717272646406050208902725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16478181764270700139268483 24717272646406050208902725)
        ·
          refine ⟨4634488621201134414169261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24717272646406050208902725 4634488621201134414169261)
          ·
            refine ⟨1737933232950425405313473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4634488621201134414169261 1737933232950425405313473)
            ·
              refine ⟨1303449924712819053985105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737933232950425405313473 1303449924712819053985105)
              ·
                refine ⟨977587443534614290488829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1303449924712819053985105 977587443534614290488829)
                ·
                  refine ⟨366595291325480358933311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977587443534614290488829 366595291325480358933311)
                  ·
                    rfl

theorem cell21_1606369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_1606369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606369 prefixEnd_1606369 := by exact prefixLift 1606369
  have htrace : WordTrace (prefixWord ++ tailWord_1606369) baseStart_1606369 baseEnd_1606369 := by
    simpa [prefixWord, tailWord_1606369, baseEnd_1606369] using wordTrace_append hprefix tailTrace_1606369
  have hstable : (prefixWord ++ tailWord_1606369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606369).length < 2 ^ (prefixWord ++ tailWord_1606369).sum := by decide
  have hdescent : baseEnd_1606369 < baseStart_1606369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606462 : List Nat := [4, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1606462 : Nat := 118140960795 + 1606462 * 2 ^ 59
def prefixEnd_1606462 : Nat := 4983230072969 + 3 ^ 40 * 1606462 * 2
def baseEnd_1606462 : Nat := 366616515192532863883121

theorem tailTrace_1606462 : CollatzResearch.WordTrace tailWord_1606462 prefixEnd_1606462 366616515192532863883121 := by
  unfold tailWord_1606462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7324060338258751338955705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39061655137380007141097093 7324060338258751338955705)
  ·
    refine ⟨5493045253694063504216779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7324060338258751338955705 5493045253694063504216779)
    ·
      refine ⟨8239567880541095256325169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493045253694063504216779 8239567880541095256325169)
      ·
        refine ⟨6179675910405821442243877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8239567880541095256325169 6179675910405821442243877)
        ·
          refine ⟨1158689233201091520420727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6179675910405821442243877 1158689233201091520420727)
          ·
            refine ⟨1738033849801637280631091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158689233201091520420727 1738033849801637280631091)
            ·
              refine ⟨2607050774702455920946637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738033849801637280631091 2607050774702455920946637)
              ·
                refine ⟨977644040513420970354989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607050774702455920946637 977644040513420970354989)
                ·
                  refine ⟨366616515192532863883121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977644040513420970354989 366616515192532863883121)
                  ·
                    rfl

theorem cell21_1606462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1606462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606462 prefixEnd_1606462 := by exact prefixLift 1606462
  have htrace : WordTrace (prefixWord ++ tailWord_1606462) baseStart_1606462 baseEnd_1606462 := by
    simpa [prefixWord, tailWord_1606462, baseEnd_1606462] using wordTrace_append hprefix tailTrace_1606462
  have hstable : (prefixWord ++ tailWord_1606462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606462).length < 2 ^ (prefixWord ++ tailWord_1606462).sum := by decide
  have hdescent : baseEnd_1606462 < baseStart_1606462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606487 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 5]
def baseStart_1606487 : Nat := 118140960795 + 1606487 * 2 ^ 59
def prefixEnd_1606487 : Nat := 4983230072969 + 3 ^ 40 * 1606487 * 2
def baseEnd_1606487 : Nat := 366622220533138375966403

theorem tailTrace_1606487 : CollatzResearch.WordTrace tailWord_1606487 prefixEnd_1606487 366622220533138375966403 := by
  unfold tailWord_1606487
  simp only [CollatzResearch.WordTrace]
  refine ⟨58593394530979439981305715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39062263020652959987537143 58593394530979439981305715)
  ·
    refine ⟨87890091796469159971958573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58593394530979439981305715 87890091796469159971958573)
    ·
      refine ⟨32958784423675934989484465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87890091796469159971958573 32958784423675934989484465)
      ·
        refine ⟨24719088317756951242113349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32958784423675934989484465 24719088317756951242113349)
        ·
          refine ⟨4634829059579428357896253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24719088317756951242113349 4634829059579428357896253)
          ·
            refine ⟨1738060897342285634211095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4634829059579428357896253 1738060897342285634211095)
            ·
              refine ⟨2607091346013428451316643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738060897342285634211095 2607091346013428451316643)
              ·
                refine ⟨3910637019020142676974965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607091346013428451316643 3910637019020142676974965)
                ·
                  refine ⟨366622220533138375966403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3910637019020142676974965 366622220533138375966403)
                  ·
                    rfl

theorem cell21_1606487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5].length) (baseStart_1606487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606487 prefixEnd_1606487 := by exact prefixLift 1606487
  have htrace : WordTrace (prefixWord ++ tailWord_1606487) baseStart_1606487 baseEnd_1606487 := by
    simpa [prefixWord, tailWord_1606487, baseEnd_1606487] using wordTrace_append hprefix tailTrace_1606487
  have hstable : (prefixWord ++ tailWord_1606487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606487).length < 2 ^ (prefixWord ++ tailWord_1606487).sum := by decide
  have hdescent : baseEnd_1606487 < baseStart_1606487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606639 : List Nat := [1, 1, 2, 1, 4, 3, 3, 3, 3]
def baseStart_1606639 : Nat := 118140960795 + 1606639 * 2 ^ 59
def prefixEnd_1606639 : Nat := 4983230072969 + 3 ^ 40 * 1606639 * 2
def baseEnd_1606639 : Nat := 366656909004019889432759

theorem tailTrace_1606639 : CollatzResearch.WordTrace tailWord_1606639 prefixEnd_1606639 366656909004019889432759 := by
  unfold tailWord_1606639
  simp only [CollatzResearch.WordTrace]
  refine ⟨58598938426428769940838971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39065958950952513293892647 58598938426428769940838971)
  ·
    refine ⟨87898407639643154911258457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58598938426428769940838971 87898407639643154911258457)
    ·
      refine ⟨65923805729732366183443843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87898407639643154911258457 65923805729732366183443843)
      ·
        refine ⟨98885708594598549275165765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65923805729732366183443843 98885708594598549275165765)
        ·
          refine ⟨18541070361487227989093581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98885708594598549275165765 18541070361487227989093581)
          ·
            refine ⟨6952901385557710495910093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18541070361487227989093581 6952901385557710495910093)
            ·
              refine ⟨2607338019584141435966285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6952901385557710495910093 2607338019584141435966285)
              ·
                refine ⟨977751757344053038487357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607338019584141435966285 977751757344053038487357)
                ·
                  refine ⟨366656909004019889432759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977751757344053038487357 366656909004019889432759)
                  ·
                    rfl

theorem cell21_1606639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 3].length) (baseStart_1606639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606639 prefixEnd_1606639 := by exact prefixLift 1606639
  have htrace : WordTrace (prefixWord ++ tailWord_1606639) baseStart_1606639 baseEnd_1606639 := by
    simpa [prefixWord, tailWord_1606639, baseEnd_1606639] using wordTrace_append hprefix tailTrace_1606639
  have hstable : (prefixWord ++ tailWord_1606639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606639).length < 2 ^ (prefixWord ++ tailWord_1606639).sum := by decide
  have hdescent : baseEnd_1606639 < baseStart_1606639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606667 : List Nat := [1, 1, 1, 1, 6, 3, 2, 6]
def baseStart_1606667 : Nat := 118140960795 + 1606667 * 2 ^ 59
def prefixEnd_1606667 : Nat := 4983230072969 + 3 ^ 40 * 1606667 * 2
def baseEnd_1606667 : Nat := 122221099661832687655345

theorem tailTrace_1606667 : CollatzResearch.WordTrace tailWord_1606667 prefixEnd_1606667 122221099661832687655345 := by
  unfold tailWord_1606667
  simp only [CollatzResearch.WordTrace]
  refine ⟨58599959670327330722858255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39066639780218220481905503 58599959670327330722858255)
  ·
    refine ⟨87899939505490996084287383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58599959670327330722858255 87899939505490996084287383)
    ·
      refine ⟨131849909258236494126431075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87899939505490996084287383 131849909258236494126431075)
      ·
        refine ⟨197774863887354741189646613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131849909258236494126431075 197774863887354741189646613)
        ·
          refine ⟨9270696744719753493264685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197774863887354741189646613 9270696744719753493264685)
          ·
            refine ⟨3476511279269907559974257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9270696744719753493264685 3476511279269907559974257)
            ·
              refine ⟨2607383459452430669980693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476511279269907559974257 2607383459452430669980693)
              ·
                refine ⟨122221099661832687655345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2607383459452430669980693 122221099661832687655345)
                ·
                  rfl

theorem cell21_1606667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 6].length) (baseStart_1606667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606667 prefixEnd_1606667 := by exact prefixLift 1606667
  have htrace : WordTrace (prefixWord ++ tailWord_1606667) baseStart_1606667 baseEnd_1606667 := by
    simpa [prefixWord, tailWord_1606667, baseEnd_1606667] using wordTrace_append hprefix tailTrace_1606667
  have hstable : (prefixWord ++ tailWord_1606667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606667).length < 2 ^ (prefixWord ++ tailWord_1606667).sum := by decide
  have hdescent : baseEnd_1606667 < baseStart_1606667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606670 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_1606670 : Nat := 118140960795 + 1606670 * 2 ^ 59
def prefixEnd_1606670 : Nat := 4983230072969 + 3 ^ 40 * 1606670 * 2
def baseEnd_1606670 : Nat := 366663983626370724416029

theorem tailTrace_1606670 : CollatzResearch.WordTrace tailWord_1606670 prefixEnd_1606670 366663983626370724416029 := by
  unfold tailWord_1606670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325008636164557779402183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39066712726210974823478309 7325008636164557779402183)
  ·
    refine ⟨10987512954246836669103275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7325008636164557779402183 10987512954246836669103275)
    ·
      refine ⟨16481269431370255003654913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10987512954246836669103275 16481269431370255003654913)
      ·
        refine ⟨12360952073527691252741185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16481269431370255003654913 12360952073527691252741185)
        ·
          refine ⟨9270714055145768439555889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12360952073527691252741185 9270714055145768439555889)
          ·
            refine ⟨6953035541359326329666917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9270714055145768439555889 6953035541359326329666917)
            ·
              refine ⟨1303694164004873686812547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6953035541359326329666917 1303694164004873686812547)
              ·
                refine ⟨1955541246007310530218821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303694164004873686812547 1955541246007310530218821)
                ·
                  refine ⟨366663983626370724416029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1955541246007310530218821 366663983626370724416029)
                  ·
                    rfl

theorem cell21_1606670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_1606670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606670 prefixEnd_1606670 := by exact prefixLift 1606670
  have htrace : WordTrace (prefixWord ++ tailWord_1606670) baseStart_1606670 baseEnd_1606670 := by
    simpa [prefixWord, tailWord_1606670, baseEnd_1606670] using wordTrace_append hprefix tailTrace_1606670
  have hstable : (prefixWord ++ tailWord_1606670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606670).length < 2 ^ (prefixWord ++ tailWord_1606670).sum := by decide
  have hdescent : baseEnd_1606670 < baseStart_1606670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606681 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 5]
def baseStart_1606681 : Nat := 118140960795 + 1606681 * 2 ^ 59
def prefixEnd_1606681 : Nat := 4983230072969 + 3 ^ 40 * 1606681 * 2
def baseEnd_1606681 : Nat := 366666493976237149732673

theorem tailTrace_1606681 : CollatzResearch.WordTrace tailWord_1606681 prefixEnd_1606681 366666493976237149732673 := by
  unfold tailWord_1606681
  simp only [CollatzResearch.WordTrace]
  refine ⟨58600470292276611113867897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39066980194851074075911931 58600470292276611113867897)
  ·
    refine ⟨43950352719207458335400923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58600470292276611113867897 43950352719207458335400923)
    ·
      refine ⟨65925529078811187503101385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43950352719207458335400923 65925529078811187503101385)
      ·
        refine ⟨49444146809108390627326039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65925529078811187503101385 49444146809108390627326039)
        ·
          refine ⟨74166220213662585940989059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49444146809108390627326039 74166220213662585940989059)
          ·
            refine ⟨111249330320493878911483589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74166220213662585940989059 111249330320493878911483589)
            ·
              refine ⟨20859249435092602295903173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111249330320493878911483589 20859249435092602295903173)
              ·
                refine ⟨3911109269079862930481845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20859249435092602295903173 3911109269079862930481845)
                ·
                  refine ⟨366666493976237149732673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3911109269079862930481845 366666493976237149732673)
                  ·
                    rfl

theorem cell21_1606681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_1606681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606681 prefixEnd_1606681 := by exact prefixLift 1606681
  have htrace : WordTrace (prefixWord ++ tailWord_1606681) baseStart_1606681 baseEnd_1606681 := by
    simpa [prefixWord, tailWord_1606681, baseEnd_1606681] using wordTrace_append hprefix tailTrace_1606681
  have hstable : (prefixWord ++ tailWord_1606681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606681).length < 2 ^ (prefixWord ++ tailWord_1606681).sum := by decide
  have hdescent : baseEnd_1606681 < baseStart_1606681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606749 : List Nat := [1, 4, 4, 1, 2, 1, 2, 3, 3]
def baseStart_1606749 : Nat := 118140960795 + 1606749 * 2 ^ 59
def prefixEnd_1606749 : Nat := 4983230072969 + 3 ^ 40 * 1606749 * 2
def baseEnd_1606749 : Nat := 366682012502684142599201

theorem tailTrace_1606749 : CollatzResearch.WordTrace tailWord_1606749 prefixEnd_1606749 366682012502684142599201 := by
  unfold tailWord_1606749
  simp only [CollatzResearch.WordTrace]
  refine ⟨58602950456030258727343301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39068633637353505818228867 58602950456030258727343301)
  ·
    refine ⟨10988053210505673511376869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58602950456030258727343301 10988053210505673511376869)
    ·
      refine ⟨2060259976969813783383163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10988053210505673511376869 2060259976969813783383163)
      ·
        refine ⟨3090389965454720675074745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060259976969813783383163 3090389965454720675074745)
        ·
          refine ⟨2317792474091040506306059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3090389965454720675074745 2317792474091040506306059)
          ·
            refine ⟨3476688711136560759459089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317792474091040506306059 3476688711136560759459089)
            ·
              refine ⟨2607516533352420569594317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476688711136560759459089 2607516533352420569594317)
              ·
                refine ⟨977818700007157713597869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607516533352420569594317 977818700007157713597869)
                ·
                  refine ⟨366682012502684142599201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977818700007157713597869 366682012502684142599201)
                  ·
                    rfl

theorem cell21_1606749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_1606749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606749 prefixEnd_1606749 := by exact prefixLift 1606749
  have htrace : WordTrace (prefixWord ++ tailWord_1606749) baseStart_1606749 baseEnd_1606749 := by
    simpa [prefixWord, tailWord_1606749, baseEnd_1606749] using wordTrace_append hprefix tailTrace_1606749
  have hstable : (prefixWord ++ tailWord_1606749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606749).length < 2 ^ (prefixWord ++ tailWord_1606749).sum := by decide
  have hdescent : baseEnd_1606749 < baseStart_1606749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606757 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 7]
def baseStart_1606757 : Nat := 118140960795 + 1606757 * 2 ^ 59
def prefixEnd_1606757 : Nat := 4983230072969 + 3 ^ 40 * 1606757 * 2
def baseEnd_1606757 : Nat := 366683838211677906465851

theorem tailTrace_1606757 : CollatzResearch.WordTrace tailWord_1606757 prefixEnd_1606757 366683838211677906465851 := by
  unfold tailWord_1606757
  simp only [CollatzResearch.WordTrace]
  refine ⟨58603242240001276093634525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39068828160000850729089683 58603242240001276093634525)
  ·
    refine ⟨21976215840000478535112947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58603242240001276093634525 21976215840000478535112947)
    ·
      refine ⟨32964323760000717802669421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21976215840000478535112947 32964323760000717802669421)
      ·
        refine ⟨12361621410000269176001033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32964323760000717802669421 12361621410000269176001033)
        ·
          refine ⟨9271216057500201882000775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12361621410000269176001033 9271216057500201882000775)
          ·
            refine ⟨13906824086250302823001163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9271216057500201882000775 13906824086250302823001163)
            ·
              refine ⟨20860236129375454234501745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13906824086250302823001163 20860236129375454234501745)
              ·
                refine ⟨15645177097031590675876309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20860236129375454234501745 15645177097031590675876309)
                ·
                  refine ⟨366683838211677906465851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15645177097031590675876309 366683838211677906465851)
                  ·
                    rfl

theorem cell21_1606757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_1606757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606757 prefixEnd_1606757 := by exact prefixLift 1606757
  have htrace : WordTrace (prefixWord ++ tailWord_1606757) baseStart_1606757 baseEnd_1606757 := by
    simpa [prefixWord, tailWord_1606757, baseEnd_1606757] using wordTrace_append hprefix tailTrace_1606757
  have hstable : (prefixWord ++ tailWord_1606757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606757).length < 2 ^ (prefixWord ++ tailWord_1606757).sum := by decide
  have hdescent : baseEnd_1606757 < baseStart_1606757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606760 : List Nat := [2, 1, 4, 4, 1, 1, 8]
def baseStart_1606760 : Nat := 118140960795 + 1606760 * 2 ^ 59
def prefixEnd_1606760 : Nat := 4983230072969 + 3 ^ 40 * 1606760 * 2
def baseEnd_1606760 : Nat := 40742724761394507546205

theorem tailTrace_1606760 : CollatzResearch.WordTrace tailWord_1606760 prefixEnd_1606760 40742724761394507546205 := by
  unfold tailWord_1606760
  simp only [CollatzResearch.WordTrace]
  refine ⟨29301675829495203802996867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39068901105993605070662489 29301675829495203802996867)
  ·
    refine ⟨43952513744242805704495301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29301675829495203802996867 43952513744242805704495301)
    ·
      refine ⟨8241096327045526069592869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43952513744242805704495301 8241096327045526069592869)
      ·
        refine ⟨1545205561321036138048663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8241096327045526069592869 1545205561321036138048663)
        ·
          refine ⟨2317808341981554207072995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545205561321036138048663 2317808341981554207072995)
          ·
            refine ⟨3476712512972331310609493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317808341981554207072995 3476712512972331310609493)
            ·
              refine ⟨40742724761394507546205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3476712512972331310609493 40742724761394507546205)
              ·
                rfl

theorem cell21_1606760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 8].length) (baseStart_1606760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606760 prefixEnd_1606760 := by exact prefixLift 1606760
  have htrace : WordTrace (prefixWord ++ tailWord_1606760) baseStart_1606760 baseEnd_1606760 := by
    simpa [prefixWord, tailWord_1606760, baseEnd_1606760] using wordTrace_append hprefix tailTrace_1606760
  have hstable : (prefixWord ++ tailWord_1606760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606760).length < 2 ^ (prefixWord ++ tailWord_1606760).sum := by decide
  have hdescent : baseEnd_1606760 < baseStart_1606760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606808 : List Nat := [2, 1, 2, 4, 2, 3, 1, 3, 3]
def baseStart_1606808 : Nat := 118140960795 + 1606808 * 2 ^ 59
def prefixEnd_1606808 : Nat := 4983230072969 + 3 ^ 40 * 1606808 * 2
def baseEnd_1606808 : Nat := 366695477106513151115747

theorem tailTrace_1606808 : CollatzResearch.WordTrace tailWord_1606808 prefixEnd_1606808 366695477106513151115747 := by
  unfold tailWord_1606808
  simp only [CollatzResearch.WordTrace]
  refine ⟨29302551181408255901870539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39070068241877674535827385 29302551181408255901870539)
  ·
    refine ⟨43953826772112383852805809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29302551181408255901870539 43953826772112383852805809)
    ·
      refine ⟨32965370079084287889604357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43953826772112383852805809 32965370079084287889604357)
      ·
        refine ⟨6181006889828303979300817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32965370079084287889604357 6181006889828303979300817)
        ·
          refine ⟨4635755167371227984475613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6181006889828303979300817 4635755167371227984475613)
          ·
            refine ⟨1738408187764210494178355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4635755167371227984475613 1738408187764210494178355)
            ·
              refine ⟨2607612281646315741267533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738408187764210494178355 2607612281646315741267533)
              ·
                refine ⟨977854605617368402975325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607612281646315741267533 977854605617368402975325)
                ·
                  refine ⟨366695477106513151115747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977854605617368402975325 366695477106513151115747)
                  ·
                    rfl

theorem cell21_1606808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_1606808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606808 prefixEnd_1606808 := by exact prefixLift 1606808
  have htrace : WordTrace (prefixWord ++ tailWord_1606808) baseStart_1606808 baseEnd_1606808 := by
    simpa [prefixWord, tailWord_1606808, baseEnd_1606808] using wordTrace_append hprefix tailTrace_1606808
  have hstable : (prefixWord ++ tailWord_1606808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606808).length < 2 ^ (prefixWord ++ tailWord_1606808).sum := by decide
  have hdescent : baseEnd_1606808 < baseStart_1606808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606881 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 4]
def baseStart_1606881 : Nat := 118140960795 + 1606881 * 2 ^ 59
def prefixEnd_1606881 : Nat := 4983230072969 + 3 ^ 40 * 1606881 * 2
def baseEnd_1606881 : Nat := 366712136701081246398931

theorem tailTrace_1606881 : CollatzResearch.WordTrace tailWord_1606881 prefixEnd_1606881 366712136701081246398931 := by
  unfold tailWord_1606881
  simp only [CollatzResearch.WordTrace]
  refine ⟨58607764891552045271148497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39071843261034696847432331 58607764891552045271148497)
  ·
    refine ⟨43955823668664033953361373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58607764891552045271148497 43955823668664033953361373)
    ·
      refine ⟨16483433875749012732510515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43955823668664033953361373 16483433875749012732510515)
      ·
        refine ⟨24725150813623519098765773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16483433875749012732510515 24725150813623519098765773)
        ·
          refine ⟨9271931555108819662037165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24725150813623519098765773 9271931555108819662037165)
          ·
            refine ⟨3476974333165807373263937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9271931555108819662037165 3476974333165807373263937)
            ·
              refine ⟨2607730749874355529947953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476974333165807373263937 2607730749874355529947953)
              ·
                refine ⟨1955798062405766647460965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607730749874355529947953 1955798062405766647460965)
                ·
                  refine ⟨366712136701081246398931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1955798062405766647460965 366712136701081246398931)
                  ·
                    rfl

theorem cell21_1606881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_1606881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1606881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1606881 prefixEnd_1606881 := by exact prefixLift 1606881
  have htrace : WordTrace (prefixWord ++ tailWord_1606881) baseStart_1606881 baseEnd_1606881 := by
    simpa [prefixWord, tailWord_1606881, baseEnd_1606881] using wordTrace_append hprefix tailTrace_1606881
  have hstable : (prefixWord ++ tailWord_1606881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606881).length < 2 ^ (prefixWord ++ tailWord_1606881).sum := by decide
  have hdescent : baseEnd_1606881 < baseStart_1606881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607002 : List Nat := [3, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_1607002 : Nat := 118140960795 + 1607002 * 2 ^ 59
def prefixEnd_1607002 : Nat := 4983230072969 + 3 ^ 40 * 1607002 * 2
def baseEnd_1607002 : Nat := 366739750549611924882017

theorem tailTrace_1607002 : CollatzResearch.WordTrace tailWord_1607002 prefixEnd_1607002 366739750549611924882017 := by
  unfold tailWord_1607002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653044531028420734075815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39074785416075788624202173 14653044531028420734075815)
  ·
    refine ⟨21979566796542631101113723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14653044531028420734075815 21979566796542631101113723)
    ·
      refine ⟨32969350194813946651670585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21979566796542631101113723 32969350194813946651670585)
      ·
        refine ⟨24727012646110459988752939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32969350194813946651670585 24727012646110459988752939)
        ·
          refine ⟨37090518969165689983129409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24727012646110459988752939 37090518969165689983129409)
          ·
            refine ⟨27817889226874267487347057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37090518969165689983129409 27817889226874267487347057)
            ·
              refine ⟨20863416920155700615510293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27817889226874267487347057 20863416920155700615510293)
              ·
                refine ⟨977972668132298466352045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20863416920155700615510293 977972668132298466352045)
                ·
                  refine ⟨366739750549611924882017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977972668132298466352045 366739750549611924882017)
                  ·
                    rfl

theorem cell21_1607002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_1607002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607002 prefixEnd_1607002 := by exact prefixLift 1607002
  have htrace : WordTrace (prefixWord ++ tailWord_1607002) baseStart_1607002 baseEnd_1607002 := by
    simpa [prefixWord, tailWord_1607002, baseEnd_1607002] using wordTrace_append hprefix tailTrace_1607002
  have hstable : (prefixWord ++ tailWord_1607002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607002).length < 2 ^ (prefixWord ++ tailWord_1607002).sum := by decide
  have hdescent : baseEnd_1607002 < baseStart_1607002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607064 : List Nat := [2, 1, 2, 5, 2, 2, 1, 6]
def baseStart_1607064 : Nat := 118140960795 + 1607064 * 2 ^ 59
def prefixEnd_1607064 : Nat := 4983230072969 + 3 ^ 40 * 1607064 * 2
def baseEnd_1607064 : Nat := 122251299931437864949519

theorem tailTrace_1607064 : CollatzResearch.WordTrace tailWord_1607064 prefixEnd_1607064 122251299931437864949519 := by
  unfold tailWord_1607064
  simp only [CollatzResearch.WordTrace]
  refine ⟨29307219724944533762530123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39076292966592711683373497 29307219724944533762530123)
  ·
    refine ⟨43960829587416800643795185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29307219724944533762530123 43960829587416800643795185)
    ·
      refine ⟨32970622190562600482846389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43960829587416800643795185 32970622190562600482846389)
      ·
        refine ⟨3090995830365243795266849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32970622190562600482846389 3090995830365243795266849)
        ·
          refine ⟨2318246872773932846450137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3090995830365243795266849 2318246872773932846450137)
          ·
            refine ⟨1738685154580449634837603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2318246872773932846450137 1738685154580449634837603)
            ·
              refine ⟨2608027731870674452256405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738685154580449634837603 2608027731870674452256405)
              ·
                refine ⟨122251299931437864949519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2608027731870674452256405 122251299931437864949519)
                ·
                  rfl

theorem cell21_1607064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_1607064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607064 prefixEnd_1607064 := by exact prefixLift 1607064
  have htrace : WordTrace (prefixWord ++ tailWord_1607064) baseStart_1607064 baseEnd_1607064 := by
    simpa [prefixWord, tailWord_1607064, baseEnd_1607064] using wordTrace_append hprefix tailTrace_1607064
  have hstable : (prefixWord ++ tailWord_1607064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607064).length < 2 ^ (prefixWord ++ tailWord_1607064).sum := by decide
  have hdescent : baseEnd_1607064 < baseStart_1607064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607120 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_1607120 : Nat := 118140960795 + 1607120 * 2 ^ 59
def prefixEnd_1607120 : Nat := 4983230072969 + 3 ^ 40 * 1607120 * 2
def baseEnd_1607120 : Nat := 366766679757269941915109

theorem tailTrace_1607120 : CollatzResearch.WordTrace tailWord_1607120 prefixEnd_1607120 366766679757269941915109 := by
  unfold tailWord_1607120
  simp only [CollatzResearch.WordTrace]
  refine ⟨29308240968843094544549407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39077654625124126059399209 29308240968843094544549407)
  ·
    refine ⟨43962361453264641816824111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29308240968843094544549407 43962361453264641816824111)
    ·
      refine ⟨65943542179896962725236167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43962361453264641816824111 65943542179896962725236167)
      ·
        refine ⟨98915313269845444087854251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65943542179896962725236167 98915313269845444087854251)
        ·
          refine ⟨148372969904768166131781377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98915313269845444087854251 148372969904768166131781377)
          ·
            refine ⟨111279727428576124598836033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148372969904768166131781377 111279727428576124598836033)
            ·
              refine ⟨83459795571432093449127025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111279727428576124598836033 83459795571432093449127025)
              ·
                refine ⟨62594846678574070086845269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83459795571432093449127025 62594846678574070086845269)
                ·
                  refine ⟨366766679757269941915109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62594846678574070086845269 366766679757269941915109)
                  ·
                    rfl

theorem cell21_1607120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_1607120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607120 prefixEnd_1607120 := by exact prefixLift 1607120
  have htrace : WordTrace (prefixWord ++ tailWord_1607120) baseStart_1607120 baseEnd_1607120 := by
    simpa [prefixWord, tailWord_1607120, baseEnd_1607120] using wordTrace_append hprefix tailTrace_1607120
  have hstable : (prefixWord ++ tailWord_1607120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607120).length < 2 ^ (prefixWord ++ tailWord_1607120).sum := by decide
  have hdescent : baseEnd_1607120 < baseStart_1607120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607137 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 5]
def baseStart_1607137 : Nat := 118140960795 + 1607137 * 2 ^ 59
def prefixEnd_1607137 : Nat := 4983230072969 + 3 ^ 40 * 1607137 * 2
def baseEnd_1607137 : Nat := 366770559388881690131741

theorem tailTrace_1607137 : CollatzResearch.WordTrace tailWord_1607137 prefixEnd_1607137 366770559388881690131741 := by
  unfold tailWord_1607137
  simp only [CollatzResearch.WordTrace]
  refine ⟨58617101978624600992467665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39078067985749733994978443 58617101978624600992467665)
  ·
    refine ⟨43962826483968450744350749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58617101978624600992467665 43962826483968450744350749)
    ·
      refine ⟨16486059931488169029131531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43962826483968450744350749 16486059931488169029131531)
      ·
        refine ⟨24729089897232253543697297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16486059931488169029131531 24729089897232253543697297)
        ·
          refine ⟨18546817422924190157772973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24729089897232253543697297 18546817422924190157772973)
          ·
            refine ⟨6955056533596571309164865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18546817422924190157772973 6955056533596571309164865)
            ·
              refine ⟨5216292400197428481873649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955056533596571309164865 5216292400197428481873649)
              ·
                refine ⟨3912219300148071361405237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5216292400197428481873649 3912219300148071361405237)
                ·
                  refine ⟨366770559388881690131741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912219300148071361405237 366770559388881690131741)
                  ·
                    rfl

theorem cell21_1607137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_1607137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607137 prefixEnd_1607137 := by exact prefixLift 1607137
  have htrace : WordTrace (prefixWord ++ tailWord_1607137) baseStart_1607137 baseEnd_1607137 := by
    simpa [prefixWord, tailWord_1607137, baseEnd_1607137] using wordTrace_append hprefix tailTrace_1607137
  have hstable : (prefixWord ++ tailWord_1607137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607137).length < 2 ^ (prefixWord ++ tailWord_1607137).sum := by decide
  have hdescent : baseEnd_1607137 < baseStart_1607137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607151 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 6]
def baseStart_1607151 : Nat := 118140960795 + 1607151 * 2 ^ 59
def prefixEnd_1607151 : Nat := 4983230072969 + 3 ^ 40 * 1607151 * 2
def baseEnd_1607151 : Nat := 366773754379620776898379

theorem tailTrace_1607151 : CollatzResearch.WordTrace tailWord_1607151 prefixEnd_1607151 366773754379620776898379 := by
  unfold tailWord_1607151
  simp only [CollatzResearch.WordTrace]
  refine ⟨58617612600573881383477307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39078408400382587588984871 58617612600573881383477307)
  ·
    refine ⟨87926418900860822075215961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58617612600573881383477307 87926418900860822075215961)
    ·
      refine ⟨65944814175645616556411971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87926418900860822075215961 65944814175645616556411971)
      ·
        refine ⟨98917221263468424834617957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65944814175645616556411971 98917221263468424834617957)
        ·
          refine ⟨18546978986900329656490867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98917221263468424834617957 18546978986900329656490867)
          ·
            refine ⟨27820468480350494484736301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18546978986900329656490867 27820468480350494484736301)
            ·
              refine ⟨10432675680131435431776113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27820468480350494484736301 10432675680131435431776113)
              ·
                refine ⟨7824506760098576573832085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10432675680131435431776113 7824506760098576573832085)
                ·
                  refine ⟨366773754379620776898379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7824506760098576573832085 366773754379620776898379)
                  ·
                    rfl

theorem cell21_1607151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_1607151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607151 prefixEnd_1607151 := by exact prefixLift 1607151
  have htrace : WordTrace (prefixWord ++ tailWord_1607151) baseStart_1607151 baseEnd_1607151 := by
    simpa [prefixWord, tailWord_1607151, baseEnd_1607151] using wordTrace_append hprefix tailTrace_1607151
  have hstable : (prefixWord ++ tailWord_1607151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607151).length < 2 ^ (prefixWord ++ tailWord_1607151).sum := by decide
  have hdescent : baseEnd_1607151 < baseStart_1607151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607174 : List Nat := [6, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1607174 : Nat := 118140960795 + 1607174 * 2 ^ 59
def prefixEnd_1607174 : Nat := 4983230072969 + 3 ^ 40 * 1607174 * 2
def baseEnd_1607174 : Nat := 122259667764325949338333

theorem tailTrace_1607174 : CollatzResearch.WordTrace tailWord_1607174 prefixEnd_1607174 122259667764325949338333 := by
  unfold tailWord_1607174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1831826608734079884736393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39078967652993704207709717 1831826608734079884736393)
  ·
    refine ⟨1373869956550559913552295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1831826608734079884736393 1373869956550559913552295)
    ·
      refine ⟨2060804934825839870328443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373869956550559913552295 2060804934825839870328443)
      ·
        refine ⟨3091207402238759805492665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060804934825839870328443 3091207402238759805492665)
        ·
          refine ⟨2318405551679069854119499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091207402238759805492665 2318405551679069854119499)
          ·
            refine ⟨3477608327518604781179249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318405551679069854119499 3477608327518604781179249)
            ·
              refine ⟨2608206245638953585884437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3477608327518604781179249 2608206245638953585884437)
              ·
                refine ⟨122259667764325949338333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2608206245638953585884437 122259667764325949338333)
                ·
                  rfl

theorem cell21_1607174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1607174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607174 prefixEnd_1607174 := by exact prefixLift 1607174
  have htrace : WordTrace (prefixWord ++ tailWord_1607174) baseStart_1607174 baseEnd_1607174 := by
    simpa [prefixWord, tailWord_1607174, baseEnd_1607174] using wordTrace_append hprefix tailTrace_1607174
  have hstable : (prefixWord ++ tailWord_1607174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607174).length < 2 ^ (prefixWord ++ tailWord_1607174).sum := by decide
  have hdescent : baseEnd_1607174 < baseStart_1607174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607222 : List Nat := [5, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1607222 : Nat := 118140960795 + 1607222 * 2 ^ 59
def prefixEnd_1607222 : Nat := 4983230072969 + 3 ^ 40 * 1607222 * 2
def baseEnd_1607222 : Nat := 366789957546940431214901

theorem tailTrace_1607222 : CollatzResearch.WordTrace tailWord_1607222 prefixEnd_1607222 366789957546940431214901 := by
  unfold tailWord_1607222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663762636457291281831995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39080134788877773672874613 3663762636457291281831995)
  ·
    refine ⟨5495643954685936922747993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663762636457291281831995 5495643954685936922747993)
    ·
      refine ⟨4121732966014452692060995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5495643954685936922747993 4121732966014452692060995)
      ·
        refine ⟨6182599449021679038091493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121732966014452692060995 6182599449021679038091493)
        ·
          refine ⟨1159237396691564819642155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6182599449021679038091493 1159237396691564819642155)
          ·
            refine ⟨1738856095037347229463233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159237396691564819642155 1738856095037347229463233)
            ·
              refine ⟨1304142071278010422097425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738856095037347229463233 1304142071278010422097425)
              ·
                refine ⟨978106553458507816573069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304142071278010422097425 978106553458507816573069)
                ·
                  refine ⟨366789957546940431214901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978106553458507816573069 366789957546940431214901)
                  ·
                    rfl

theorem cell21_1607222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1607222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607222 prefixEnd_1607222 := by exact prefixLift 1607222
  have htrace : WordTrace (prefixWord ++ tailWord_1607222) baseStart_1607222 baseEnd_1607222 := by
    simpa [prefixWord, tailWord_1607222, baseEnd_1607222] using wordTrace_append hprefix tailTrace_1607222
  have hstable : (prefixWord ++ tailWord_1607222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607222).length < 2 ^ (prefixWord ++ tailWord_1607222).sum := by decide
  have hdescent : baseEnd_1607222 < baseStart_1607222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607244 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1607244 : Nat := 118140960795 + 1607244 * 2 ^ 59
def prefixEnd_1607244 : Nat := 4983230072969 + 3 ^ 40 * 1607244 * 2
def baseEnd_1607244 : Nat := 366794978246673281848189

theorem tailTrace_1607244 : CollatzResearch.WordTrace tailWord_1607244 prefixEnd_1607244 366794978246673281848189 := by
  unfold tailWord_1607244
  simp only [CollatzResearch.WordTrace]
  refine ⟨29310502294618479133306393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39080669726157972177741857 29310502294618479133306393)
  ·
    refine ⟨21982876720963859349979795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29310502294618479133306393 21982876720963859349979795)
    ·
      refine ⟨32974315081445789024969693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21982876720963859349979795 32974315081445789024969693)
      ·
        refine ⟨12365368155542170884363635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32974315081445789024969693 12365368155542170884363635)
        ·
          refine ⟨18548052233313256326545453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12365368155542170884363635 18548052233313256326545453)
          ·
            refine ⟨6955519587492471122454545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18548052233313256326545453 6955519587492471122454545)
            ·
              refine ⟨5216639690619353341840909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955519587492471122454545 5216639690619353341840909)
              ·
                refine ⟨1956239883982257503190341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5216639690619353341840909 1956239883982257503190341)
                ·
                  refine ⟨366794978246673281848189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1956239883982257503190341 366794978246673281848189)
                  ·
                    rfl

theorem cell21_1607244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1607244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607244 prefixEnd_1607244 := by exact prefixLift 1607244
  have htrace : WordTrace (prefixWord ++ tailWord_1607244) baseStart_1607244 baseEnd_1607244 := by
    simpa [prefixWord, tailWord_1607244, baseEnd_1607244] using wordTrace_append hprefix tailTrace_1607244
  have hstable : (prefixWord ++ tailWord_1607244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607244).length < 2 ^ (prefixWord ++ tailWord_1607244).sum := by decide
  have hdescent : baseEnd_1607244 < baseStart_1607244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607278 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1607278 : Nat := 118140960795 + 1607278 * 2 ^ 59
def prefixEnd_1607278 : Nat := 4983230072969 + 3 ^ 40 * 1607278 * 2
def baseEnd_1607278 : Nat := 366802737509896778281453

theorem tailTrace_1607278 : CollatzResearch.WordTrace tailWord_1607278 prefixEnd_1607278 366802737509896778281453 := by
  unfold tailWord_1607278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327780583889222759168811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39081496447409188048900325 7327780583889222759168811)
  ·
    refine ⟨10991670875833834138753217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7327780583889222759168811 10991670875833834138753217)
    ·
      refine ⟨8243753156875375604064913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10991670875833834138753217 8243753156875375604064913)
      ·
        refine ⟨6182814867656531703048685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8243753156875375604064913 6182814867656531703048685)
        ·
          refine ⟨2318555575371199388643257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6182814867656531703048685 2318555575371199388643257)
          ·
            refine ⟨1738916681528399541482443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2318555575371199388643257 1738916681528399541482443)
            ·
              refine ⟨2608375022292599312223665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738916681528399541482443 2608375022292599312223665)
              ·
                refine ⟨1956281266719449484167749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608375022292599312223665 1956281266719449484167749)
                ·
                  refine ⟨366802737509896778281453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1956281266719449484167749 366802737509896778281453)
                  ·
                    rfl

theorem cell21_1607278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1607278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607278 prefixEnd_1607278 := by exact prefixLift 1607278
  have htrace : WordTrace (prefixWord ++ tailWord_1607278) baseStart_1607278 baseEnd_1607278 := by
    simpa [prefixWord, tailWord_1607278, baseEnd_1607278] using wordTrace_append hprefix tailTrace_1607278
  have hstable : (prefixWord ++ tailWord_1607278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607278).length < 2 ^ (prefixWord ++ tailWord_1607278).sum := by decide
  have hdescent : baseEnd_1607278 < baseStart_1607278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607289 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 5]
def baseStart_1607289 : Nat := 118140960795 + 1607289 * 2 ^ 59
def prefixEnd_1607289 : Nat := 4983230072969 + 3 ^ 40 * 1607289 * 2
def baseEnd_1607289 : Nat := 366805247859763203598097

theorem tailTrace_1607289 : CollatzResearch.WordTrace tailWord_1607289 prefixEnd_1607289 366805247859763203598097 := by
  unfold tailWord_1607289
  simp only [CollatzResearch.WordTrace]
  refine ⟨58622645874073930952000921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39081763916049287301333947 58622645874073930952000921)
  ·
    refine ⟨43966984405555448214000691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58622645874073930952000921 43966984405555448214000691)
    ·
      refine ⟨65950476608333172321001037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43966984405555448214000691 65950476608333172321001037)
      ·
        refine ⟨24731428728124939620375389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65950476608333172321001037 24731428728124939620375389)
        ·
          refine ⟨9274285773046852357640771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24731428728124939620375389 9274285773046852357640771)
          ·
            refine ⟨13911428659570278536461157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9274285773046852357640771 13911428659570278536461157)
            ·
              refine ⟨2608392873669427225586467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13911428659570278536461157 2608392873669427225586467)
              ·
                refine ⟨3912589310504140838379701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608392873669427225586467 3912589310504140838379701)
                ·
                  refine ⟨366805247859763203598097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912589310504140838379701 366805247859763203598097)
                  ·
                    rfl

theorem cell21_1607289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_1607289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607289 prefixEnd_1607289 := by exact prefixLift 1607289
  have htrace : WordTrace (prefixWord ++ tailWord_1607289) baseStart_1607289 baseEnd_1607289 := by
    simpa [prefixWord, tailWord_1607289, baseEnd_1607289] using wordTrace_append hprefix tailTrace_1607289
  have hstable : (prefixWord ++ tailWord_1607289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607289).length < 2 ^ (prefixWord ++ tailWord_1607289).sum := by decide
  have hdescent : baseEnd_1607289 < baseStart_1607289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607393 : List Nat := [1, 2, 3, 1, 14]
def baseStart_1607393 : Nat := 118140960795 + 1607393 * 2 ^ 59
def prefixEnd_1607393 : Nat := 4983230072969 + 3 ^ 40 * 1607393 * 2
def baseEnd_1607393 : Nat := 4528752865144223874871

theorem tailTrace_1607393 : CollatzResearch.WordTrace tailWord_1607393 prefixEnd_1607393 4528752865144223874871 := by
  unfold tailWord_1607393
  simp only [CollatzResearch.WordTrace]
  refine ⟨58626439065697156713786833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39084292710464771142524555 58626439065697156713786833)
  ·
    refine ⟨43969829299272867535340125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58626439065697156713786833 43969829299272867535340125)
    ·
      refine ⟨16488685987227325325752547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43969829299272867535340125 16488685987227325325752547)
      ·
        refine ⟨24733028980840987988628821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16488685987227325325752547 24733028980840987988628821)
        ·
          refine ⟨4528752865144223874871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 24733028980840987988628821 4528752865144223874871)
          ·
            rfl

theorem cell21_1607393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 14].length) (baseStart_1607393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607393 prefixEnd_1607393 := by exact prefixLift 1607393
  have htrace : WordTrace (prefixWord ++ tailWord_1607393) baseStart_1607393 baseEnd_1607393 := by
    simpa [prefixWord, tailWord_1607393, baseEnd_1607393] using wordTrace_append hprefix tailTrace_1607393
  have hstable : (prefixWord ++ tailWord_1607393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607393).length < 2 ^ (prefixWord ++ tailWord_1607393).sum := by decide
  have hdescent : baseEnd_1607393 < baseStart_1607393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607396 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_1607396 : Nat := 118140960795 + 1607396 * 2 ^ 59
def prefixEnd_1607396 : Nat := 4983230072969 + 3 ^ 40 * 1607396 * 2
def baseEnd_1607396 : Nat := 366829666717554795314545

theorem tailTrace_1607396 : CollatzResearch.WordTrace tailWord_1607396 prefixEnd_1607396 366829666717554795314545 := by
  unfold tailWord_1607396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29313274242343144113073021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39084365656457525484097361 29313274242343144113073021)
  ·
    refine ⟨10992477840878679042402383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29313274242343144113073021 10992477840878679042402383)
    ·
      refine ⟨16488716761318018563603575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10992477840878679042402383 16488716761318018563603575)
      ·
        refine ⟨24733075141977027845405363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16488716761318018563603575 24733075141977027845405363)
        ·
          refine ⟨37099612712965541768108045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24733075141977027845405363 37099612712965541768108045)
          ·
            refine ⟨13912354767362078163040517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37099612712965541768108045 13912354767362078163040517)
            ·
              refine ⟨2608566518880389655570097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13912354767362078163040517 2608566518880389655570097)
              ·
                refine ⟨1956424889160292241677573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608566518880389655570097 1956424889160292241677573)
                ·
                  refine ⟨366829666717554795314545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1956424889160292241677573 366829666717554795314545)
                  ·
                    rfl

theorem cell21_1607396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_1607396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607396 prefixEnd_1607396 := by exact prefixLift 1607396
  have htrace : WordTrace (prefixWord ++ tailWord_1607396) baseStart_1607396 baseEnd_1607396 := by
    simpa [prefixWord, tailWord_1607396, baseEnd_1607396] using wordTrace_append hprefix tailTrace_1607396
  have hstable : (prefixWord ++ tailWord_1607396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607396).length < 2 ^ (prefixWord ++ tailWord_1607396).sum := by decide
  have hdescent : baseEnd_1607396 < baseStart_1607396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607424 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_1607424 : Nat := 118140960795 + 1607424 * 2 ^ 59
def prefixEnd_1607424 : Nat := 4983230072969 + 3 ^ 40 * 1607424 * 2
def baseEnd_1607424 : Nat := 366836056699032968847821

theorem tailTrace_1607424 : CollatzResearch.WordTrace tailWord_1607424 prefixEnd_1607424 366836056699032968847821 := by
  unfold tailWord_1607424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29313784864292424504082663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39085046485723232672110217 29313784864292424504082663)
  ·
    refine ⟨43970677296438636756123995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29313784864292424504082663 43970677296438636756123995)
    ·
      refine ⟨65956015944657955134185993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43970677296438636756123995 65956015944657955134185993)
      ·
        refine ⟨49467011958493466350639495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65956015944657955134185993 49467011958493466350639495)
        ·
          refine ⟨74200517937740199525959243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49467011958493466350639495 74200517937740199525959243)
          ·
            refine ⟨111300776906610299288938865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74200517937740199525959243 111300776906610299288938865)
            ·
              refine ⟨83475582679957724466704149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111300776906610299288938865 83475582679957724466704149)
              ·
                refine ⟨3912917938123018334376757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83475582679957724466704149 3912917938123018334376757)
                ·
                  refine ⟨366836056699032968847821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912917938123018334376757 366836056699032968847821)
                  ·
                    rfl

theorem cell21_1607424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_1607424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607424 prefixEnd_1607424 := by exact prefixLift 1607424
  have htrace : WordTrace (prefixWord ++ tailWord_1607424) baseStart_1607424 baseEnd_1607424 := by
    simpa [prefixWord, tailWord_1607424, baseEnd_1607424] using wordTrace_append hprefix tailTrace_1607424
  have hstable : (prefixWord ++ tailWord_1607424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607424).length < 2 ^ (prefixWord ++ tailWord_1607424).sum := by decide
  have hdescent : baseEnd_1607424 < baseStart_1607424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607455 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 6]
def baseStart_1607455 : Nat := 118140960795 + 1607455 * 2 ^ 59
def prefixEnd_1607455 : Nat := 4983230072969 + 3 ^ 40 * 1607455 * 2
def baseEnd_1607455 : Nat := 366843131321383803831091

theorem tailTrace_1607455 : CollatzResearch.WordTrace tailWord_1607455 prefixEnd_1607455 366843131321383803831091 := by
  unfold tailWord_1607455
  simp only [CollatzResearch.WordTrace]
  refine ⟨58628700391472541302543819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39085800260981694201695879 58628700391472541302543819)
  ·
    refine ⟨87943050587208811953815729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58628700391472541302543819 87943050587208811953815729)
    ·
      refine ⟨65957287940406608965361797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87943050587208811953815729 65957287940406608965361797)
      ·
        refine ⟨12366991488826239181005337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65957287940406608965361797 12366991488826239181005337)
        ·
          refine ⟨9275243616619679385754003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12366991488826239181005337 9275243616619679385754003)
          ·
            refine ⟨13912865424929519078631005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9275243616619679385754003 13912865424929519078631005)
            ·
              refine ⟨5217324534348569654486627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13912865424929519078631005 5217324534348569654486627)
              ·
                refine ⟨7825986801522854481729941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5217324534348569654486627 7825986801522854481729941)
                ·
                  refine ⟨366843131321383803831091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7825986801522854481729941 366843131321383803831091)
                  ·
                    rfl

theorem cell21_1607455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_1607455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607455 prefixEnd_1607455 := by exact prefixLift 1607455
  have htrace : WordTrace (prefixWord ++ tailWord_1607455) baseStart_1607455 baseEnd_1607455 := by
    simpa [prefixWord, tailWord_1607455, baseEnd_1607455] using wordTrace_append hprefix tailTrace_1607455
  have hstable : (prefixWord ++ tailWord_1607455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607455).length < 2 ^ (prefixWord ++ tailWord_1607455).sum := by decide
  have hdescent : baseEnd_1607455 < baseStart_1607455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607458 : List Nat := [3, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1607458 : Nat := 118140960795 + 1607458 * 2 ^ 59
def prefixEnd_1607458 : Nat := 4983230072969 + 3 ^ 40 * 1607458 * 2
def baseEnd_1607458 : Nat := 366843815962256465281085

theorem tailTrace_1607458 : CollatzResearch.WordTrace tailWord_1607458 prefixEnd_1607458 366843815962256465281085 := by
  unfold tailWord_1607458
  simp only [CollatzResearch.WordTrace]
  refine ⟨14657202452615418203725757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39085873206974448543268685 14657202452615418203725757)
  ·
    refine ⟨5496450919730781826397159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14657202452615418203725757 5496450919730781826397159)
    ·
      refine ⟨8244676379596172739595739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5496450919730781826397159 8244676379596172739595739)
      ·
        refine ⟨12367014569394259109393609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8244676379596172739595739 12367014569394259109393609)
        ·
          refine ⟨9275260927045694332045207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12367014569394259109393609 9275260927045694332045207)
          ·
            refine ⟨13912891390568541498067811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9275260927045694332045207 13912891390568541498067811)
            ·
              refine ⟨20869337085852812247101717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13912891390568541498067811 20869337085852812247101717)
              ·
                refine ⟨978250175899350574082893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20869337085852812247101717 978250175899350574082893)
                ·
                  refine ⟨366843815962256465281085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978250175899350574082893 366843815962256465281085)
                  ·
                    rfl

theorem cell21_1607458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1607458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607458 prefixEnd_1607458 := by exact prefixLift 1607458
  have htrace : WordTrace (prefixWord ++ tailWord_1607458) baseStart_1607458 baseEnd_1607458 := by
    simpa [prefixWord, tailWord_1607458, baseEnd_1607458] using wordTrace_append hprefix tailTrace_1607458
  have hstable : (prefixWord ++ tailWord_1607458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607458).length < 2 ^ (prefixWord ++ tailWord_1607458).sum := by decide
  have hdescent : baseEnd_1607458 < baseStart_1607458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607545 : List Nat := [1, 2, 1, 3, 2, 2, 1, 9]
def baseStart_1607545 : Nat := 118140960795 + 1607545 * 2 ^ 59
def prefixEnd_1607545 : Nat := 4983230072969 + 3 ^ 40 * 1607545 * 2
def baseEnd_1607545 : Nat := 122287890182521215776969

theorem tailTrace_1607545 : CollatzResearch.WordTrace tailWord_1607545 prefixEnd_1607545 122287890182521215776969 := by
  unfold tailWord_1607545
  simp only [CollatzResearch.WordTrace]
  refine ⟨58631982961146486673320089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39087988640764324448880059 58631982961146486673320089)
  ·
    refine ⟨43973987220859865004990067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58631982961146486673320089 43973987220859865004990067)
    ·
      refine ⟨65960980831289797507485101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43973987220859865004990067 65960980831289797507485101)
      ·
        refine ⟨24735367811733674065306913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65960980831289797507485101 24735367811733674065306913)
        ·
          refine ⟨18551525858800255548980185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24735367811733674065306913 18551525858800255548980185)
          ·
            refine ⟨13913644394100191661735139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18551525858800255548980185 13913644394100191661735139)
            ·
              refine ⟨20870466591150287492602709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13913644394100191661735139 20870466591150287492602709)
              ·
                refine ⟨122287890182521215776969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20870466591150287492602709 122287890182521215776969)
                ·
                  rfl

theorem cell21_1607545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 9].length) (baseStart_1607545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607545 prefixEnd_1607545 := by exact prefixLift 1607545
  have htrace : WordTrace (prefixWord ++ tailWord_1607545) baseStart_1607545 baseEnd_1607545 := by
    simpa [prefixWord, tailWord_1607545, baseEnd_1607545] using wordTrace_append hprefix tailTrace_1607545
  have hstable : (prefixWord ++ tailWord_1607545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607545).length < 2 ^ (prefixWord ++ tailWord_1607545).sum := by decide
  have hdescent : baseEnd_1607545 < baseStart_1607545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607562 : List Nat := [3, 1, 2, 4, 2, 9]
def baseStart_1607562 : Nat := 118140960795 + 1607562 * 2 ^ 59
def prefixEnd_1607562 : Nat := 4983230072969 + 3 ^ 40 * 1607562 * 2
def baseEnd_1607562 : Nat := 13587687043673162798057

theorem tailTrace_1607562 : CollatzResearch.WordTrace tailWord_1607562 prefixEnd_1607562 13587687043673162798057 := by
  unfold tailWord_1607562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14658150750521224644172235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39088402001389932384459293 14658150750521224644172235)
  ·
    refine ⟨21987226125781836966258353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14658150750521224644172235 21987226125781836966258353)
    ·
      refine ⟨16490419594336377724693765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21987226125781836966258353 16490419594336377724693765)
      ·
        refine ⟨3091953673938070823380081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16490419594336377724693765 3091953673938070823380081)
        ·
          refine ⟨2318965255453553117535061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091953673938070823380081 2318965255453553117535061)
          ·
            refine ⟨13587687043673162798057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2318965255453553117535061 13587687043673162798057)
            ·
              rfl

theorem cell21_1607562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 9].length) (baseStart_1607562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607562 prefixEnd_1607562 := by exact prefixLift 1607562
  have htrace : WordTrace (prefixWord ++ tailWord_1607562) baseStart_1607562 baseEnd_1607562 := by
    simpa [prefixWord, tailWord_1607562, baseEnd_1607562] using wordTrace_append hprefix tailTrace_1607562
  have hstable : (prefixWord ++ tailWord_1607562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607562).length < 2 ^ (prefixWord ++ tailWord_1607562).sum := by decide
  have hdescent : baseEnd_1607562 < baseStart_1607562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607624 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_1607624 : Nat := 118140960795 + 1607624 * 2 ^ 59
def prefixEnd_1607624 : Nat := 4983230072969 + 3 ^ 40 * 1607624 * 2
def baseEnd_1607624 : Nat := 366881699423877065514079

theorem tailTrace_1607624 : CollatzResearch.WordTrace tailWord_1607624 prefixEnd_1607624 366881699423877065514079 := by
  unfold tailWord_1607624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29317432163930141582722963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39089909551906855443630617 29317432163930141582722963)
  ·
    refine ⟨43976148245895212374084445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29317432163930141582722963 43976148245895212374084445)
    ·
      refine ⟨16491055592210704640281667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43976148245895212374084445 16491055592210704640281667)
      ·
        refine ⟨24736583388316056960422501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16491055592210704640281667 24736583388316056960422501)
        ·
          refine ⟨4638109385309260680079219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24736583388316056960422501 4638109385309260680079219)
          ·
            refine ⟨6957164077963891020118829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638109385309260680079219 6957164077963891020118829)
            ·
              refine ⟨2608936529236459132544561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6957164077963891020118829 2608936529236459132544561)
              ·
                refine ⟨1956702396927344349408421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608936529236459132544561 1956702396927344349408421)
                ·
                  refine ⟨366881699423877065514079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1956702396927344349408421 366881699423877065514079)
                  ·
                    rfl

theorem cell21_1607624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_1607624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607624 prefixEnd_1607624 := by exact prefixLift 1607624
  have htrace : WordTrace (prefixWord ++ tailWord_1607624) baseStart_1607624 baseEnd_1607624 := by
    simpa [prefixWord, tailWord_1607624, baseEnd_1607624] using wordTrace_append hprefix tailTrace_1607624
  have hstable : (prefixWord ++ tailWord_1607624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607624).length < 2 ^ (prefixWord ++ tailWord_1607624).sum := by decide
  have hdescent : baseEnd_1607624 < baseStart_1607624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607641 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 4]
def baseStart_1607641 : Nat := 118140960795 + 1607641 * 2 ^ 59
def prefixEnd_1607641 : Nat := 4983230072969 + 3 ^ 40 * 1607641 * 2
def baseEnd_1607641 : Nat := 366885579055488813730711

theorem tailTrace_1607641 : CollatzResearch.WordTrace tailWord_1607641 prefixEnd_1607641 366885579055488813730711 := by
  unfold tailWord_1607641
  simp only [CollatzResearch.WordTrace]
  refine ⟨58635484368798695068814777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39090322912532463379209851 58635484368798695068814777)
  ·
    refine ⟨43976613276599021301611083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58635484368798695068814777 43976613276599021301611083)
    ·
      refine ⟨65964919914898531952416625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43976613276599021301611083 65964919914898531952416625)
      ·
        refine ⟨49473689936173898964312469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65964919914898531952416625 49473689936173898964312469)
        ·
          refine ⟨2319079215758151513952147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49473689936173898964312469 2319079215758151513952147)
          ·
            refine ⟨3478618823637227270928221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319079215758151513952147 3478618823637227270928221)
            ·
              refine ⟨1304482058863960226598083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478618823637227270928221 1304482058863960226598083)
              ·
                refine ⟨1956723088295940339897125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304482058863960226598083 1956723088295940339897125)
                ·
                  refine ⟨366885579055488813730711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1956723088295940339897125 366885579055488813730711)
                  ·
                    rfl

theorem cell21_1607641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_1607641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607641 prefixEnd_1607641 := by exact prefixLift 1607641
  have htrace : WordTrace (prefixWord ++ tailWord_1607641) baseStart_1607641 baseEnd_1607641 := by
    simpa [prefixWord, tailWord_1607641, baseEnd_1607641] using wordTrace_append hprefix tailTrace_1607641
  have hstable : (prefixWord ++ tailWord_1607641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607641).length < 2 ^ (prefixWord ++ tailWord_1607641).sum := by decide
  have hdescent : baseEnd_1607641 < baseStart_1607641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607652 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1607652 : Nat := 118140960795 + 1607652 * 2 ^ 59
def prefixEnd_1607652 : Nat := 4983230072969 + 3 ^ 40 * 1607652 * 2
def baseEnd_1607652 : Nat := 366888089405355239047355

theorem tailTrace_1607652 : CollatzResearch.WordTrace tailWord_1607652 prefixEnd_1607652 366888089405355239047355 := by
  unfold tailWord_1607652
  simp only [CollatzResearch.WordTrace]
  refine ⟨29317942785879421973732605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39090590381172562631643473 29317942785879421973732605)
  ·
    refine ⟨10994228544704783240149727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29317942785879421973732605 10994228544704783240149727)
    ·
      refine ⟨16491342817057174860224591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10994228544704783240149727 16491342817057174860224591)
      ·
        refine ⟨24737014225585762290336887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16491342817057174860224591 24737014225585762290336887)
        ·
          refine ⟨37105521338378643435505331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24737014225585762290336887 37105521338378643435505331)
          ·
            refine ⟨55658282007567965153257997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37105521338378643435505331 55658282007567965153257997)
            ·
              refine ⟨20871855752837986932471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55658282007567965153257997 20871855752837986932471749)
              ·
                refine ⟨3913472953657122549838453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20871855752837986932471749 3913472953657122549838453)
                ·
                  refine ⟨366888089405355239047355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3913472953657122549838453 366888089405355239047355)
                  ·
                    rfl

theorem cell21_1607652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1607652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607652 prefixEnd_1607652 := by exact prefixLift 1607652
  have htrace : WordTrace (prefixWord ++ tailWord_1607652) baseStart_1607652 baseEnd_1607652 := by
    simpa [prefixWord, tailWord_1607652, baseEnd_1607652] using wordTrace_append hprefix tailTrace_1607652
  have hstable : (prefixWord ++ tailWord_1607652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607652).length < 2 ^ (prefixWord ++ tailWord_1607652).sum := by decide
  have hdescent : baseEnd_1607652 < baseStart_1607652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
