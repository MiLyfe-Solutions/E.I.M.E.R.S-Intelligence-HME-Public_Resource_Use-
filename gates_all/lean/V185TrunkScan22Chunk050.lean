import V185TrunkScan22Chunk049

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_448274 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_448274 : Nat := 118140960795 + 448274 * 2 ^ 59
def prefixEnd_448274 : Nat := 4983230072969 + 3 ^ 40 * 448274 * 2
def baseEnd_448274 : Nat := 153453351275789573075621

theorem tailTrace_448274 : CollatzResearch.WordTrace tailWord_448274 prefixEnd_448274 153453351275789573075621 := by
  unfold tailWord_448274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4087473994496832987281969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10899930651991554632751917 4087473994496832987281969)
  ·
    refine ⟨3065605495872624740461477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4087473994496832987281969 3065605495872624740461477)
    ·
      refine ⟨574801030476117138836527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3065605495872624740461477 574801030476117138836527)
      ·
        refine ⟨862201545714175708254791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574801030476117138836527 862201545714175708254791)
        ·
          refine ⟨1293302318571263562382187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862201545714175708254791 1293302318571263562382187)
          ·
            refine ⟨1939953477856895343573281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293302318571263562382187 1939953477856895343573281)
            ·
              refine ⟨1454965108392671507679961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939953477856895343573281 1454965108392671507679961)
              ·
                refine ⟨1091223831294503630759971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454965108392671507679961 1091223831294503630759971)
                ·
                  refine ⟨1636835746941755446139957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091223831294503630759971 1636835746941755446139957)
                  ·
                    refine ⟨153453351275789573075621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1636835746941755446139957 153453351275789573075621)
                    ·
                      rfl

theorem cell22_448274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_448274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448274 prefixEnd_448274 := by exact prefixLift 448274
  have htrace : WordTrace (prefixWord ++ tailWord_448274) baseStart_448274 baseEnd_448274 := by
    simpa [prefixWord, tailWord_448274, baseEnd_448274] using wordTrace_append hprefix tailTrace_448274
  have hstable : (prefixWord ++ tailWord_448274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448274).length < 2 ^ (prefixWord ++ tailWord_448274).sum := by decide
  have hdescent : baseEnd_448274 < baseStart_448274 := by decide
  rcases family_descends (prefixWord ++ tailWord_448274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448308 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_448308 : Nat := 118140960795 + 448308 * 2 ^ 59
def prefixEnd_448308 : Nat := 4983230072969 + 3 ^ 40 * 448308 * 2
def baseEnd_448308 : Nat := 153464990170624817725517

theorem tailTrace_448308 : CollatzResearch.WordTrace tailWord_448308 prefixEnd_448308 153464990170624817725517 := by
  unfold tailWord_448308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8175568029932077877932789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10900757373242770503910385 8175568029932077877932789)
  ·
    refine ⟨766459502806132301056199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8175568029932077877932789 766459502806132301056199)
    ·
      refine ⟨1149689254209198451584299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766459502806132301056199 1149689254209198451584299)
      ·
        refine ⟨1724533881313797677376449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149689254209198451584299 1724533881313797677376449)
        ·
          refine ⟨1293400410985348258032337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724533881313797677376449 1293400410985348258032337)
          ·
            refine ⟨970050308239011193524253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293400410985348258032337 970050308239011193524253)
            ·
              refine ⟨363768865589629197571595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 970050308239011193524253 363768865589629197571595)
              ·
                refine ⟨545653298384443796357393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363768865589629197571595 545653298384443796357393)
                ·
                  refine ⟨409239973788332847268045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545653298384443796357393 409239973788332847268045)
                  ·
                    refine ⟨153464990170624817725517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409239973788332847268045 153464990170624817725517)
                    ·
                      rfl

theorem cell22_448308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_448308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448308 prefixEnd_448308 := by exact prefixLift 448308
  have htrace : WordTrace (prefixWord ++ tailWord_448308) baseStart_448308 baseEnd_448308 := by
    simpa [prefixWord, tailWord_448308, baseEnd_448308] using wordTrace_append hprefix tailTrace_448308
  have hstable : (prefixWord ++ tailWord_448308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448308).length < 2 ^ (prefixWord ++ tailWord_448308).sum := by decide
  have hdescent : baseEnd_448308 < baseStart_448308 := by decide
  rcases family_descends (prefixWord ++ tailWord_448308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448366 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_448366 : Nat := 118140960795 + 448366 * 2 ^ 59
def prefixEnd_448366 : Nat := 4983230072969 + 3 ^ 40 * 448366 * 2
def baseEnd_448366 : Nat := 51161614918643999925113

theorem tailTrace_448366 : CollatzResearch.WordTrace tailWord_448366 prefixEnd_448366 51161614918643999925113 := by
  unfold tailWord_448366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044156436706753957684619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10902167662436021107651301 2044156436706753957684619)
  ·
    refine ⟨3066234655060130936526929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2044156436706753957684619 3066234655060130936526929)
    ·
      refine ⟨2299675991295098202395197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3066234655060130936526929 2299675991295098202395197)
      ·
        refine ⟨862378496735661825898199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2299675991295098202395197 862378496735661825898199)
        ·
          refine ⟨1293567745103492738847299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862378496735661825898199 1293567745103492738847299)
          ·
            refine ⟨1940351617655239108270949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293567745103492738847299 1940351617655239108270949)
            ·
              refine ⟨363815928310357332800803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1940351617655239108270949 363815928310357332800803)
              ·
                refine ⟨545723892465535999201205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363815928310357332800803 545723892465535999201205)
                ·
                  refine ⟨51161614918643999925113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 545723892465535999201205 51161614918643999925113)
                  ·
                    rfl

theorem cell22_448366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_448366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448366 prefixEnd_448366 := by exact prefixLift 448366
  have htrace : WordTrace (prefixWord ++ tailWord_448366) baseStart_448366 baseEnd_448366 := by
    simpa [prefixWord, tailWord_448366, baseEnd_448366] using wordTrace_append hprefix tailTrace_448366
  have hstable : (prefixWord ++ tailWord_448366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448366).length < 2 ^ (prefixWord ++ tailWord_448366).sum := by decide
  have hdescent : baseEnd_448366 < baseStart_448366 := by decide
  rcases family_descends (prefixWord ++ tailWord_448366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448409 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 2, 3]
def baseStart_448409 : Nat := 118140960795 + 448409 * 2 ^ 59
def prefixEnd_448409 : Nat := 4983230072969 + 3 ^ 40 * 448409 * 2
def baseEnd_448409 : Nat := 153499564534694220950207

theorem tailTrace_448409 : CollatzResearch.WordTrace tailWord_448409 prefixEnd_448409 153499564534694220950207 := by
  unfold tailWord_448409
  simp only [CollatzResearch.WordTrace]
  refine ⟨16354819832498250005292281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10903213221665500003528187 16354819832498250005292281)
  ·
    refine ⟨12266114874373687503969211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16354819832498250005292281 12266114874373687503969211)
    ·
      refine ⟨18399172311560531255953817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12266114874373687503969211 18399172311560531255953817)
      ·
        refine ⟨13799379233670398441965363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18399172311560531255953817 13799379233670398441965363)
        ·
          refine ⟨20699068850505597662948045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13799379233670398441965363 20699068850505597662948045)
          ·
            refine ⟨7762150818939599123605517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20699068850505597662948045 7762150818939599123605517)
            ·
              refine ⟨2910806557102349671352069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7762150818939599123605517 2910806557102349671352069)
              ·
                refine ⟨545776229456690563378513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2910806557102349671352069 545776229456690563378513)
                ·
                  refine ⟨409332172092517922533885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545776229456690563378513 409332172092517922533885)
                  ·
                    refine ⟨153499564534694220950207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409332172092517922533885 153499564534694220950207)
                    ·
                      rfl

theorem cell22_448409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_448409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448409 prefixEnd_448409 := by exact prefixLift 448409
  have htrace : WordTrace (prefixWord ++ tailWord_448409) baseStart_448409 baseEnd_448409 := by
    simpa [prefixWord, tailWord_448409, baseEnd_448409] using wordTrace_append hprefix tailTrace_448409
  have hstable : (prefixWord ++ tailWord_448409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448409).length < 2 ^ (prefixWord ++ tailWord_448409).sum := by decide
  have hdescent : baseEnd_448409 < baseStart_448409 := by decide
  rcases family_descends (prefixWord ++ tailWord_448409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448471 : List Nat := [1, 1, 3, 2, 1, 1, 3, 6, 1, 3]
def baseStart_448471 : Nat := 118140960795 + 448471 * 2 ^ 59
def prefixEnd_448471 : Nat := 4983230072969 + 3 ^ 40 * 448471 * 2
def baseEnd_448471 : Nat := 153520788401746725900017

theorem tailTrace_448471 : CollatzResearch.WordTrace tailWord_448471 prefixEnd_448471 153520788401746725900017 := by
  unfold tailWord_448471
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357081158273634594049267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10904720772182423062699511 16357081158273634594049267)
  ·
    refine ⟨24535621737410451891073901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16357081158273634594049267 24535621737410451891073901)
    ·
      refine ⟨9200858151528919459152713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24535621737410451891073901 9200858151528919459152713)
      ·
        refine ⟨6900643613646689594364535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9200858151528919459152713 6900643613646689594364535)
        ·
          refine ⟨10350965420470034391546803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6900643613646689594364535 10350965420470034391546803)
          ·
            refine ⟨15526448130705051587320205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350965420470034391546803 15526448130705051587320205)
            ·
              refine ⟨5822418049014394345245077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15526448130705051587320205 5822418049014394345245077)
              ·
                refine ⟨272925846047549734933363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5822418049014394345245077 272925846047549734933363)
                ·
                  refine ⟨409388769071324602400045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272925846047549734933363 409388769071324602400045)
                  ·
                    refine ⟨153520788401746725900017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409388769071324602400045 153520788401746725900017)
                    ·
                      rfl

theorem cell22_448471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_448471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448471 prefixEnd_448471 := by exact prefixLift 448471
  have htrace : WordTrace (prefixWord ++ tailWord_448471) baseStart_448471 baseEnd_448471 := by
    simpa [prefixWord, tailWord_448471, baseEnd_448471] using wordTrace_append hprefix tailTrace_448471
  have hstable : (prefixWord ++ tailWord_448471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448471).length < 2 ^ (prefixWord ++ tailWord_448471).sum := by decide
  have hdescent : baseEnd_448471 < baseStart_448471 := by decide
  rcases family_descends (prefixWord ++ tailWord_448471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448535 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 5]
def baseStart_448535 : Nat := 118140960795 + 448535 * 2 ^ 59
def prefixEnd_448535 : Nat := 4983230072969 + 3 ^ 40 * 448535 * 2
def baseEnd_448535 : Nat := 51180898969890630766607

theorem tailTrace_448535 : CollatzResearch.WordTrace tailWord_448535 prefixEnd_448535 51180898969890630766607 := by
  unfold tailWord_448535
  simp only [CollatzResearch.WordTrace]
  refine ⟨16359415430041773524379059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10906276953361182349586039 16359415430041773524379059)
  ·
    refine ⟨24539123145062660286568589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16359415430041773524379059 24539123145062660286568589)
    ·
      refine ⟨9202171179398497607463221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24539123145062660286568589 9202171179398497607463221)
      ·
        refine ⟨862703548068609150699677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9202171179398497607463221 862703548068609150699677)
        ·
          refine ⟨323513830525728431512379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 862703548068609150699677 323513830525728431512379)
          ·
            refine ⟨485270745788592647268569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323513830525728431512379 485270745788592647268569)
            ·
              refine ⟨363953059341444485451427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485270745788592647268569 363953059341444485451427)
              ·
                refine ⟨545929589012166728177141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363953059341444485451427 545929589012166728177141)
                ·
                  refine ⟨51180898969890630766607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 545929589012166728177141 51180898969890630766607)
                  ·
                    rfl

theorem cell22_448535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 5].length) (baseStart_448535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448535 prefixEnd_448535 := by exact prefixLift 448535
  have htrace : WordTrace (prefixWord ++ tailWord_448535) baseStart_448535 baseEnd_448535 := by
    simpa [prefixWord, tailWord_448535, baseEnd_448535] using wordTrace_append hprefix tailTrace_448535
  have hstable : (prefixWord ++ tailWord_448535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448535).length < 2 ^ (prefixWord ++ tailWord_448535).sum := by decide
  have hdescent : baseEnd_448535 < baseStart_448535 := by decide
  rcases family_descends (prefixWord ++ tailWord_448535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448574 : List Nat := [4, 2, 1, 3, 12]
def baseStart_448574 : Nat := 118140960795 + 448574 * 2 ^ 59
def prefixEnd_448574 : Nat := 4983230072969 + 3 ^ 40 * 448574 * 2
def baseEnd_448574 : Nat := 631917890562505311007

theorem tailTrace_448574 : CollatzResearch.WordTrace tailWord_448574 prefixEnd_448574 631917890562505311007 := by
  unfold tailWord_448574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045104734612560398131097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10907225251266988790032517 2045104734612560398131097)
  ·
    refine ⟨1533828550959420298598323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2045104734612560398131097 1533828550959420298598323)
    ·
      refine ⟨2300742826439130447897485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533828550959420298598323 2300742826439130447897485)
      ·
        refine ⟨862778559914673917961557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2300742826439130447897485 862778559914673917961557)
        ·
          refine ⟨631917890562505311007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 862778559914673917961557 631917890562505311007)
          ·
            rfl

theorem cell22_448574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 12].length) (baseStart_448574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448574 prefixEnd_448574 := by exact prefixLift 448574
  have htrace : WordTrace (prefixWord ++ tailWord_448574) baseStart_448574 baseEnd_448574 := by
    simpa [prefixWord, tailWord_448574, baseEnd_448574] using wordTrace_append hprefix tailTrace_448574
  have hstable : (prefixWord ++ tailWord_448574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448574).length < 2 ^ (prefixWord ++ tailWord_448574).sum := by decide
  have hdescent : baseEnd_448574 < baseStart_448574 := by decide
  rcases family_descends (prefixWord ++ tailWord_448574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448610 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_448610 : Nat := 118140960795 + 448610 * 2 ^ 59
def prefixEnd_448610 : Nat := 4983230072969 + 3 ^ 40 * 448610 * 2
def baseEnd_448610 : Nat := 153568370942396696674591

theorem tailTrace_448610 : CollatzResearch.WordTrace tailWord_448610 prefixEnd_448610 153568370942396696674591 := by
  unfold tailWord_448610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090537726192515333339821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10908100603180040888906189 4090537726192515333339821)
  ·
    refine ⟨1533951647322193250002433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4090537726192515333339821 1533951647322193250002433)
    ·
      refine ⟨1150463735491644937501825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1533951647322193250002433 1150463735491644937501825)
      ·
        refine ⟨862847801618733703126369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1150463735491644937501825 862847801618733703126369)
        ·
          refine ⟨647135851214050277344777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862847801618733703126369 647135851214050277344777)
          ·
            refine ⟨485351888410537708008583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647135851214050277344777 485351888410537708008583)
            ·
              refine ⟨728027832615806562012875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485351888410537708008583 728027832615806562012875)
              ·
                refine ⟨1092041748923709843019313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728027832615806562012875 1092041748923709843019313)
                ·
                  refine ⟨819031311692782382264485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092041748923709843019313 819031311692782382264485)
                  ·
                    refine ⟨153568370942396696674591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819031311692782382264485 153568370942396696674591)
                    ·
                      rfl

theorem cell22_448610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_448610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448610 prefixEnd_448610 := by exact prefixLift 448610
  have htrace : WordTrace (prefixWord ++ tailWord_448610) baseStart_448610 baseEnd_448610 := by
    simpa [prefixWord, tailWord_448610, baseEnd_448610] using wordTrace_append hprefix tailTrace_448610
  have hstable : (prefixWord ++ tailWord_448610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448610).length < 2 ^ (prefixWord ++ tailWord_448610).sum := by decide
  have hdescent : baseEnd_448610 < baseStart_448610 := by decide
  rcases family_descends (prefixWord ++ tailWord_448610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448623 : List Nat := [1, 1, 2, 1, 3, 4, 1, 5, 1, 3]
def baseStart_448623 : Nat := 118140960795 + 448623 * 2 ^ 59
def prefixEnd_448623 : Nat := 4983230072969 + 3 ^ 40 * 448623 * 2
def baseEnd_448623 : Nat := 153572821108068996099551

theorem tailTrace_448623 : CollatzResearch.WordTrace tailWord_448623 prefixEnd_448623 153572821108068996099551 := by
  unfold tailWord_448623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16362625053722964553582523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10908416702481976369055015 16362625053722964553582523)
  ·
    refine ⟨24543937580584446830373785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16362625053722964553582523 24543937580584446830373785)
    ·
      refine ⟨18407953185438335122780339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24543937580584446830373785 18407953185438335122780339)
      ·
        refine ⟨27611929778157502684170509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18407953185438335122780339 27611929778157502684170509)
        ·
          refine ⟨10354473666809063506563941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27611929778157502684170509 10354473666809063506563941)
          ·
            refine ⟨1941463812526699407480739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10354473666809063506563941 1941463812526699407480739)
            ·
              refine ⟨2912195718790049111221109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941463812526699407480739 2912195718790049111221109)
              ·
                refine ⟨273018348636567104176979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2912195718790049111221109 273018348636567104176979)
                ·
                  refine ⟨409527522954850656265469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273018348636567104176979 409527522954850656265469)
                  ·
                    refine ⟨153572821108068996099551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409527522954850656265469 153572821108068996099551)
                    ·
                      rfl

theorem cell22_448623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 3].length) (baseStart_448623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448623 prefixEnd_448623 := by exact prefixLift 448623
  have htrace : WordTrace (prefixWord ++ tailWord_448623) baseStart_448623 baseEnd_448623 := by
    simpa [prefixWord, tailWord_448623, baseEnd_448623] using wordTrace_append hprefix tailTrace_448623
  have hstable : (prefixWord ++ tailWord_448623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448623).length < 2 ^ (prefixWord ++ tailWord_448623).sum := by decide
  have hdescent : baseEnd_448623 < baseStart_448623 := by decide
  rcases family_descends (prefixWord ++ tailWord_448623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448636 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 5]
def baseStart_448636 : Nat := 118140960795 + 448636 * 2 ^ 59
def prefixEnd_448636 : Nat := 4983230072969 + 3 ^ 40 * 448636 * 2
def baseEnd_448636 : Nat := 51192423757913765174837

theorem tailTrace_448636 : CollatzResearch.WordTrace tailWord_448636 prefixEnd_448636 51192423757913765174837 := by
  unfold tailWord_448636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181549601337933886902881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10908732801783911849203841 8181549601337933886902881)
  ·
    refine ⟨6136162201003450415177161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8181549601337933886902881 6136162201003450415177161)
    ·
      refine ⟨4602121650752587811382871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6136162201003450415177161 4602121650752587811382871)
      ·
        refine ⟨6903182476128881717074307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602121650752587811382871 6903182476128881717074307)
        ·
          refine ⟨10354773714193322575611461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903182476128881717074307 10354773714193322575611461)
          ·
            refine ⟨1941520071411247982927149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10354773714193322575611461 1941520071411247982927149)
            ·
              refine ⟨728070026779217993597681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1941520071411247982927149 728070026779217993597681)
              ·
                refine ⟨546052520084413495198261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728070026779217993597681 546052520084413495198261)
                ·
                  refine ⟨51192423757913765174837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546052520084413495198261 51192423757913765174837)
                  ·
                    rfl

theorem cell22_448636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_448636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448636 prefixEnd_448636 := by exact prefixLift 448636
  have htrace : WordTrace (prefixWord ++ tailWord_448636) baseStart_448636 baseEnd_448636 := by
    simpa [prefixWord, tailWord_448636, baseEnd_448636] using wordTrace_append hprefix tailTrace_448636
  have hstable : (prefixWord ++ tailWord_448636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448636).length < 2 ^ (prefixWord ++ tailWord_448636).sum := by decide
  have hdescent : baseEnd_448636 < baseStart_448636 := by decide
  rcases family_descends (prefixWord ++ tailWord_448636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448696 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 4, 3]
def baseStart_448696 : Nat := 118140960795 + 448696 * 2 ^ 59
def prefixEnd_448696 : Nat := 4983230072969 + 3 ^ 40 * 448696 * 2
def baseEnd_448696 : Nat := 153597810499921139024327

theorem tailTrace_448696 : CollatzResearch.WordTrace tailWord_448696 prefixEnd_448696 153597810499921139024327 := by
  unfold tailWord_448696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182643791229249010494971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10910191721638998680659961 8182643791229249010494971)
  ·
    refine ⟨12273965686843873515742457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8182643791229249010494971 12273965686843873515742457)
    ·
      refine ⟨9205474265132905136806843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12273965686843873515742457 9205474265132905136806843)
      ·
        refine ⟨13808211397699357705210265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205474265132905136806843 13808211397699357705210265)
        ·
          refine ⟨10356158548274518278907699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13808211397699357705210265 10356158548274518278907699)
          ·
            refine ⟨15534237822411777418361549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10356158548274518278907699 15534237822411777418361549)
            ·
              refine ⟨5825339183404416531885581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15534237822411777418361549 5825339183404416531885581)
              ·
                refine ⟨2184502193776656199457093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5825339183404416531885581 2184502193776656199457093)
                ·
                  refine ⟨409594161333123037398205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184502193776656199457093 409594161333123037398205)
                  ·
                    refine ⟨153597810499921139024327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409594161333123037398205 153597810499921139024327)
                    ·
                      rfl

theorem cell22_448696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_448696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448696 prefixEnd_448696 := by exact prefixLift 448696
  have htrace : WordTrace (prefixWord ++ tailWord_448696) baseStart_448696 baseEnd_448696 := by
    simpa [prefixWord, tailWord_448696, baseEnd_448696] using wordTrace_append hprefix tailTrace_448696
  have hstable : (prefixWord ++ tailWord_448696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448696).length < 2 ^ (prefixWord ++ tailWord_448696).sum := by decide
  have hdescent : baseEnd_448696 < baseStart_448696 := by decide
  rcases family_descends (prefixWord ++ tailWord_448696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448709 : List Nat := [1, 3, 1, 1, 1, 1, 5, 9]
def baseStart_448709 : Nat := 118140960795 + 448709 * 2 ^ 59
def prefixEnd_448709 : Nat := 4983230072969 + 3 ^ 40 * 448709 * 2
def baseEnd_448709 : Nat := 17066917851732604272143

theorem tailTrace_448709 : CollatzResearch.WordTrace tailWord_448709 prefixEnd_448709 17066917851732604272143 := by
  unfold tailWord_448709
  simp only [CollatzResearch.WordTrace]
  refine ⟨16365761731411401241213181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10910507820940934160808787 16365761731411401241213181)
  ·
    refine ⟨6137160649279275465454943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16365761731411401241213181 6137160649279275465454943)
    ·
      refine ⟨9205740973918913198182415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6137160649279275465454943 9205740973918913198182415)
      ·
        refine ⟨13808611460878369797273623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205740973918913198182415 13808611460878369797273623)
        ·
          refine ⟨20712917191317554695910435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13808611460878369797273623 20712917191317554695910435)
          ·
            refine ⟨31069375786976332043865653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20712917191317554695910435 31069375786976332043865653)
            ·
              refine ⟨2912753980029031129112405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31069375786976332043865653 2912753980029031129112405)
              ·
                refine ⟨17066917851732604272143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2912753980029031129112405 17066917851732604272143)
                ·
                  rfl

theorem cell22_448709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 9].length) (baseStart_448709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448709 prefixEnd_448709 := by exact prefixLift 448709
  have htrace : WordTrace (prefixWord ++ tailWord_448709) baseStart_448709 baseEnd_448709 := by
    simpa [prefixWord, tailWord_448709, baseEnd_448709] using wordTrace_append hprefix tailTrace_448709
  have hstable : (prefixWord ++ tailWord_448709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448709).length < 2 ^ (prefixWord ++ tailWord_448709).sum := by decide
  have hdescent : baseEnd_448709 < baseStart_448709 := by decide
  rcases family_descends (prefixWord ++ tailWord_448709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448728 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_448728 : Nat := 118140960795 + 448728 * 2 ^ 59
def prefixEnd_448728 : Nat := 4983230072969 + 3 ^ 40 * 448728 * 2
def baseEnd_448728 : Nat := 153608764753883722224229

theorem tailTrace_448728 : CollatzResearch.WordTrace tailWord_448728 prefixEnd_448728 153608764753883722224229 := by
  unfold tailWord_448728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8183227359171283743077419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10910969812228378324103225 8183227359171283743077419)
  ·
    refine ⟨12274841038756925614616129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8183227359171283743077419 12274841038756925614616129)
    ·
      refine ⟨9206130779067694210962097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12274841038756925614616129 9206130779067694210962097)
      ·
        refine ⟨6904598084300770658221573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9206130779067694210962097 6904598084300770658221573)
        ·
          refine ⟨1294612140806394498416545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6904598084300770658221573 1294612140806394498416545)
          ·
            refine ⟨970959105604795873812409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294612140806394498416545 970959105604795873812409)
            ·
              refine ⟨728219329203596905359307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970959105604795873812409 728219329203596905359307)
              ·
                refine ⟨1092328993805395358038961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728219329203596905359307 1092328993805395358038961)
                ·
                  refine ⟨819246745354046518529221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092328993805395358038961 819246745354046518529221)
                  ·
                    refine ⟨153608764753883722224229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819246745354046518529221 153608764753883722224229)
                    ·
                      rfl

theorem cell22_448728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_448728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448728 prefixEnd_448728 := by exact prefixLift 448728
  have htrace : WordTrace (prefixWord ++ tailWord_448728) baseStart_448728 baseEnd_448728 := by
    simpa [prefixWord, tailWord_448728, baseEnd_448728] using wordTrace_append hprefix tailTrace_448728
  have hstable : (prefixWord ++ tailWord_448728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448728).length < 2 ^ (prefixWord ++ tailWord_448728).sum := by decide
  have hdescent : baseEnd_448728 < baseStart_448728 := by decide
  rcases family_descends (prefixWord ++ tailWord_448728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448749 : List Nat := [1, 5, 1, 2, 4, 1, 2, 2, 4]
def baseStart_448749 : Nat := 118140960795 + 448749 * 2 ^ 59
def prefixEnd_448749 : Nat := 4983230072969 + 3 ^ 40 * 448749 * 2
def baseEnd_448749 : Nat := 51205317827682222483055

theorem tailTrace_448749 : CollatzResearch.WordTrace tailWord_448749 prefixEnd_448749 51205317827682222483055 := by
  unfold tailWord_448749
  simp only [CollatzResearch.WordTrace]
  refine ⟨16367220651266488072669301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10911480434177658715112867 16367220651266488072669301)
  ·
    refine ⟨1534426936056233256812747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16367220651266488072669301 1534426936056233256812747)
    ·
      refine ⟨2301640404084349885219121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534426936056233256812747 2301640404084349885219121)
      ·
        refine ⟨1726230303063262413914341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2301640404084349885219121 1726230303063262413914341)
        ·
          refine ⟨323668181824361702608939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1726230303063262413914341 323668181824361702608939)
          ·
            refine ⟨485502272736542553913409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323668181824361702608939 485502272736542553913409)
            ·
              refine ⟨364126704552406915435057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485502272736542553913409 364126704552406915435057)
              ·
                refine ⟨273095028414305186576293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364126704552406915435057 273095028414305186576293)
                ·
                  refine ⟨51205317827682222483055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273095028414305186576293 51205317827682222483055)
                  ·
                    rfl

theorem cell22_448749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_448749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448749 prefixEnd_448749 := by exact prefixLift 448749
  have htrace : WordTrace (prefixWord ++ tailWord_448749) baseStart_448749 baseEnd_448749 := by
    simpa [prefixWord, tailWord_448749, baseEnd_448749] using wordTrace_append hprefix tailTrace_448749
  have hstable : (prefixWord ++ tailWord_448749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448749).length < 2 ^ (prefixWord ++ tailWord_448749).sum := by decide
  have hdescent : baseEnd_448749 < baseStart_448749 := by decide
  rcases family_descends (prefixWord ++ tailWord_448749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448771 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 5]
def baseStart_448771 : Nat := 118140960795 + 448771 * 2 ^ 59
def prefixEnd_448771 : Nat := 4983230072969 + 3 ^ 40 * 448771 * 2
def baseEnd_448771 : Nat := 51207828177548647799699

theorem tailTrace_448771 : CollatzResearch.WordTrace tailWord_448771 prefixEnd_448771 51207828177548647799699 := by
  unfold tailWord_448771
  simp only [CollatzResearch.WordTrace]
  refine ⟨16368023057186785829970167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10912015371457857219980111 16368023057186785829970167)
  ·
    refine ⟨24552034585780178744955251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16368023057186785829970167 24552034585780178744955251)
    ·
      refine ⟨36828051878670268117432877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24552034585780178744955251 36828051878670268117432877)
      ·
        refine ⟨13810519454501350544037329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36828051878670268117432877 13810519454501350544037329)
        ·
          refine ⟨10357889590876012908027997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13810519454501350544037329 10357889590876012908027997)
          ·
            refine ⟨3884208596578504840510499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10357889590876012908027997 3884208596578504840510499)
            ·
              refine ⟨5826312894867757260765749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884208596578504840510499 5826312894867757260765749)
              ·
                refine ⟨546216833893852243196789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5826312894867757260765749 546216833893852243196789)
                ·
                  refine ⟨51207828177548647799699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546216833893852243196789 51207828177548647799699)
                  ·
                    rfl

theorem cell22_448771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 5].length) (baseStart_448771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448771 prefixEnd_448771 := by exact prefixLift 448771
  have htrace : WordTrace (prefixWord ++ tailWord_448771) baseStart_448771 baseEnd_448771 := by
    simpa [prefixWord, tailWord_448771, baseEnd_448771] using wordTrace_append hprefix tailTrace_448771
  have hstable : (prefixWord ++ tailWord_448771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448771).length < 2 ^ (prefixWord ++ tailWord_448771).sum := by decide
  have hdescent : baseEnd_448771 < baseStart_448771 := by decide
  rcases family_descends (prefixWord ++ tailWord_448771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448805 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 5]
def baseStart_448805 : Nat := 118140960795 + 448805 * 2 ^ 59
def prefixEnd_448805 : Nat := 4983230072969 + 3 ^ 40 * 448805 * 2
def baseEnd_448805 : Nat := 51211707809160396016331

theorem tailTrace_448805 : CollatzResearch.WordTrace tailWord_448805 prefixEnd_448805 51211707809160396016331 := by
  unfold tailWord_448805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16369263139063609636707869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10912842092709073091138579 16369263139063609636707869)
  ·
    refine ⟨6138473677148853613765451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16369263139063609636707869 6138473677148853613765451)
    ·
      refine ⟨9207710515723280420648177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138473677148853613765451 9207710515723280420648177)
      ·
        refine ⟨6905782886792460315486133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9207710515723280420648177 6905782886792460315486133)
        ·
          refine ⟨647417145636793154576825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6905782886792460315486133 647417145636793154576825)
          ·
            refine ⟨485562859227594865932619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647417145636793154576825 485562859227594865932619)
            ·
              refine ⟨728344288841392298898929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485562859227594865932619 728344288841392298898929)
              ·
                refine ⟨546258216631044224174197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728344288841392298898929 546258216631044224174197)
                ·
                  refine ⟨51211707809160396016331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546258216631044224174197 51211707809160396016331)
                  ·
                    rfl

theorem cell22_448805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_448805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448805 prefixEnd_448805 := by exact prefixLift 448805
  have htrace : WordTrace (prefixWord ++ tailWord_448805) baseStart_448805 baseEnd_448805 := by
    simpa [prefixWord, tailWord_448805, baseEnd_448805] using wordTrace_append hprefix tailTrace_448805
  have hstable : (prefixWord ++ tailWord_448805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448805).length < 2 ^ (prefixWord ++ tailWord_448805).sum := by decide
  have hdescent : baseEnd_448805 < baseStart_448805 := by decide
  rcases family_descends (prefixWord ++ tailWord_448805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448848 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 4, 3]
def baseStart_448848 : Nat := 118140960795 + 448848 * 2 ^ 59
def prefixEnd_448848 : Nat := 4983230072969 + 3 ^ 40 * 448848 * 2
def baseEnd_448848 : Nat := 153649843206243409223861

theorem tailTrace_448848 : CollatzResearch.WordTrace tailWord_448848 prefixEnd_448848 153649843206243409223861 := by
  unfold tailWord_448848
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185415738953913990261599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10913887651938551987015465 8185415738953913990261599)
  ·
    refine ⟨12278123608430870985392399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8185415738953913990261599 12278123608430870985392399)
    ·
      refine ⟨18417185412646306478088599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12278123608430870985392399 18417185412646306478088599)
      ·
        refine ⟨27625778118969459717132899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18417185412646306478088599 27625778118969459717132899)
        ·
          refine ⟨41438667178454189575699349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27625778118969459717132899 41438667178454189575699349)
          ·
            refine ⟨1942437523990040136360907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41438667178454189575699349 1942437523990040136360907)
            ·
              refine ⟨2913656285985060204541361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942437523990040136360907 2913656285985060204541361)
              ·
                refine ⟨2185242214488795153406021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2913656285985060204541361 2185242214488795153406021)
                ·
                  refine ⟨409732915216649091263629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185242214488795153406021 409732915216649091263629)
                  ·
                    refine ⟨153649843206243409223861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409732915216649091263629 153649843206243409223861)
                    ·
                      rfl

theorem cell22_448848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_448848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448848 prefixEnd_448848 := by exact prefixLift 448848
  have htrace : WordTrace (prefixWord ++ tailWord_448848) baseStart_448848 baseEnd_448848 := by
    simpa [prefixWord, tailWord_448848, baseEnd_448848] using wordTrace_append hprefix tailTrace_448848
  have hstable : (prefixWord ++ tailWord_448848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448848).length < 2 ^ (prefixWord ++ tailWord_448848).sum := by decide
  have hdescent : baseEnd_448848 < baseStart_448848 := by decide
  rcases family_descends (prefixWord ++ tailWord_448848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448850 : List Nat := [3, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_448850 : Nat := 118140960795 + 448850 * 2 ^ 59
def prefixEnd_448850 : Nat := 4983230072969 + 3 ^ 40 * 448850 * 2
def baseEnd_448850 : Nat := 51216842615705356891285

theorem tailTrace_448850 : CollatzResearch.WordTrace tailWord_448850 prefixEnd_448850 51216842615705356891285 := by
  unfold tailWord_448850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092726105975145580524001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10913936282600388214730669 4092726105975145580524001)
  ·
    refine ⟨3069544579481359185393001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4092726105975145580524001 3069544579481359185393001)
    ·
      refine ⟨2302158434611019389044751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3069544579481359185393001 2302158434611019389044751)
      ·
        refine ⟨3453237651916529083567127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302158434611019389044751 3453237651916529083567127)
        ·
          refine ⟨5179856477874793625350691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453237651916529083567127 5179856477874793625350691)
          ·
            refine ⟨7769784716812190438026037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179856477874793625350691 7769784716812190438026037)
            ·
              refine ⟨728417317201142853564941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7769784716812190438026037 728417317201142853564941)
              ·
                refine ⟨273156493950428570086853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 728417317201142853564941 273156493950428570086853)
                ·
                  refine ⟨51216842615705356891285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273156493950428570086853 51216842615705356891285)
                  ·
                    rfl

theorem cell22_448850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_448850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448850 prefixEnd_448850 := by exact prefixLift 448850
  have htrace : WordTrace (prefixWord ++ tailWord_448850) baseStart_448850 baseEnd_448850 := by
    simpa [prefixWord, tailWord_448850, baseEnd_448850] using wordTrace_append hprefix tailTrace_448850
  have hstable : (prefixWord ++ tailWord_448850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448850).length < 2 ^ (prefixWord ++ tailWord_448850).sum := by decide
  have hdescent : baseEnd_448850 < baseStart_448850 := by decide
  rcases family_descends (prefixWord ++ tailWord_448850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448882 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_448882 : Nat := 118140960795 + 448882 * 2 ^ 59
def prefixEnd_448882 : Nat := 4983230072969 + 3 ^ 40 * 448882 * 2
def baseEnd_448882 : Nat := 153661482101078653873757

theorem tailTrace_448882 : CollatzResearch.WordTrace tailWord_448882 prefixEnd_448882 153661482101078653873757 := by
  unfold tailWord_448882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093017889946162946815225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10914714373189767858173933 4093017889946162946815225)
  ·
    refine ⟨3069763417459622210111419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4093017889946162946815225 3069763417459622210111419)
    ·
      refine ⟨4604645126189433315167129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3069763417459622210111419 4604645126189433315167129)
      ·
        refine ⟨3453483844642074986375347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4604645126189433315167129 3453483844642074986375347)
        ·
          refine ⟨5180225766963112479563021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453483844642074986375347 5180225766963112479563021)
          ·
            refine ⟨1942584662611167179836133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5180225766963112479563021 1942584662611167179836133)
            ·
              refine ⟨364234624239593846219275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1942584662611167179836133 364234624239593846219275)
              ·
                refine ⟨546351936359390769328913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364234624239593846219275 546351936359390769328913)
                ·
                  refine ⟨409763952269543076996685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546351936359390769328913 409763952269543076996685)
                  ·
                    refine ⟨153661482101078653873757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409763952269543076996685 153661482101078653873757)
                    ·
                      rfl

theorem cell22_448882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_448882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448882 prefixEnd_448882 := by exact prefixLift 448882
  have htrace : WordTrace (prefixWord ++ tailWord_448882) baseStart_448882 baseEnd_448882 := by
    simpa [prefixWord, tailWord_448882, baseEnd_448882] using wordTrace_append hprefix tailTrace_448882
  have hstable : (prefixWord ++ tailWord_448882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448882).length < 2 ^ (prefixWord ++ tailWord_448882).sum := by decide
  have hdescent : baseEnd_448882 < baseStart_448882 := by decide
  rcases family_descends (prefixWord ++ tailWord_448882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448886 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_448886 : Nat := 118140960795 + 448886 * 2 ^ 59
def prefixEnd_448886 : Nat := 4983230072969 + 3 ^ 40 * 448886 * 2
def baseEnd_448886 : Nat := 153662851382823976773745

theorem tailTrace_448886 : CollatzResearch.WordTrace tailWord_448886 prefixEnd_448886 153662851382823976773745 := by
  unfold tailWord_448886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1023263590735635029400407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10914811634513440313604341 1023263590735635029400407)
  ·
    refine ⟨1534895386103452544100611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1023263590735635029400407 1534895386103452544100611)
    ·
      refine ⟨2302343079155178816150917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534895386103452544100611 2302343079155178816150917)
      ·
        refine ⟨431689327341596028028297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2302343079155178816150917 431689327341596028028297)
        ·
          refine ⟨323766995506197021021223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431689327341596028028297 323766995506197021021223)
          ·
            refine ⟨485650493259295531531835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323766995506197021021223 485650493259295531531835)
            ·
              refine ⟨728475739888943297297753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485650493259295531531835 728475739888943297297753)
              ·
                refine ⟨546356804916707472973315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728475739888943297297753 546356804916707472973315)
                ·
                  refine ⟨819535207375061209459973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546356804916707472973315 819535207375061209459973)
                  ·
                    refine ⟨153662851382823976773745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819535207375061209459973 153662851382823976773745)
                    ·
                      rfl

theorem cell22_448886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_448886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448886 prefixEnd_448886 := by exact prefixLift 448886
  have htrace : WordTrace (prefixWord ++ tailWord_448886) baseStart_448886 baseEnd_448886 := by
    simpa [prefixWord, tailWord_448886, baseEnd_448886] using wordTrace_append hprefix tailTrace_448886
  have hstable : (prefixWord ++ tailWord_448886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448886).length < 2 ^ (prefixWord ++ tailWord_448886).sum := by decide
  have hdescent : baseEnd_448886 < baseStart_448886 := by decide
  rcases family_descends (prefixWord ++ tailWord_448886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448927 : List Nat := [1, 1, 2, 5, 1, 1, 3, 4, 1, 3]
def baseStart_448927 : Nat := 118140960795 + 448927 * 2 ^ 59
def prefixEnd_448927 : Nat := 4983230072969 + 3 ^ 40 * 448927 * 2
def baseEnd_448927 : Nat := 153676886520713536498619

theorem tailTrace_448927 : CollatzResearch.WordTrace tailWord_448927 prefixEnd_448927 153676886520713536498619 := by
  unfold tailWord_448927
  simp only [CollatzResearch.WordTrace]
  refine ⟨16373712844621624472649035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10915808563081082981766023 16373712844621624472649035)
  ·
    refine ⟨24560569266932436708973553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16373712844621624472649035 24560569266932436708973553)
    ·
      refine ⟨18420426950199327531730165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24560569266932436708973553 18420426950199327531730165)
      ·
        refine ⟨1726915026581186956099703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18420426950199327531730165 1726915026581186956099703)
        ·
          refine ⟨2590372539871780434149555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726915026581186956099703 2590372539871780434149555)
          ·
            refine ⟨3885558809807670651224333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590372539871780434149555 3885558809807670651224333)
            ·
              refine ⟨1457084553677876494209125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3885558809807670651224333 1457084553677876494209125)
              ·
                refine ⟨273203353814601842664211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1457084553677876494209125 273203353814601842664211)
                ·
                  refine ⟨409805030721902763996317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273203353814601842664211 409805030721902763996317)
                  ·
                    refine ⟨153676886520713536498619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409805030721902763996317 153676886520713536498619)
                    ·
                      rfl

theorem cell22_448927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 3].length) (baseStart_448927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448927 prefixEnd_448927 := by exact prefixLift 448927
  have htrace : WordTrace (prefixWord ++ tailWord_448927) baseStart_448927 baseEnd_448927 := by
    simpa [prefixWord, tailWord_448927, baseEnd_448927] using wordTrace_append hprefix tailTrace_448927
  have hstable : (prefixWord ++ tailWord_448927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448927).length < 2 ^ (prefixWord ++ tailWord_448927).sum := by decide
  have hdescent : baseEnd_448927 < baseStart_448927 := by decide
  rcases family_descends (prefixWord ++ tailWord_448927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448970 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_448970 : Nat := 118140960795 + 448970 * 2 ^ 59
def prefixEnd_448970 : Nat := 4983230072969 + 3 ^ 40 * 448970 * 2
def baseEnd_448970 : Nat := 153691606299475757673487

theorem tailTrace_448970 : CollatzResearch.WordTrace tailWord_448970 prefixEnd_448970 153691606299475757673487 := by
  unfold tailWord_448970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093820295866460704116091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10916854122310561877642909 4093820295866460704116091)
  ·
    refine ⟨6140730443799691056174137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4093820295866460704116091 6140730443799691056174137)
    ·
      refine ⟨4605547832849768292130603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6140730443799691056174137 4605547832849768292130603)
      ·
        refine ⟨6908321749274652438195905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605547832849768292130603 6908321749274652438195905)
        ·
          refine ⟨5181241311955989328646929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6908321749274652438195905 5181241311955989328646929)
          ·
            refine ⟨3885930983966991996485197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5181241311955989328646929 3885930983966991996485197)
            ·
              refine ⟨1457224118987621998681949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3885930983966991996485197 1457224118987621998681949)
              ·
                refine ⟨546459044620358249505731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1457224118987621998681949 546459044620358249505731)
                ·
                  refine ⟨819688566930537374258597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546459044620358249505731 819688566930537374258597)
                  ·
                    refine ⟨153691606299475757673487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819688566930537374258597 153691606299475757673487)
                    ·
                      rfl

theorem cell22_448970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_448970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448970 prefixEnd_448970 := by exact prefixLift 448970
  have htrace : WordTrace (prefixWord ++ tailWord_448970) baseStart_448970 baseEnd_448970 := by
    simpa [prefixWord, tailWord_448970, baseEnd_448970] using wordTrace_append hprefix tailTrace_448970
  have hstable : (prefixWord ++ tailWord_448970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448970).length < 2 ^ (prefixWord ++ tailWord_448970).sum := by decide
  have hdescent : baseEnd_448970 < baseStart_448970 := by decide
  rcases family_descends (prefixWord ++ tailWord_448970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448985 : List Nat := [1, 2, 1, 2, 4, 1, 1, 6, 4]
def baseStart_448985 : Nat := 118140960795 + 448985 * 2 ^ 59
def prefixEnd_448985 : Nat := 4983230072969 + 3 ^ 40 * 448985 * 2
def baseEnd_448985 : Nat := 51232247035340239516147

theorem tailTrace_448985 : CollatzResearch.WordTrace tailWord_448985 prefixEnd_448985 51232247035340239516147 := by
  unfold tailWord_448985
  simp only [CollatzResearch.WordTrace]
  refine ⟨16375828278411500378260409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10917218852274333585506939 16375828278411500378260409)
  ·
    refine ⟨12281871208808625283695307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16375828278411500378260409 12281871208808625283695307)
    ·
      refine ⟨18422806813212937925542961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12281871208808625283695307 18422806813212937925542961)
      ·
        refine ⟨13817105109909703444157221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18422806813212937925542961 13817105109909703444157221)
        ·
          refine ⟨2590707208108069395779479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13817105109909703444157221 2590707208108069395779479)
          ·
            refine ⟨3886060812162104093669219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590707208108069395779479 3886060812162104093669219)
            ·
              refine ⟨5829091218243156140503829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886060812162104093669219 5829091218243156140503829)
              ·
                refine ⟨273238650855147944086117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5829091218243156140503829 273238650855147944086117)
                ·
                  refine ⟨51232247035340239516147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273238650855147944086117 51232247035340239516147)
                  ·
                    rfl

theorem cell22_448985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_448985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448985 prefixEnd_448985 := by exact prefixLift 448985
  have htrace : WordTrace (prefixWord ++ tailWord_448985) baseStart_448985 baseEnd_448985 := by
    simpa [prefixWord, tailWord_448985, baseEnd_448985] using wordTrace_append hprefix tailTrace_448985
  have hstable : (prefixWord ++ tailWord_448985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448985).length < 2 ^ (prefixWord ++ tailWord_448985).sum := by decide
  have hdescent : baseEnd_448985 < baseStart_448985 := by decide
  rcases family_descends (prefixWord ++ tailWord_448985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449000 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_449000 : Nat := 118140960795 + 449000 * 2 ^ 59
def prefixEnd_449000 : Nat := 4983230072969 + 3 ^ 40 * 449000 * 2
def baseEnd_449000 : Nat := 153701875912565679423395

theorem tailTrace_449000 : CollatzResearch.WordTrace tailWord_449000 prefixEnd_449000 153701875912565679423395 := by
  unfold tailWord_449000
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188187686678578970028227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10917583582238105293370969 8188187686678578970028227)
  ·
    refine ⟨12282281530017868455042341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8188187686678578970028227 12282281530017868455042341)
    ·
      refine ⟨2302927786878350335320439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12282281530017868455042341 2302927786878350335320439)
      ·
        refine ⟨3454391680317525502980659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302927786878350335320439 3454391680317525502980659)
        ·
          refine ⟨5181587520476288254470989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3454391680317525502980659 5181587520476288254470989)
          ·
            refine ⟨1943095320178608095426621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5181587520476288254470989 1943095320178608095426621)
            ·
              refine ⟨728660745066978035784983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1943095320178608095426621 728660745066978035784983)
              ·
                refine ⟨1092991117600467053677475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728660745066978035784983 1092991117600467053677475)
                ·
                  refine ⟨1639486676400700580516213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092991117600467053677475 1639486676400700580516213)
                  ·
                    refine ⟨153701875912565679423395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1639486676400700580516213 153701875912565679423395)
                    ·
                      rfl

theorem cell22_449000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_449000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449000 prefixEnd_449000 := by exact prefixLift 449000
  have htrace : WordTrace (prefixWord ++ tailWord_449000) baseStart_449000 baseEnd_449000 := by
    simpa [prefixWord, tailWord_449000, baseEnd_449000] using wordTrace_append hprefix tailTrace_449000
  have hstable : (prefixWord ++ tailWord_449000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449000).length < 2 ^ (prefixWord ++ tailWord_449000).sum := by decide
  have hdescent : baseEnd_449000 < baseStart_449000 := by decide
  rcases family_descends (prefixWord ++ tailWord_449000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449043 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 2, 6]
def baseStart_449043 : Nat := 118140960795 + 449043 * 2 ^ 59
def prefixEnd_449043 : Nat := 4983230072969 + 3 ^ 40 * 449043 * 2
def baseEnd_449043 : Nat := 153716595691327900598263

theorem tailTrace_449043 : CollatzResearch.WordTrace tailWord_449043 prefixEnd_449043 153716595691327900598263 := by
  unfold tailWord_449043
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377943712201376283871783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10918629141467584189247855 16377943712201376283871783)
  ·
    refine ⟨24566915568302064425807675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16377943712201376283871783 24566915568302064425807675)
    ·
      refine ⟨36850373352453096638711513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24566915568302064425807675 36850373352453096638711513)
      ·
        refine ⟨27637780014339822479033635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36850373352453096638711513 27637780014339822479033635)
        ·
          refine ⟨41456670021509733718550453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27637780014339822479033635 41456670021509733718550453)
          ·
            refine ⟨3886562814516537536114105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41456670021509733718550453 3886562814516537536114105)
            ·
              refine ⟨2914922110887403152085579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886562814516537536114105 2914922110887403152085579)
              ·
                refine ⟨4372383166331104728128369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914922110887403152085579 4372383166331104728128369)
                ·
                  refine ⟨3279287374748328546096277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4372383166331104728128369 3279287374748328546096277)
                  ·
                    refine ⟨153716595691327900598263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3279287374748328546096277 153716595691327900598263)
                    ·
                      rfl

theorem cell22_449043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_449043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449043 prefixEnd_449043 := by exact prefixLift 449043
  have htrace : WordTrace (prefixWord ++ tailWord_449043) baseStart_449043 baseEnd_449043 := by
    simpa [prefixWord, tailWord_449043, baseEnd_449043] using wordTrace_append hprefix tailTrace_449043
  have hstable : (prefixWord ++ tailWord_449043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449043).length < 2 ^ (prefixWord ++ tailWord_449043).sum := by decide
  have hdescent : baseEnd_449043 < baseStart_449043 := by decide
  rcases family_descends (prefixWord ++ tailWord_449043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449047 : List Nat := [1, 1, 3, 6, 1, 1, 2, 7]
def baseStart_449047 : Nat := 118140960795 + 449047 * 2 ^ 59
def prefixEnd_449047 : Nat := 4983230072969 + 3 ^ 40 * 449047 * 2
def baseEnd_449047 : Nat := 17079773885897024833139

theorem tailTrace_449047 : CollatzResearch.WordTrace tailWord_449047 prefixEnd_449047 17079773885897024833139 := by
  unfold tailWord_449047
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378089604186884967017395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10918726402791256644678263 16378089604186884967017395)
  ·
    refine ⟨24567134406280327450526093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16378089604186884967017395 24567134406280327450526093)
    ·
      refine ⟨9212675402355122793947285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24567134406280327450526093 9212675402355122793947285)
      ·
        refine ⟨431844159485396380966279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9212675402355122793947285 431844159485396380966279)
        ·
          refine ⟨647766239228094571449419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431844159485396380966279 647766239228094571449419)
          ·
            refine ⟨971649358842141857174129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647766239228094571449419 971649358842141857174129)
            ·
              refine ⟨728737019131606392880597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971649358842141857174129 728737019131606392880597)
              ·
                refine ⟨17079773885897024833139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 728737019131606392880597 17079773885897024833139)
                ·
                  rfl

theorem cell22_449047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 7].length) (baseStart_449047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449047 prefixEnd_449047 := by exact prefixLift 449047
  have htrace : WordTrace (prefixWord ++ tailWord_449047) baseStart_449047 baseEnd_449047 := by
    simpa [prefixWord, tailWord_449047, baseEnd_449047] using wordTrace_append hprefix tailTrace_449047
  have hstable : (prefixWord ++ tailWord_449047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449047).length < 2 ^ (prefixWord ++ tailWord_449047).sum := by decide
  have hdescent : baseEnd_449047 < baseStart_449047 := by decide
  rcases family_descends (prefixWord ++ tailWord_449047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449105 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_449105 : Nat := 118140960795 + 449105 * 2 ^ 59
def prefixEnd_449105 : Nat := 4983230072969 + 3 ^ 40 * 449105 * 2
def baseEnd_449105 : Nat := 153737819558380405548073

theorem tailTrace_449105 : CollatzResearch.WordTrace tailWord_449105 prefixEnd_449105 153737819558380405548073 := by
  unfold tailWord_449105
  simp only [CollatzResearch.WordTrace]
  refine ⟨16380205037976760872628769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10920136691984507248419179 16380205037976760872628769)
  ·
    refine ⟨12285153778482570654471577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16380205037976760872628769 12285153778482570654471577)
    ·
      refine ⟨9213865333861927990853683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12285153778482570654471577 9213865333861927990853683)
      ·
        refine ⟨13820798000792891986280525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9213865333861927990853683 13820798000792891986280525)
        ·
          refine ⟨5182799250297334494855197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13820798000792891986280525 5182799250297334494855197)
          ·
            refine ⟨1943549718861500435570699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5182799250297334494855197 1943549718861500435570699)
            ·
              refine ⟨2915324578292250653356049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943549718861500435570699 2915324578292250653356049)
              ·
                refine ⟨2186493433719187990017037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915324578292250653356049 2186493433719187990017037)
                ·
                  refine ⟨819935037644695496256389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2186493433719187990017037 819935037644695496256389)
                  ·
                    refine ⟨153737819558380405548073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819935037644695496256389 153737819558380405548073)
                    ·
                      rfl

theorem cell22_449105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_449105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449105 prefixEnd_449105 := by exact prefixLift 449105
  have htrace : WordTrace (prefixWord ++ tailWord_449105) baseStart_449105 baseEnd_449105 := by
    simpa [prefixWord, tailWord_449105, baseEnd_449105] using wordTrace_append hprefix tailTrace_449105
  have hstable : (prefixWord ++ tailWord_449105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449105).length < 2 ^ (prefixWord ++ tailWord_449105).sum := by decide
  have hdescent : baseEnd_449105 < baseStart_449105 := by decide
  rcases family_descends (prefixWord ++ tailWord_449105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449135 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 1, 5]
def baseStart_449135 : Nat := 118140960795 + 449135 * 2 ^ 59
def prefixEnd_449135 : Nat := 4983230072969 + 3 ^ 40 * 449135 * 2
def baseEnd_449135 : Nat := 153748089171470327297981

theorem tailTrace_449135 : CollatzResearch.WordTrace tailWord_449135 prefixEnd_449135 153748089171470327297981 := by
  unfold tailWord_449135
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381299227868075996220859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10920866151912050664147239 16381299227868075996220859)
  ·
    refine ⟨24571948841802113994331289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16381299227868075996220859 24571948841802113994331289)
    ·
      refine ⟨18428961631351585495748467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24571948841802113994331289 18428961631351585495748467)
      ·
        refine ⟨27643442447027378243622701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18428961631351585495748467 27643442447027378243622701)
        ·
          refine ⟨10366290917635266841358513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27643442447027378243622701 10366290917635266841358513)
          ·
            refine ⟨7774718188226450131018885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10366290917635266841358513 7774718188226450131018885)
            ·
              refine ⟨1457759660292459399566041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7774718188226450131018885 1457759660292459399566041)
              ·
                refine ⟨1093319745219344549674531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457759660292459399566041 1093319745219344549674531)
                ·
                  refine ⟨1639979617829016824511797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093319745219344549674531 1639979617829016824511797)
                  ·
                    refine ⟨153748089171470327297981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1639979617829016824511797 153748089171470327297981)
                    ·
                      rfl

theorem cell22_449135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_449135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449135 prefixEnd_449135 := by exact prefixLift 449135
  have htrace : WordTrace (prefixWord ++ tailWord_449135) baseStart_449135 baseEnd_449135 := by
    simpa [prefixWord, tailWord_449135, baseEnd_449135] using wordTrace_append hprefix tailTrace_449135
  have hstable : (prefixWord ++ tailWord_449135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449135).length < 2 ^ (prefixWord ++ tailWord_449135).sum := by decide
  have hdescent : baseEnd_449135 < baseStart_449135 := by decide
  rcases family_descends (prefixWord ++ tailWord_449135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449152 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 4, 3]
def baseStart_449152 : Nat := 118140960795 + 449152 * 2 ^ 59
def prefixEnd_449152 : Nat := 4983230072969 + 3 ^ 40 * 449152 * 2
def baseEnd_449152 : Nat := 153753908618887949622929

theorem tailTrace_449152 : CollatzResearch.WordTrace tailWord_449152 prefixEnd_449152 153753908618887949622929 := by
  unfold tailWord_449152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8190959634403243949794855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10921279512537658599726473 8190959634403243949794855)
  ·
    refine ⟨12286439451604865924692283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8190959634403243949794855 12286439451604865924692283)
    ·
      refine ⟨18429659177407298887038425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12286439451604865924692283 18429659177407298887038425)
      ·
        refine ⟨13822244383055474165278819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18429659177407298887038425 13822244383055474165278819)
        ·
          refine ⟨20733366574583211247918229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13822244383055474165278819 20733366574583211247918229)
          ·
            refine ⟨971876558183588027246167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20733366574583211247918229 971876558183588027246167)
            ·
              refine ⟨1457814837275382040869251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971876558183588027246167 1457814837275382040869251)
              ·
                refine ⟨2186722255913073061303877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457814837275382040869251 2186722255913073061303877)
                ·
                  refine ⟨410010422983701198994477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2186722255913073061303877 410010422983701198994477)
                  ·
                    refine ⟨153753908618887949622929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 410010422983701198994477 153753908618887949622929)
                    ·
                      rfl

theorem cell22_449152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_449152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449152 prefixEnd_449152 := by exact prefixLift 449152
  have htrace : WordTrace (prefixWord ++ tailWord_449152) baseStart_449152 baseEnd_449152 := by
    simpa [prefixWord, tailWord_449152, baseEnd_449152] using wordTrace_append hprefix tailTrace_449152
  have hstable : (prefixWord ++ tailWord_449152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449152).length < 2 ^ (prefixWord ++ tailWord_449152).sum := by decide
  have hdescent : baseEnd_449152 < baseStart_449152 := by decide
  rcases family_descends (prefixWord ++ tailWord_449152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449182 : List Nat := [4, 3, 1, 1, 1, 1, 3, 8]
def baseStart_449182 : Nat := 118140960795 + 449182 * 2 ^ 59
def prefixEnd_449182 : Nat := 4983230072969 + 3 ^ 40 * 449182 * 2
def baseEnd_449182 : Nat := 17084908692441985708093

theorem tailTrace_449182 : CollatzResearch.WordTrace tailWord_449182 prefixEnd_449182 17084908692441985708093 := by
  unfold tailWord_449182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047876682337225377897725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10922008972465202015454533 2047876682337225377897725)
  ·
    refine ⟨767953755876459516711647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2047876682337225377897725 767953755876459516711647)
    ·
      refine ⟨1151930633814689275067471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767953755876459516711647 1151930633814689275067471)
      ·
        refine ⟨1727895950722033912601207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151930633814689275067471 1727895950722033912601207)
        ·
          refine ⟨2591843926083050868901811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727895950722033912601207 2591843926083050868901811)
          ·
            refine ⟨3887765889124576303352717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591843926083050868901811 3887765889124576303352717)
            ·
              refine ⟨1457912208421716113757269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3887765889124576303352717 1457912208421716113757269)
              ·
                refine ⟨17084908692441985708093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1457912208421716113757269 17084908692441985708093)
                ·
                  rfl

theorem cell22_449182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_449182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449182 prefixEnd_449182 := by exact prefixLift 449182
  have htrace : WordTrace (prefixWord ++ tailWord_449182) baseStart_449182 baseEnd_449182 := by
    simpa [prefixWord, tailWord_449182, baseEnd_449182] using wordTrace_append hprefix tailTrace_449182
  have hstable : (prefixWord ++ tailWord_449182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449182).length < 2 ^ (prefixWord ++ tailWord_449182).sum := by decide
  have hdescent : baseEnd_449182 < baseStart_449182 := by decide
  rcases family_descends (prefixWord ++ tailWord_449182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449210 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_449210 : Nat := 118140960795 + 449210 * 2 ^ 59
def prefixEnd_449210 : Nat := 4983230072969 + 3 ^ 40 * 449210 * 2
def baseEnd_449210 : Nat := 51257921068065043890917

theorem tailTrace_449210 : CollatzResearch.WordTrace tailWord_449210 prefixEnd_449210 51257921068065043890917 := by
  unfold tailWord_449210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096008675649090951300271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10922689801730909203467389 4096008675649090951300271)
  ·
    refine ⟨6144013013473636426950407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4096008675649090951300271 6144013013473636426950407)
    ·
      refine ⟨9216019520210454640425611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6144013013473636426950407 9216019520210454640425611)
      ·
        refine ⟨13824029280315681960638417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9216019520210454640425611 13824029280315681960638417)
        ·
          refine ⟨10368021960236761470478813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13824029280315681960638417 10368021960236761470478813)
          ·
            refine ⟨3888008235088785551429555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10368021960236761470478813 3888008235088785551429555)
            ·
              refine ⟨5832012352633178327144333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888008235088785551429555 5832012352633178327144333)
              ·
                refine ⟨2187004632237441872679125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5832012352633178327144333 2187004632237441872679125)
                ·
                  refine ⟨51257921068065043890917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2187004632237441872679125 51257921068065043890917)
                  ·
                    rfl

theorem cell22_449210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_449210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449210 prefixEnd_449210 := by exact prefixLift 449210
  have htrace : WordTrace (prefixWord ++ tailWord_449210) baseStart_449210 baseEnd_449210 := by
    simpa [prefixWord, tailWord_449210, baseEnd_449210] using wordTrace_append hprefix tailTrace_449210
  have hstable : (prefixWord ++ tailWord_449210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449210).length < 2 ^ (prefixWord ++ tailWord_449210).sum := by decide
  have hdescent : baseEnd_449210 < baseStart_449210 := by decide
  rcases family_descends (prefixWord ++ tailWord_449210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449257 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_449257 : Nat := 118140960795 + 449257 * 2 ^ 59
def prefixEnd_449257 : Nat := 4983230072969 + 3 ^ 40 * 449257 * 2
def baseEnd_449257 : Nat := 153789852264702675747607

theorem tailTrace_449257 : CollatzResearch.WordTrace tailWord_449257 prefixEnd_449257 153789852264702675747607 := by
  unfold tailWord_449257
  simp only [CollatzResearch.WordTrace]
  refine ⟨16385748933426090832162025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10923832622284060554774683 16385748933426090832162025)
  ·
    refine ⟨12289311700069568124121519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16385748933426090832162025 12289311700069568124121519)
    ·
      refine ⟨18433967550104352186182279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12289311700069568124121519 18433967550104352186182279)
      ·
        refine ⟨27650951325156528279273419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18433967550104352186182279 27650951325156528279273419)
        ·
          refine ⟨41476426987734792418910129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27650951325156528279273419 41476426987734792418910129)
          ·
            refine ⟨31107320240801094314182597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41476426987734792418910129 31107320240801094314182597)
            ·
              refine ⟨5832622545150205183909237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31107320240801094314182597 5832622545150205183909237)
              ·
                refine ⟨546808363607831735991491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5832622545150205183909237 546808363607831735991491)
                ·
                  refine ⟨820212545411747603987237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546808363607831735991491 820212545411747603987237)
                  ·
                    refine ⟨153789852264702675747607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 820212545411747603987237 153789852264702675747607)
                    ·
                      rfl

theorem cell22_449257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_449257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449257 prefixEnd_449257 := by exact prefixLift 449257
  have htrace : WordTrace (prefixWord ++ tailWord_449257) baseStart_449257 baseEnd_449257 := by
    simpa [prefixWord, tailWord_449257, baseEnd_449257] using wordTrace_append hprefix tailTrace_449257
  have hstable : (prefixWord ++ tailWord_449257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449257).length < 2 ^ (prefixWord ++ tailWord_449257).sum := by decide
  have hdescent : baseEnd_449257 < baseStart_449257 := by decide
  rcases family_descends (prefixWord ++ tailWord_449257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449338 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_449338 : Nat := 118140960795 + 449338 * 2 ^ 59
def prefixEnd_449338 : Nat := 4983230072969 + 3 ^ 40 * 449338 * 2
def baseEnd_449338 : Nat := 153817580220045464472359

theorem tailTrace_449338 : CollatzResearch.WordTrace tailWord_449338 prefixEnd_449338 153817580220045464472359 := by
  unfold tailWord_449338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097175811533160416465167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10925802164088427777240445 4097175811533160416465167)
  ·
    refine ⟨6145763717299740624697751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4097175811533160416465167 6145763717299740624697751)
    ·
      refine ⟨9218645575949610937046627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145763717299740624697751 9218645575949610937046627)
      ·
        refine ⟨13827968363924416405569941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9218645575949610937046627 13827968363924416405569941)
        ·
          refine ⟨648186017058957019011091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13827968363924416405569941 648186017058957019011091)
          ·
            refine ⟨972279025588435528516637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648186017058957019011091 972279025588435528516637)
            ·
              refine ⟨364604634595663323193739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 972279025588435528516637 364604634595663323193739)
              ·
                refine ⟨546906951893494984790609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364604634595663323193739 546906951893494984790609)
                ·
                  refine ⟨410180213920121238592957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546906951893494984790609 410180213920121238592957)
                  ·
                    refine ⟨153817580220045464472359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 410180213920121238592957 153817580220045464472359)
                    ·
                      rfl

theorem cell22_449338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_449338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449338 prefixEnd_449338 := by exact prefixLift 449338
  have htrace : WordTrace (prefixWord ++ tailWord_449338) baseStart_449338 baseEnd_449338 := by
    simpa [prefixWord, tailWord_449338, baseEnd_449338] using wordTrace_append hprefix tailTrace_449338
  have hstable : (prefixWord ++ tailWord_449338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449338).length < 2 ^ (prefixWord ++ tailWord_449338).sum := by decide
  have hdescent : baseEnd_449338 < baseStart_449338 := by decide
  rcases family_descends (prefixWord ++ tailWord_449338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449362 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_449362 : Nat := 118140960795 + 449362 * 2 ^ 59
def prefixEnd_449362 : Nat := 4983230072969 + 3 ^ 40 * 449362 * 2
def baseEnd_449362 : Nat := 51275265303505800624095

theorem tailTrace_449362 : CollatzResearch.WordTrace tailWord_449362 prefixEnd_449362 51275265303505800624095 := by
  unfold tailWord_449362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097394649511423441183585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10926385732030462509822893 4097394649511423441183585)
  ·
    refine ⟨3073045987133567580887689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4097394649511423441183585 3073045987133567580887689)
    ·
      refine ⟨2304784490350175685665767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3073045987133567580887689 2304784490350175685665767)
      ·
        refine ⟨3457176735525263528498651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304784490350175685665767 3457176735525263528498651)
        ·
          refine ⟨5185765103287895292747977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457176735525263528498651 5185765103287895292747977)
          ·
            refine ⟨3889323827465921469560983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185765103287895292747977 3889323827465921469560983)
            ·
              refine ⟨5833985741198882204341475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889323827465921469560983 5833985741198882204341475)
              ·
                refine ⟨8750978611798323306512213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833985741198882204341475 8750978611798323306512213)
                ·
                  refine ⟨51275265303505800624095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8750978611798323306512213 51275265303505800624095)
                  ·
                    rfl

theorem cell22_449362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_449362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449362 prefixEnd_449362 := by exact prefixLift 449362
  have htrace : WordTrace (prefixWord ++ tailWord_449362) baseStart_449362 baseEnd_449362 := by
    simpa [prefixWord, tailWord_449362, baseEnd_449362] using wordTrace_append hprefix tailTrace_449362
  have hstable : (prefixWord ++ tailWord_449362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449362).length < 2 ^ (prefixWord ++ tailWord_449362).sum := by decide
  have hdescent : baseEnd_449362 < baseStart_449362 := by decide
  rcases family_descends (prefixWord ++ tailWord_449362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449377 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_449377 : Nat := 118140960795 + 449377 * 2 ^ 59
def prefixEnd_449377 : Nat := 4983230072969 + 3 ^ 40 * 449377 * 2
def baseEnd_449377 : Nat := 153830930717062362747239

theorem tailTrace_449377 : CollatzResearch.WordTrace tailWord_449377 prefixEnd_449377 153830930717062362747239 := by
  unfold tailWord_449377
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390125692991351326530385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10926750461994234217686923 16390125692991351326530385)
  ·
    refine ⟨12292594269743513494897789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16390125692991351326530385 12292594269743513494897789)
    ·
      refine ⟨4609722851153817560586671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12292594269743513494897789 4609722851153817560586671)
      ·
        refine ⟨6914584276730726340880007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609722851153817560586671 6914584276730726340880007)
        ·
          refine ⟨10371876415096089511320011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6914584276730726340880007 10371876415096089511320011)
          ·
            refine ⟨15557814622644134266980017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10371876415096089511320011 15557814622644134266980017)
            ·
              refine ⟨11668360966983100700235013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15557814622644134266980017 11668360966983100700235013)
              ·
                refine ⟨2187817681309331381294065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11668360966983100700235013 2187817681309331381294065)
                ·
                  refine ⟨1640863260981998535970549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2187817681309331381294065 1640863260981998535970549)
                  ·
                    refine ⟨153830930717062362747239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1640863260981998535970549 153830930717062362747239)
                    ·
                      rfl

theorem cell22_449377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_449377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449377 prefixEnd_449377 := by exact prefixLift 449377
  have htrace : WordTrace (prefixWord ++ tailWord_449377) baseStart_449377 baseEnd_449377 := by
    simpa [prefixWord, tailWord_449377, baseEnd_449377] using wordTrace_append hprefix tailTrace_449377
  have hstable : (prefixWord ++ tailWord_449377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449377).length < 2 ^ (prefixWord ++ tailWord_449377).sum := by decide
  have hdescent : baseEnd_449377 < baseStart_449377 := by decide
  rcases family_descends (prefixWord ++ tailWord_449377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449407 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 6]
def baseStart_449407 : Nat := 118140960795 + 449407 * 2 ^ 59
def prefixEnd_449407 : Nat := 4983230072969 + 3 ^ 40 * 449407 * 2
def baseEnd_449407 : Nat := 51280400110050761499049

theorem tailTrace_449407 : CollatzResearch.WordTrace tailWord_449407 prefixEnd_449407 51280400110050761499049 := by
  unfold tailWord_449407
  simp only [CollatzResearch.WordTrace]
  refine ⟨16391219882882666450122475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10927479921921777633414983 16391219882882666450122475)
  ·
    refine ⟨24586829824323999675183713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16391219882882666450122475 24586829824323999675183713)
    ·
      refine ⟨18440122368242999756387785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24586829824323999675183713 18440122368242999756387785)
      ·
        refine ⟨13830091776182249817290839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18440122368242999756387785 13830091776182249817290839)
        ·
          refine ⟨20745137664273374725936259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13830091776182249817290839 20745137664273374725936259)
          ·
            refine ⟨31117706496410062088904389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20745137664273374725936259 31117706496410062088904389)
            ·
              refine ⟨5834569968076886641669573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31117706496410062088904389 5834569968076886641669573)
              ·
                refine ⟨1093981869014416245313045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5834569968076886641669573 1093981869014416245313045)
                ·
                  refine ⟨51280400110050761499049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1093981869014416245313045 51280400110050761499049)
                  ·
                    rfl

theorem cell22_449407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 6].length) (baseStart_449407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449407 prefixEnd_449407 := by exact prefixLift 449407
  have htrace : WordTrace (prefixWord ++ tailWord_449407) baseStart_449407 baseEnd_449407 := by
    simpa [prefixWord, tailWord_449407, baseEnd_449407] using wordTrace_append hprefix tailTrace_449407
  have hstable : (prefixWord ++ tailWord_449407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449407).length < 2 ^ (prefixWord ++ tailWord_449407).sum := by decide
  have hdescent : baseEnd_449407 < baseStart_449407 := by decide
  rcases family_descends (prefixWord ++ tailWord_449407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449430 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_449430 : Nat := 118140960795 + 449430 * 2 ^ 59
def prefixEnd_449430 : Nat := 4983230072969 + 3 ^ 40 * 449430 * 2
def baseEnd_449430 : Nat := 51283024566729297057359

theorem tailTrace_449430 : CollatzResearch.WordTrace tailWord_449430 prefixEnd_449430 51283024566729297057359 := by
  unfold tailWord_449430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1024503672612458836138109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10928039174532894252139829 1024503672612458836138109)
  ·
    refine ⟨384188877229672063551791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1024503672612458836138109 384188877229672063551791)
    ·
      refine ⟨576283315844508095327687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384188877229672063551791 576283315844508095327687)
      ·
        refine ⟨864424973766762142991531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576283315844508095327687 864424973766762142991531)
        ·
          refine ⟨1296637460650143214487297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864424973766762142991531 1296637460650143214487297)
          ·
            refine ⟨972478095487607410865473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1296637460650143214487297 972478095487607410865473)
            ·
              refine ⟨729358571615705558149105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972478095487607410865473 729358571615705558149105)
              ·
                refine ⟨547018928711779168611829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729358571615705558149105 547018928711779168611829)
                ·
                  refine ⟨51283024566729297057359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 547018928711779168611829 51283024566729297057359)
                  ·
                    rfl

theorem cell22_449430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_449430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449430 prefixEnd_449430 := by exact prefixLift 449430
  have htrace : WordTrace (prefixWord ++ tailWord_449430) baseStart_449430 baseEnd_449430 := by
    simpa [prefixWord, tailWord_449430, baseEnd_449430] using wordTrace_append hprefix tailTrace_449430
  have hstable : (prefixWord ++ tailWord_449430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449430).length < 2 ^ (prefixWord ++ tailWord_449430).sum := by decide
  have hdescent : baseEnd_449430 < baseStart_449430 := by decide
  rcases family_descends (prefixWord ++ tailWord_449430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449490 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_449490 : Nat := 118140960795 + 449490 * 2 ^ 59
def prefixEnd_449490 : Nat := 4983230072969 + 3 ^ 40 * 449490 * 2
def baseEnd_449490 : Nat := 153869612926367734671893

theorem tailTrace_449490 : CollatzResearch.WordTrace tailWord_449490 prefixEnd_449490 153869612926367734671893 := by
  unfold tailWord_449490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098561785395492906348481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10929498094387981083595949 4098561785395492906348481)
  ·
    refine ⟨3073921339046619679761361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4098561785395492906348481 3073921339046619679761361)
    ·
      refine ⟨2305441004284964759821021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3073921339046619679761361 2305441004284964759821021)
      ·
        refine ⟨864540376606861784932883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2305441004284964759821021 864540376606861784932883)
        ·
          refine ⟨1296810564910292677399325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864540376606861784932883 1296810564910292677399325)
          ·
            refine ⟨486303961841359754024747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1296810564910292677399325 486303961841359754024747)
            ·
              refine ⟨729455942762039631037121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486303961841359754024747 729455942762039631037121)
              ·
                refine ⟨547091957071529723277841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729455942762039631037121 547091957071529723277841)
                ·
                  refine ⟨410318967803647292458381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547091957071529723277841 410318967803647292458381)
                  ·
                    refine ⟨153869612926367734671893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 410318967803647292458381 153869612926367734671893)
                    ·
                      rfl

theorem cell22_449490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_449490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449490 prefixEnd_449490 := by exact prefixLift 449490
  have htrace : WordTrace (prefixWord ++ tailWord_449490) baseStart_449490 baseEnd_449490 := by
    simpa [prefixWord, tailWord_449490, baseEnd_449490] using wordTrace_append hprefix tailTrace_449490
  have hstable : (prefixWord ++ tailWord_449490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449490).length < 2 ^ (prefixWord ++ tailWord_449490).sum := by decide
  have hdescent : baseEnd_449490 < baseStart_449490 := by decide
  rcases family_descends (prefixWord ++ tailWord_449490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449565 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 5]
def baseStart_449565 : Nat := 118140960795 + 449565 * 2 ^ 59
def prefixEnd_449565 : Nat := 4983230072969 + 3 ^ 40 * 449565 * 2
def baseEnd_449565 : Nat := 51298428986364179682221

theorem tailTrace_449565 : CollatzResearch.WordTrace tailWord_449565 prefixEnd_449565 51298428986364179682221 := by
  unfold tailWord_449565
  simp only [CollatzResearch.WordTrace]
  refine ⟨16396982616310259434374149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10931321744206839622916099 16396982616310259434374149)
  ·
    refine ⟨3074434240558173643945153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16396982616310259434374149 3074434240558173643945153)
    ·
      refine ⟨2305825680418630232958865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3074434240558173643945153 2305825680418630232958865)
      ·
        refine ⟨1729369260313972674719149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2305825680418630232958865 1729369260313972674719149)
        ·
          refine ⟨648513472617739753019681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1729369260313972674719149 648513472617739753019681)
          ·
            refine ⟨486385104463304814764761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648513472617739753019681 486385104463304814764761)
            ·
              refine ⟨364788828347478611073571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486385104463304814764761 364788828347478611073571)
              ·
                refine ⟨547183242521217916610357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364788828347478611073571 547183242521217916610357)
                ·
                  refine ⟨51298428986364179682221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 547183242521217916610357 51298428986364179682221)
                  ·
                    rfl

theorem cell22_449565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_449565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449565 prefixEnd_449565 := by exact prefixLift 449565
  have htrace : WordTrace (prefixWord ++ tailWord_449565) baseStart_449565 baseEnd_449565 := by
    simpa [prefixWord, tailWord_449565, baseEnd_449565] using wordTrace_append hprefix tailTrace_449565
  have hstable : (prefixWord ++ tailWord_449565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449565).length < 2 ^ (prefixWord ++ tailWord_449565).sum := by decide
  have hdescent : baseEnd_449565 < baseStart_449565 := by decide
  rcases family_descends (prefixWord ++ tailWord_449565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449578 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_449578 : Nat := 118140960795 + 449578 * 2 ^ 59
def prefixEnd_449578 : Nat := 4983230072969 + 3 ^ 40 * 449578 * 2
def baseEnd_449578 : Nat := 153899737124764838471623

theorem tailTrace_449578 : CollatzResearch.WordTrace tailWord_449578 prefixEnd_449578 153899737124764838471623 := by
  unfold tailWord_449578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099364191315790663649347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10931637843508775103064925 4099364191315790663649347)
  ·
    refine ⟨6149046286973685995474021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4099364191315790663649347 6149046286973685995474021)
    ·
      refine ⟨1152946178807566124151379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6149046286973685995474021 1152946178807566124151379)
      ·
        refine ⟨1729419268211349186227069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152946178807566124151379 1729419268211349186227069)
        ·
          refine ⟨648532225579255944835151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1729419268211349186227069 648532225579255944835151)
          ·
            refine ⟨972798338368883917252727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648532225579255944835151 972798338368883917252727)
            ·
              refine ⟨1459197507553325875879091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972798338368883917252727 1459197507553325875879091)
              ·
                refine ⟨2188796261329988813818637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459197507553325875879091 2188796261329988813818637)
                ·
                  refine ⟨820798597998745805181989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2188796261329988813818637 820798597998745805181989)
                  ·
                    refine ⟨153899737124764838471623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 820798597998745805181989 153899737124764838471623)
                    ·
                      rfl

theorem cell22_449578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_449578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449578 prefixEnd_449578 := by exact prefixLift 449578
  have htrace : WordTrace (prefixWord ++ tailWord_449578) baseStart_449578 baseEnd_449578 := by
    simpa [prefixWord, tailWord_449578, baseEnd_449578] using wordTrace_append hprefix tailTrace_449578
  have hstable : (prefixWord ++ tailWord_449578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449578).length < 2 ^ (prefixWord ++ tailWord_449578).sum := by decide
  have hdescent : baseEnd_449578 < baseStart_449578 := by decide
  rcases family_descends (prefixWord ++ tailWord_449578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449608 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 2, 3]
def baseStart_449608 : Nat := 118140960795 + 449608 * 2 ^ 59
def prefixEnd_449608 : Nat := 4983230072969 + 3 ^ 40 * 449608 * 2
def baseEnd_449608 : Nat := 153910006737854760221531

theorem tailTrace_449608 : CollatzResearch.WordTrace tailWord_449608 prefixEnd_449608 153910006737854760221531 := by
  unfold tailWord_449608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8199275477577238889094739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10932367303436318518792985 8199275477577238889094739)
  ·
    refine ⟨12298913216365858333642109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8199275477577238889094739 12298913216365858333642109)
    ·
      refine ⟨4612092456137196875115791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12298913216365858333642109 4612092456137196875115791)
      ·
        refine ⟨6918138684205795312673687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612092456137196875115791 6918138684205795312673687)
        ·
          refine ⟨10377208026308692969010531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6918138684205795312673687 10377208026308692969010531)
          ·
            refine ⟨15565812039463039453515797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10377208026308692969010531 15565812039463039453515797)
            ·
              refine ⟨729647439349829974383553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15565812039463039453515797 729647439349829974383553)
              ·
                refine ⟨547235579512372480787665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729647439349829974383553 547235579512372480787665)
                ·
                  refine ⟨410426684634279360590749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547235579512372480787665 410426684634279360590749)
                  ·
                    refine ⟨153910006737854760221531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 410426684634279360590749 153910006737854760221531)
                    ·
                      rfl

theorem cell22_449608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_449608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449608 prefixEnd_449608 := by exact prefixLift 449608
  have htrace : WordTrace (prefixWord ++ tailWord_449608) baseStart_449608 baseEnd_449608 := by
    simpa [prefixWord, tailWord_449608, baseEnd_449608] using wordTrace_append hprefix tailTrace_449608
  have hstable : (prefixWord ++ tailWord_449608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449608).length < 2 ^ (prefixWord ++ tailWord_449608).sum := by decide
  have hdescent : baseEnd_449608 < baseStart_449608 := by decide
  rcases family_descends (prefixWord ++ tailWord_449608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449734 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_449734 : Nat := 118140960795 + 449734 * 2 ^ 59
def prefixEnd_449734 : Nat := 4983230072969 + 3 ^ 40 * 449734 * 2
def baseEnd_449734 : Nat := 51317713037610810523715

theorem tailTrace_449734 : CollatzResearch.WordTrace tailWord_449734 prefixEnd_449734 51317713037610810523715 := by
  unfold tailWord_449734
  simp only [CollatzResearch.WordTrace]
  refine ⟨512598329771812540539883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10935431035132000864850837 512598329771812540539883)
  ·
    refine ⟨768897494657718810809825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 512598329771812540539883 768897494657718810809825)
    ·
      refine ⟨576673120993289108107369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 768897494657718810809825 576673120993289108107369)
      ·
        refine ⟨432504840744966831080527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576673120993289108107369 432504840744966831080527)
        ·
          refine ⟨648757261117450246620791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432504840744966831080527 648757261117450246620791)
          ·
            refine ⟨973135891676175369931187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648757261117450246620791 973135891676175369931187)
            ·
              refine ⟨1459703837514263054896781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973135891676175369931187 1459703837514263054896781)
              ·
                refine ⟨547388939067848645586293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459703837514263054896781 547388939067848645586293)
                ·
                  refine ⟨51317713037610810523715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 547388939067848645586293 51317713037610810523715)
                  ·
                    rfl

theorem cell22_449734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_449734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449734 prefixEnd_449734 := by exact prefixLift 449734
  have htrace : WordTrace (prefixWord ++ tailWord_449734) baseStart_449734 baseEnd_449734 := by
    simpa [prefixWord, tailWord_449734, baseEnd_449734] using wordTrace_append hprefix tailTrace_449734
  have hstable : (prefixWord ++ tailWord_449734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449734).length < 2 ^ (prefixWord ++ tailWord_449734).sum := by decide
  have hdescent : baseEnd_449734 < baseStart_449734 := by decide
  rcases family_descends (prefixWord ++ tailWord_449734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449786 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_449786 : Nat := 118140960795 + 449786 * 2 ^ 59
def prefixEnd_449786 : Nat := 4983230072969 + 3 ^ 40 * 449786 * 2
def baseEnd_449786 : Nat := 153970939775521629270985

theorem tailTrace_449786 : CollatzResearch.WordTrace tailWord_449786 prefixEnd_449786 153970939775521629270985 := by
  unfold tailWord_449786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101260787127403544542303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10936695432339742785446141 4101260787127403544542303)
  ·
    refine ⟨6151891180691105316813455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4101260787127403544542303 6151891180691105316813455)
    ·
      refine ⟨9227836771036657975220183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6151891180691105316813455 9227836771036657975220183)
      ·
        refine ⟨13841755156554986962830275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227836771036657975220183 13841755156554986962830275)
        ·
          refine ⟨20762632734832480444245413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13841755156554986962830275 20762632734832480444245413)
          ·
            refine ⟨3892993637781090083296015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20762632734832480444245413 3892993637781090083296015)
            ·
              refine ⟨5839490456671635124944023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892993637781090083296015 5839490456671635124944023)
              ·
                refine ⟨8759235685007452687416035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839490456671635124944023 8759235685007452687416035)
                ·
                  refine ⟨13138853527511179031124053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8759235685007452687416035 13138853527511179031124053)
                  ·
                    refine ⟨153970939775521629270985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13138853527511179031124053 153970939775521629270985)
                    ·
                      rfl

theorem cell22_449786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_449786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449786 prefixEnd_449786 := by exact prefixLift 449786
  have htrace : WordTrace (prefixWord ++ tailWord_449786) baseStart_449786 baseEnd_449786 := by
    simpa [prefixWord, tailWord_449786, baseEnd_449786] using wordTrace_append hprefix tailTrace_449786
  have hstable : (prefixWord ++ tailWord_449786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449786).length < 2 ^ (prefixWord ++ tailWord_449786).sum := by decide
  have hdescent : baseEnd_449786 < baseStart_449786 := by decide
  rcases family_descends (prefixWord ++ tailWord_449786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449790 : List Nat := [4, 2, 2, 1, 1, 4, 1, 7]
def baseStart_449790 : Nat := 118140960795 + 449790 * 2 ^ 59
def prefixEnd_449790 : Nat := 4983230072969 + 3 ^ 40 * 449790 * 2
def baseEnd_449790 : Nat := 17108034339696328018997

theorem tailTrace_449790 : CollatzResearch.WordTrace tailWord_449790 prefixEnd_449790 17108034339696328018997 := by
  unfold tailWord_449790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050648630061890357664353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10936792693663415240876549 2050648630061890357664353)
  ·
    refine ⟨1537986472546417768248265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2050648630061890357664353 1537986472546417768248265)
    ·
      refine ⟨1153489854409813326186199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1537986472546417768248265 1153489854409813326186199)
      ·
        refine ⟨1730234781614719989279299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153489854409813326186199 1730234781614719989279299)
        ·
          refine ⟨2595352172422079983918949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730234781614719989279299 2595352172422079983918949)
          ·
            refine ⟨486628532329139996984803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2595352172422079983918949 486628532329139996984803)
            ·
              refine ⟨729942798493709995477205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486628532329139996984803 729942798493709995477205)
              ·
                refine ⟨17108034339696328018997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 729942798493709995477205 17108034339696328018997)
                ·
                  rfl

theorem cell22_449790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_449790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449790 prefixEnd_449790 := by exact prefixLift 449790
  have htrace : WordTrace (prefixWord ++ tailWord_449790) baseStart_449790 baseEnd_449790 := by
    simpa [prefixWord, tailWord_449790, baseEnd_449790] using wordTrace_append hprefix tailTrace_449790
  have hstable : (prefixWord ++ tailWord_449790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449790).length < 2 ^ (prefixWord ++ tailWord_449790).sum := by decide
  have hdescent : baseEnd_449790 < baseStart_449790 := by decide
  rcases family_descends (prefixWord ++ tailWord_449790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449863 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 6]
def baseStart_449863 : Nat := 118140960795 + 449863 * 2 ^ 59
def prefixEnd_449863 : Nat := 4983230072969 + 3 ^ 40 * 449863 * 2
def baseEnd_449863 : Nat := 51332432816373031698583

theorem tailTrace_449863 : CollatzResearch.WordTrace tailWord_449863 prefixEnd_449863 51332432816373031698583 := by
  unfold tailWord_449863
  simp only [CollatzResearch.WordTrace]
  refine ⟨16407851569230656328722243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10938567712820437552481495 16407851569230656328722243)
  ·
    refine ⟨24611777353845984493083365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16407851569230656328722243 24611777353845984493083365)
    ·
      refine ⟨4614708253846122092453131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24611777353845984493083365 4614708253846122092453131)
      ·
        refine ⟨6922062380769183138679697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614708253846122092453131 6922062380769183138679697)
        ·
          refine ⟨5191546785576887354009773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6922062380769183138679697 5191546785576887354009773)
          ·
            refine ⟨1946830044591332757753665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5191546785576887354009773 1946830044591332757753665)
            ·
              refine ⟨1460122533443499568315249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946830044591332757753665 1460122533443499568315249)
              ·
                refine ⟨1095091900082624676236437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460122533443499568315249 1095091900082624676236437)
                ·
                  refine ⟨51332432816373031698583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1095091900082624676236437 51332432816373031698583)
                  ·
                    rfl

theorem cell22_449863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 6].length) (baseStart_449863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449863 prefixEnd_449863 := by exact prefixLift 449863
  have htrace : WordTrace (prefixWord ++ tailWord_449863) baseStart_449863 baseEnd_449863 := by
    simpa [prefixWord, tailWord_449863, baseEnd_449863] using wordTrace_append hprefix tailTrace_449863
  have hstable : (prefixWord ++ tailWord_449863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449863).length < 2 ^ (prefixWord ++ tailWord_449863).sum := by decide
  have hdescent : baseEnd_449863 < baseStart_449863 := by decide
  rcases family_descends (prefixWord ++ tailWord_449863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449948 : List Nat := [2, 2, 3, 4, 2, 1, 2, 2, 4]
def baseStart_449948 : Nat := 118140960795 + 449948 * 2 ^ 59
def prefixEnd_449948 : Nat := 4983230072969 + 3 ^ 40 * 449948 * 2
def baseEnd_449948 : Nat := 51342131895402402240163

theorem tailTrace_449948 : CollatzResearch.WordTrace tailWord_449948 prefixEnd_449948 51342131895402402240163 := by
  unfold tailWord_449948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205475886961357922783249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10940634515948477230377665 8205475886961357922783249)
  ·
    refine ⟨6154106915221018442087437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8205475886961357922783249 6154106915221018442087437)
    ·
      refine ⟨2307790093207881915782789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6154106915221018442087437 2307790093207881915782789)
      ·
        refine ⟨432710642476477859209273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2307790093207881915782789 432710642476477859209273)
        ·
          refine ⟨324532981857358394406955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432710642476477859209273 324532981857358394406955)
          ·
            refine ⟨486799472786037591610433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324532981857358394406955 486799472786037591610433)
            ·
              refine ⟨365099604589528193707825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486799472786037591610433 365099604589528193707825)
              ·
                refine ⟨273824703442146145280869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365099604589528193707825 273824703442146145280869)
                ·
                  refine ⟨51342131895402402240163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273824703442146145280869 51342131895402402240163)
                  ·
                    rfl

theorem cell22_449948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_449948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_449948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_449948 prefixEnd_449948 := by exact prefixLift 449948
  have htrace : WordTrace (prefixWord ++ tailWord_449948) baseStart_449948 baseEnd_449948 := by
    simpa [prefixWord, tailWord_449948, baseEnd_449948] using wordTrace_append hprefix tailTrace_449948
  have hstable : (prefixWord ++ tailWord_449948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449948).length < 2 ^ (prefixWord ++ tailWord_449948).sum := by decide
  have hdescent : baseEnd_449948 < baseStart_449948 := by decide
  rcases family_descends (prefixWord ++ tailWord_449948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450000 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_450000 : Nat := 118140960795 + 450000 * 2 ^ 59
def prefixEnd_450000 : Nat := 4983230072969 + 3 ^ 40 * 450000 * 2
def baseEnd_450000 : Nat := 154044196348896404420329

theorem tailTrace_450000 : CollatzResearch.WordTrace tailWord_450000 prefixEnd_450000 154044196348896404420329 := by
  unfold tailWord_450000
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206424184867164363229727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10941898913156219150972969 8206424184867164363229727)
  ·
    refine ⟨12309636277300746544844591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8206424184867164363229727 12309636277300746544844591)
    ·
      refine ⟨18464454415951119817266887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12309636277300746544844591 18464454415951119817266887)
      ·
        refine ⟨27696681623926679725900331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18464454415951119817266887 27696681623926679725900331)
        ·
          refine ⟨41545022435890019588850497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27696681623926679725900331 41545022435890019588850497)
          ·
            refine ⟨31158766826917514691637873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41545022435890019588850497 31158766826917514691637873)
            ·
              refine ⟨23369075120188136018728405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31158766826917514691637873 23369075120188136018728405)
              ·
                refine ⟨547712698129409437938947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23369075120188136018728405 547712698129409437938947)
                ·
                  refine ⟨821569047194114156908421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547712698129409437938947 821569047194114156908421)
                  ·
                    refine ⟨154044196348896404420329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 821569047194114156908421 154044196348896404420329)
                    ·
                      rfl

theorem cell22_450000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_450000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450000 prefixEnd_450000 := by exact prefixLift 450000
  have htrace : WordTrace (prefixWord ++ tailWord_450000) baseStart_450000 baseEnd_450000 := by
    simpa [prefixWord, tailWord_450000, baseEnd_450000] using wordTrace_append hprefix tailTrace_450000
  have hstable : (prefixWord ++ tailWord_450000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450000).length < 2 ^ (prefixWord ++ tailWord_450000).sum := by decide
  have hdescent : baseEnd_450000 < baseStart_450000 := by decide
  rcases family_descends (prefixWord ++ tailWord_450000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450004 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 5]
def baseStart_450004 : Nat := 118140960795 + 450004 * 2 ^ 59
def prefixEnd_450004 : Nat := 4983230072969 + 3 ^ 40 * 450004 * 2
def baseEnd_450004 : Nat := 51348521876880575773439

theorem tailTrace_450004 : CollatzResearch.WordTrace tailWord_450004 prefixEnd_450004 51348521876880575773439 := by
  unfold tailWord_450004
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206497130859918704802533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10941996174479891606403377 8206497130859918704802533)
  ·
    refine ⟨1538718212036234757150475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8206497130859918704802533 1538718212036234757150475)
    ·
      refine ⟨2308077318054352135725713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538718212036234757150475 2308077318054352135725713)
      ·
        refine ⟨1731057988540764101794285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2308077318054352135725713 1731057988540764101794285)
        ·
          refine ⟨649146745702786538172857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1731057988540764101794285 649146745702786538172857)
          ·
            refine ⟨486860059277089903629643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649146745702786538172857 486860059277089903629643)
            ·
              refine ⟨730290088915634855444465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486860059277089903629643 730290088915634855444465)
              ·
                refine ⟨547717566686726141583349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730290088915634855444465 547717566686726141583349)
                ·
                  refine ⟨51348521876880575773439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 547717566686726141583349 51348521876880575773439)
                  ·
                    rfl

theorem cell22_450004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_450004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450004 prefixEnd_450004 := by exact prefixLift 450004
  have htrace : WordTrace (prefixWord ++ tailWord_450004) baseStart_450004 baseEnd_450004 := by
    simpa [prefixWord, tailWord_450004, baseEnd_450004] using wordTrace_append hprefix tailTrace_450004
  have hstable : (prefixWord ++ tailWord_450004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450004).length < 2 ^ (prefixWord ++ tailWord_450004).sum := by decide
  have hdescent : baseEnd_450004 < baseStart_450004 := by decide
  rcases family_descends (prefixWord ++ tailWord_450004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450015 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 6]
def baseStart_450015 : Nat := 118140960795 + 450015 * 2 ^ 59
def prefixEnd_450015 : Nat := 4983230072969 + 3 ^ 40 * 450015 * 2
def baseEnd_450015 : Nat := 51349777051813788431761

theorem tailTrace_450015 : CollatzResearch.WordTrace tailWord_450015 prefixEnd_450015 51349777051813788431761 := by
  unfold tailWord_450015
  simp only [CollatzResearch.WordTrace]
  refine ⟨16413395464679986288255499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10942263643119990858836999 16413395464679986288255499)
  ·
    refine ⟨24620093197019979432383249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16413395464679986288255499 24620093197019979432383249)
    ·
      refine ⟨18465069897764984574287437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24620093197019979432383249 18465069897764984574287437)
      ·
        refine ⟨6924401211661869215357789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18465069897764984574287437 6924401211661869215357789)
        ·
          refine ⟨2596650454373200955759171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6924401211661869215357789 2596650454373200955759171)
          ·
            refine ⟨3894975681559801433638757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596650454373200955759171 3894975681559801433638757)
            ·
              refine ⟨730307940292462768807267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3894975681559801433638757 730307940292462768807267)
              ·
                refine ⟨1095461910438694153210901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730307940292462768807267 1095461910438694153210901)
                ·
                  refine ⟨51349777051813788431761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1095461910438694153210901 51349777051813788431761)
                  ·
                    rfl

theorem cell22_450015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 6].length) (baseStart_450015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450015 prefixEnd_450015 := by exact prefixLift 450015
  have htrace : WordTrace (prefixWord ++ tailWord_450015) baseStart_450015 baseEnd_450015 := by
    simpa [prefixWord, tailWord_450015, baseEnd_450015] using wordTrace_append hprefix tailTrace_450015
  have hstable : (prefixWord ++ tailWord_450015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450015).length < 2 ^ (prefixWord ++ tailWord_450015).sum := by decide
  have hdescent : baseEnd_450015 < baseStart_450015 := by decide
  rcases family_descends (prefixWord ++ tailWord_450015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450034 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_450034 : Nat := 118140960795 + 450034 * 2 ^ 59
def prefixEnd_450034 : Nat := 4983230072969 + 3 ^ 40 * 450034 * 2
def baseEnd_450034 : Nat := 154055835243731649070225

theorem tailTrace_450034 : CollatzResearch.WordTrace tailWord_450034 prefixEnd_450034 154055835243731649070225 := by
  unfold tailWord_450034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4103522112902788133299289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10942725634407435022131437 4103522112902788133299289)
  ·
    refine ⟨3077641584677091099974467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4103522112902788133299289 3077641584677091099974467)
    ·
      refine ⟨4616462377015636649961701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077641584677091099974467 4616462377015636649961701)
      ·
        refine ⟨865586695690431871867819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4616462377015636649961701 865586695690431871867819)
        ·
          refine ⟨1298380043535647807801729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865586695690431871867819 1298380043535647807801729)
          ·
            refine ⟨973785032651735855851297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298380043535647807801729 973785032651735855851297)
            ·
              refine ⟨730338774488801891888473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973785032651735855851297 730338774488801891888473)
              ·
                refine ⟨547754080866601418916355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730338774488801891888473 547754080866601418916355)
                ·
                  refine ⟨821631121299902128374533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547754080866601418916355 821631121299902128374533)
                  ·
                    refine ⟨154055835243731649070225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 821631121299902128374533 154055835243731649070225)
                    ·
                      rfl

theorem cell22_450034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_450034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450034 prefixEnd_450034 := by exact prefixLift 450034
  have htrace : WordTrace (prefixWord ++ tailWord_450034) baseStart_450034 baseEnd_450034 := by
    simpa [prefixWord, tailWord_450034, baseEnd_450034] using wordTrace_append hprefix tailTrace_450034
  have hstable : (prefixWord ++ tailWord_450034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450034).length < 2 ^ (prefixWord ++ tailWord_450034).sum := by decide
  have hdescent : baseEnd_450034 < baseStart_450034 := by decide
  rcases family_descends (prefixWord ++ tailWord_450034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450043 : List Nat := [1, 1, 1, 1, 1, 3, 2, 12]
def baseStart_450043 : Nat := 118140960795 + 450043 * 2 ^ 59
def prefixEnd_450043 : Nat := 4983230072969 + 3 ^ 40 * 450043 * 2
def baseEnd_450043 : Nat := 17117657347517625066133

theorem tailTrace_450043 : CollatzResearch.WordTrace tailWord_450043 prefixEnd_450043 17117657347517625066133 := by
  unfold tailWord_450043
  simp only [CollatzResearch.WordTrace]
  refine ⟨16414416708578547070274783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10942944472385698046849855 16414416708578547070274783)
  ·
    refine ⟨24621625062867820605412175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16414416708578547070274783 24621625062867820605412175)
    ·
      refine ⟨36932437594301730908118263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24621625062867820605412175 36932437594301730908118263)
      ·
        refine ⟨55398656391452596362177395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36932437594301730908118263 55398656391452596362177395)
        ·
          refine ⟨83097984587178894543266093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55398656391452596362177395 83097984587178894543266093)
          ·
            refine ⟨31161744220192085453724785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83097984587178894543266093 31161744220192085453724785)
            ·
              refine ⟨23371308165144064090293589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31161744220192085453724785 23371308165144064090293589)
              ·
                refine ⟨17117657347517625066133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 23371308165144064090293589 17117657347517625066133)
                ·
                  rfl

theorem cell22_450043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 12].length) (baseStart_450043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450043 prefixEnd_450043 := by exact prefixLift 450043
  have htrace : WordTrace (prefixWord ++ tailWord_450043) baseStart_450043 baseEnd_450043 := by
    simpa [prefixWord, tailWord_450043, baseEnd_450043] using wordTrace_append hprefix tailTrace_450043
  have hstable : (prefixWord ++ tailWord_450043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450043).length < 2 ^ (prefixWord ++ tailWord_450043).sum := by decide
  have hdescent : baseEnd_450043 < baseStart_450043 := by decide
  rcases family_descends (prefixWord ++ tailWord_450043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450045 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_450045 : Nat := 118140960795 + 450045 * 2 ^ 59
def prefixEnd_450045 : Nat := 4983230072969 + 3 ^ 40 * 450045 * 2
def baseEnd_450045 : Nat := 154059600768531287045191

theorem tailTrace_450045 : CollatzResearch.WordTrace tailWord_450045 prefixEnd_450045 154059600768531287045191 := by
  unfold tailWord_450045
  simp only [CollatzResearch.WordTrace]
  refine ⟨16414489654571301411847589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10942993103047534274565059 16414489654571301411847589)
  ·
    refine ⟨3077716810232119014721423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16414489654571301411847589 3077716810232119014721423)
    ·
      refine ⟨4616575215348178522082135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077716810232119014721423 4616575215348178522082135)
      ·
        refine ⟨6924862823022267783123203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616575215348178522082135 6924862823022267783123203)
        ·
          refine ⟨10387294234533401674684805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6924862823022267783123203 10387294234533401674684805)
          ·
            refine ⟨1947617668975012814003401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10387294234533401674684805 1947617668975012814003401)
            ·
              refine ⟨1460713251731259610502551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947617668975012814003401 1460713251731259610502551)
              ·
                refine ⟨2191069877596889415753827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460713251731259610502551 2191069877596889415753827)
                ·
                  refine ⟨3286604816395334123630741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191069877596889415753827 3286604816395334123630741)
                  ·
                    refine ⟨154059600768531287045191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3286604816395334123630741 154059600768531287045191)
                    ·
                      rfl

theorem cell22_450045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_450045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450045 prefixEnd_450045 := by exact prefixLift 450045
  have htrace : WordTrace (prefixWord ++ tailWord_450045) baseStart_450045 baseEnd_450045 := by
    simpa [prefixWord, tailWord_450045, baseEnd_450045] using wordTrace_append hprefix tailTrace_450045
  have hstable : (prefixWord ++ tailWord_450045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450045).length < 2 ^ (prefixWord ++ tailWord_450045).sum := by decide
  have hdescent : baseEnd_450045 < baseStart_450045 := by decide
  rcases family_descends (prefixWord ++ tailWord_450045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450081 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 2, 3]
def baseStart_450081 : Nat := 118140960795 + 450081 * 2 ^ 59
def prefixEnd_450081 : Nat := 4983230072969 + 3 ^ 40 * 450081 * 2
def baseEnd_450081 : Nat := 154071924304239193145081

theorem tailTrace_450081 : CollatzResearch.WordTrace tailWord_450081 prefixEnd_450081 154071924304239193145081 := by
  unfold tailWord_450081
  simp only [CollatzResearch.WordTrace]
  refine ⟨16415802682440879560158097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10943868454960586373438731 16415802682440879560158097)
  ·
    refine ⟨12311852011830659670118573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16415802682440879560158097 12311852011830659670118573)
    ·
      refine ⟨4616944504436497376294465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12311852011830659670118573 4616944504436497376294465)
      ·
        refine ⟨3462708378327373032220849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4616944504436497376294465 3462708378327373032220849)
        ·
          refine ⟨2597031283745529774165637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462708378327373032220849 2597031283745529774165637)
          ·
            refine ⟨486943365702286832656057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2597031283745529774165637 486943365702286832656057)
            ·
              refine ⟨365207524276715124492043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486943365702286832656057 365207524276715124492043)
              ·
                refine ⟨547811286415072686738065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365207524276715124492043 547811286415072686738065)
                ·
                  refine ⟨410858464811304515053549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547811286415072686738065 410858464811304515053549)
                  ·
                    refine ⟨154071924304239193145081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 410858464811304515053549 154071924304239193145081)
                    ·
                      rfl

theorem cell22_450081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_450081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450081 prefixEnd_450081 := by exact prefixLift 450081
  have htrace : WordTrace (prefixWord ++ tailWord_450081) baseStart_450081 baseEnd_450081 := by
    simpa [prefixWord, tailWord_450081, baseEnd_450081] using wordTrace_append hprefix tailTrace_450081
  have hstable : (prefixWord ++ tailWord_450081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450081).length < 2 ^ (prefixWord ++ tailWord_450081).sum := by decide
  have hdescent : baseEnd_450081 < baseStart_450081 := by decide
  rcases family_descends (prefixWord ++ tailWord_450081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450122 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_450122 : Nat := 118140960795 + 450122 * 2 ^ 59
def prefixEnd_450122 : Nat := 4983230072969 + 3 ^ 40 * 450122 * 2
def baseEnd_450122 : Nat := 51361986480709584289985

theorem tailTrace_450122 : CollatzResearch.WordTrace tailWord_450122 prefixEnd_450122 51361986480709584289985 := by
  unfold tailWord_450122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104324518823085890600155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10944865383528229041600413 4104324518823085890600155)
  ·
    refine ⟨6156486778234628835900233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4104324518823085890600155 6156486778234628835900233)
    ·
      refine ⟨4617365083675971626925175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6156486778234628835900233 4617365083675971626925175)
      ·
        refine ⟨6926047625513957440387763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617365083675971626925175 6926047625513957440387763)
        ·
          refine ⟨10389071438270936160581645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926047625513957440387763 10389071438270936160581645)
          ·
            refine ⟨3895901789351601060218117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10389071438270936160581645 3895901789351601060218117)
            ·
              refine ⟨730481585503425198790897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3895901789351601060218117 730481585503425198790897)
              ·
                refine ⟨547861189127568899093173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730481585503425198790897 547861189127568899093173)
                ·
                  refine ⟨51361986480709584289985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 547861189127568899093173 51361986480709584289985)
                  ·
                    rfl

theorem cell22_450122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_450122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450122 prefixEnd_450122 := by exact prefixLift 450122
  have htrace : WordTrace (prefixWord ++ tailWord_450122) baseStart_450122 baseEnd_450122 := by
    simpa [prefixWord, tailWord_450122, baseEnd_450122] using wordTrace_append hprefix tailTrace_450122
  have hstable : (prefixWord ++ tailWord_450122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450122).length < 2 ^ (prefixWord ++ tailWord_450122).sum := by decide
  have hdescent : baseEnd_450122 < baseStart_450122 := by decide
  rcases family_descends (prefixWord ++ tailWord_450122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450199 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 1, 5]
def baseStart_450199 : Nat := 118140960795 + 450199 * 2 ^ 59
def prefixEnd_450199 : Nat := 4983230072969 + 3 ^ 40 * 450199 * 2
def baseEnd_450199 : Nat := 154112318115726218694719

theorem tailTrace_450199 : CollatzResearch.WordTrace tailWord_450199 prefixEnd_450199 154112318115726218694719 := by
  unfold tailWord_450199
  simp only [CollatzResearch.WordTrace]
  refine ⟨16420106496013385712953651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10946737664008923808635767 16420106496013385712953651)
  ·
    refine ⟨24630159744020078569430477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16420106496013385712953651 24630159744020078569430477)
    ·
      refine ⟨9236309904007529463536429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24630159744020078569430477 9236309904007529463536429)
      ·
        refine ⟨3463616214002823548826161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9236309904007529463536429 3463616214002823548826161)
        ·
          refine ⟨2597712160502117661619621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3463616214002823548826161 2597712160502117661619621)
          ·
            refine ⟨487071030094147061553679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2597712160502117661619621 487071030094147061553679)
            ·
              refine ⟨730606545141220592330519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487071030094147061553679 730606545141220592330519)
              ·
                refine ⟨1095909817711830888495779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730606545141220592330519 1095909817711830888495779)
                ·
                  refine ⟨1643864726567746332743669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095909817711830888495779 1643864726567746332743669)
                  ·
                    refine ⟨154112318115726218694719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1643864726567746332743669 154112318115726218694719)
                    ·
                      rfl

theorem cell22_450199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_450199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450199 prefixEnd_450199 := by exact prefixLift 450199
  have htrace : WordTrace (prefixWord ++ tailWord_450199) baseStart_450199 baseEnd_450199 := by
    simpa [prefixWord, tailWord_450199, baseEnd_450199] using wordTrace_append hprefix tailTrace_450199
  have hstable : (prefixWord ++ tailWord_450199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450199).length < 2 ^ (prefixWord ++ tailWord_450199).sum := by decide
  have hdescent : baseEnd_450199 < baseStart_450199 := by decide
  rcases family_descends (prefixWord ++ tailWord_450199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450212 : List Nat := [2, 3, 1, 2, 2, 3, 1, 8]
def baseStart_450212 : Nat := 118140960795 + 450212 * 2 ^ 59
def prefixEnd_450212 : Nat := 4983230072969 + 3 ^ 40 * 450212 * 2
def baseEnd_450212 : Nat := 17124085364599835346631

theorem tailTrace_450212 : CollatzResearch.WordTrace tailWord_450212 prefixEnd_450212 17124085364599835346631 := by
  unfold tailWord_450212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8210290322483144466588445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10947053763310859288784593 8210290322483144466588445)
  ·
    refine ⟨3078858870931179174970667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8210290322483144466588445 3078858870931179174970667)
    ·
      refine ⟨4618288306396768762456001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3078858870931179174970667 4618288306396768762456001)
      ·
        refine ⟨3463716229797576571842001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4618288306396768762456001 3463716229797576571842001)
        ·
          refine ⟨2597787172348182428881501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3463716229797576571842001 2597787172348182428881501)
          ·
            refine ⟨974170189630568410830563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2597787172348182428881501 974170189630568410830563)
            ·
              refine ⟨1461255284445852616245845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974170189630568410830563 1461255284445852616245845)
              ·
                refine ⟨17124085364599835346631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1461255284445852616245845 17124085364599835346631)
                ·
                  rfl

theorem cell22_450212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 8].length) (baseStart_450212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450212 prefixEnd_450212 := by exact prefixLift 450212
  have htrace : WordTrace (prefixWord ++ tailWord_450212) baseStart_450212 baseEnd_450212 := by
    simpa [prefixWord, tailWord_450212, baseEnd_450212] using wordTrace_append hprefix tailTrace_450212
  have hstable : (prefixWord ++ tailWord_450212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450212).length < 2 ^ (prefixWord ++ tailWord_450212).sum := by decide
  have hdescent : baseEnd_450212 < baseStart_450212 := by decide
  rcases family_descends (prefixWord ++ tailWord_450212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450229 : List Nat := [1, 3, 3, 3, 2, 2, 8]
def baseStart_450229 : Nat := 118140960795 + 450229 * 2 ^ 59
def prefixEnd_450229 : Nat := 4983230072969 + 3 ^ 40 * 450229 * 2
def baseEnd_450229 : Nat := 5708243989956153349801

theorem tailTrace_450229 : CollatzResearch.WordTrace tailWord_450229 prefixEnd_450229 5708243989956153349801 := by
  unfold tailWord_450229
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421200685904700836545741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10947467123936467224363827 16421200685904700836545741)
  ·
    refine ⟨6157950257214262813704653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16421200685904700836545741 6157950257214262813704653)
    ·
      refine ⟨2309231346455348555139245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6157950257214262813704653 2309231346455348555139245)
      ·
        refine ⟨865961754920755708177217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2309231346455348555139245 865961754920755708177217)
        ·
          refine ⟨649471316190566781132913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865961754920755708177217 649471316190566781132913)
          ·
            refine ⟨487103487142925085849685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649471316190566781132913 487103487142925085849685)
            ·
              refine ⟨5708243989956153349801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 487103487142925085849685 5708243989956153349801)
              ·
                rfl

theorem cell22_450229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 8].length) (baseStart_450229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450229 prefixEnd_450229 := by exact prefixLift 450229
  have htrace : WordTrace (prefixWord ++ tailWord_450229) baseStart_450229 baseEnd_450229 := by
    simpa [prefixWord, tailWord_450229, baseEnd_450229] using wordTrace_append hprefix tailTrace_450229
  have hstable : (prefixWord ++ tailWord_450229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450229).length < 2 ^ (prefixWord ++ tailWord_450229).sum := by decide
  have hdescent : baseEnd_450229 < baseStart_450229 := by decide
  rcases family_descends (prefixWord ++ tailWord_450229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450246 : List Nat := [6, 1, 2, 1, 1, 1, 1, 9]
def baseStart_450246 : Nat := 118140960795 + 450246 * 2 ^ 59
def prefixEnd_450246 : Nat := 4983230072969 + 3 ^ 40 * 450246 * 2
def baseEnd_450246 : Nat := 17125378575137084752175

theorem tailTrace_450246 : CollatzResearch.WordTrace tailWord_450246 prefixEnd_450246 17125378575137084752175 := by
  unfold tailWord_450246
  simp only [CollatzResearch.WordTrace]
  refine ⟨513181897713847273122331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10947880484562075159943061 513181897713847273122331)
  ·
    refine ⟨769772846570770909683497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 513181897713847273122331 769772846570770909683497)
    ·
      refine ⟨577329634928078182262623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 769772846570770909683497 577329634928078182262623)
      ·
        refine ⟨865994452392117273393935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577329634928078182262623 865994452392117273393935)
        ·
          refine ⟨1298991678588175910090903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865994452392117273393935 1298991678588175910090903)
          ·
            refine ⟨1948487517882263865136355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298991678588175910090903 1948487517882263865136355)
            ·
              refine ⟨2922731276823395797704533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948487517882263865136355 2922731276823395797704533)
              ·
                refine ⟨17125378575137084752175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2922731276823395797704533 17125378575137084752175)
                ·
                  rfl

theorem cell22_450246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_450246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450246 prefixEnd_450246 := by exact prefixLift 450246
  have htrace : WordTrace (prefixWord ++ tailWord_450246) baseStart_450246 baseEnd_450246 := by
    simpa [prefixWord, tailWord_450246, baseEnd_450246] using wordTrace_append hprefix tailTrace_450246
  have hstable : (prefixWord ++ tailWord_450246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450246).length < 2 ^ (prefixWord ++ tailWord_450246).sum := by decide
  have hdescent : baseEnd_450246 < baseStart_450246 := by decide
  rcases family_descends (prefixWord ++ tailWord_450246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450250 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_450250 : Nat := 118140960795 + 450250 * 2 ^ 59
def prefixEnd_450250 : Nat := 4983230072969 + 3 ^ 40 * 450250 * 2
def baseEnd_450250 : Nat := 154129776457979085669563

theorem tailTrace_450250 : CollatzResearch.WordTrace tailWord_450250 prefixEnd_450250 154129776457979085669563 := by
  unfold tailWord_450250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105491654707155355765051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10947977745885747615373469 4105491654707155355765051)
  ·
    refine ⟨6158237482060733033647577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4105491654707155355765051 6158237482060733033647577)
    ·
      refine ⟨4618678111545549775235683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6158237482060733033647577 4618678111545549775235683)
      ·
        refine ⟨6928017167318324662853525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618678111545549775235683 6928017167318324662853525)
        ·
          refine ⟨324750804718046468571259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6928017167318324662853525 324750804718046468571259)
          ·
            refine ⟨487126207077069702856889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324750804718046468571259 487126207077069702856889)
            ·
              refine ⟨365344655307802277142667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487126207077069702856889 365344655307802277142667)
              ·
                refine ⟨548016982961703415714001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365344655307802277142667 548016982961703415714001)
                ·
                  refine ⟨411012737221277561785501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548016982961703415714001 411012737221277561785501)
                  ·
                    refine ⟨154129776457979085669563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411012737221277561785501 154129776457979085669563)
                    ·
                      rfl

theorem cell22_450250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_450250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450250 prefixEnd_450250 := by exact prefixLift 450250
  have htrace : WordTrace (prefixWord ++ tailWord_450250) baseStart_450250 baseEnd_450250 := by
    simpa [prefixWord, tailWord_450250, baseEnd_450250] using wordTrace_append hprefix tailTrace_450250
  have hstable : (prefixWord ++ tailWord_450250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450250).length < 2 ^ (prefixWord ++ tailWord_450250).sum := by decide
  have hdescent : baseEnd_450250 < baseStart_450250 := by decide
  rcases family_descends (prefixWord ++ tailWord_450250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450336 : List Nat := [2, 1, 1, 5, 1, 1, 4, 3, 4]
def baseStart_450336 : Nat := 118140960795 + 450336 * 2 ^ 59
def prefixEnd_450336 : Nat := 4983230072969 + 3 ^ 40 * 450336 * 2
def baseEnd_450336 : Nat := 51386405338501176006433

theorem tailTrace_450336 : CollatzResearch.WordTrace tailWord_450336 prefixEnd_450336 51386405338501176006433 := by
  unfold tailWord_450336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212551648258529055345431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10950068864344705407127241 8212551648258529055345431)
  ·
    refine ⟨12318827472387793583018147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8212551648258529055345431 12318827472387793583018147)
    ·
      refine ⟨18478241208581690374527221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12318827472387793583018147 18478241208581690374527221)
      ·
        refine ⟨1732335113304533472611927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18478241208581690374527221 1732335113304533472611927)
        ·
          refine ⟨2598502669956800208917891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732335113304533472611927 2598502669956800208917891)
          ·
            refine ⟨3897754004935200313376837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598502669956800208917891 3897754004935200313376837)
            ·
              refine ⟨730828875925350058758157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3897754004935200313376837 730828875925350058758157)
              ·
                refine ⟨274060828472006272034309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 730828875925350058758157 274060828472006272034309)
                ·
                  refine ⟨51386405338501176006433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274060828472006272034309 51386405338501176006433)
                  ·
                    rfl

theorem cell22_450336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_450336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450336 prefixEnd_450336 := by exact prefixLift 450336
  have htrace : WordTrace (prefixWord ++ tailWord_450336) baseStart_450336 baseEnd_450336 := by
    simpa [prefixWord, tailWord_450336, baseEnd_450336] using wordTrace_append hprefix tailTrace_450336
  have hstable : (prefixWord ++ tailWord_450336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450336).length < 2 ^ (prefixWord ++ tailWord_450336).sum := by decide
  have hdescent : baseEnd_450336 < baseStart_450336 := by decide
  rcases family_descends (prefixWord ++ tailWord_450336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450381 : List Nat := [1, 6, 1, 2, 1, 2, 1, 8]
def baseStart_450381 : Nat := 118140960795 + 450381 * 2 ^ 59
def prefixEnd_450381 : Nat := 4983230072969 + 3 ^ 40 * 450381 * 2
def baseEnd_450381 : Nat := 17130513381682045627129

theorem tailTrace_450381 : CollatzResearch.WordTrace tailWord_450381 prefixEnd_450381 17130513381682045627129 := by
  unfold tailWord_450381
  simp only [CollatzResearch.WordTrace]
  refine ⟨16426744581354030796078997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10951163054236020530719331 16426744581354030796078997)
  ·
    refine ⟨770003652250970193566203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16426744581354030796078997 770003652250970193566203)
    ·
      refine ⟨1155005478376455290349305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770003652250970193566203 1155005478376455290349305)
      ·
        refine ⟨866254108782341467761979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1155005478376455290349305 866254108782341467761979)
        ·
          refine ⟨1299381163173512201642969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866254108782341467761979 1299381163173512201642969)
          ·
            refine ⟨974535872380134151232227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299381163173512201642969 974535872380134151232227)
            ·
              refine ⟨1461803808570201226848341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974535872380134151232227 1461803808570201226848341)
              ·
                refine ⟨17130513381682045627129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1461803808570201226848341 17130513381682045627129)
                ·
                  rfl

theorem cell22_450381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 8].length) (baseStart_450381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450381 prefixEnd_450381 := by exact prefixLift 450381
  have htrace : WordTrace (prefixWord ++ tailWord_450381) baseStart_450381 baseEnd_450381 := by
    simpa [prefixWord, tailWord_450381, baseEnd_450381] using wordTrace_append hprefix tailTrace_450381
  have hstable : (prefixWord ++ tailWord_450381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450381).length < 2 ^ (prefixWord ++ tailWord_450381).sum := by decide
  have hdescent : baseEnd_450381 < baseStart_450381 := by decide
  rcases family_descends (prefixWord ++ tailWord_450381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450413 : List Nat := [1, 5, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_450413 : Nat := 118140960795 + 450413 * 2 ^ 59
def prefixEnd_450413 : Nat := 4983230072969 + 3 ^ 40 * 450413 * 2
def baseEnd_450413 : Nat := 154185574689100993844063

theorem tailTrace_450413 : CollatzResearch.WordTrace tailWord_450413 prefixEnd_450413 154185574689100993844063 := by
  unfold tailWord_450413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16427911717238100261243893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10951941144825400174162595 16427911717238100261243893)
  ·
    refine ⟨1540116723491071899491615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16427911717238100261243893 1540116723491071899491615)
    ·
      refine ⟨2310175085236607849237423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1540116723491071899491615 2310175085236607849237423)
      ·
        refine ⟨3465262627854911773856135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2310175085236607849237423 3465262627854911773856135)
        ·
          refine ⟨5197893941782367660784203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3465262627854911773856135 5197893941782367660784203)
          ·
            refine ⟨7796840912673551491176305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197893941782367660784203 7796840912673551491176305)
            ·
              refine ⟨5847630684505163618382229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7796840912673551491176305 5847630684505163618382229)
              ·
                refine ⟨274107688336179544611667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5847630684505163618382229 274107688336179544611667)
                ·
                  refine ⟨411161532504269316917501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274107688336179544611667 411161532504269316917501)
                  ·
                    refine ⟨154185574689100993844063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411161532504269316917501 154185574689100993844063)
                    ·
                      rfl

theorem cell22_450413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_450413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450413 prefixEnd_450413 := by exact prefixLift 450413
  have htrace : WordTrace (prefixWord ++ tailWord_450413) baseStart_450413 baseEnd_450413 := by
    simpa [prefixWord, tailWord_450413, baseEnd_450413] using wordTrace_append hprefix tailTrace_450413
  have hstable : (prefixWord ++ tailWord_450413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450413).length < 2 ^ (prefixWord ++ tailWord_450413).sum := by decide
  have hdescent : baseEnd_450413 < baseStart_450413 := by decide
  rcases family_descends (prefixWord ++ tailWord_450413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450426 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_450426 : Nat := 118140960795 + 450426 * 2 ^ 59
def prefixEnd_450426 : Nat := 4983230072969 + 3 ^ 40 * 450426 * 2
def baseEnd_450426 : Nat := 51396674951591097756341

theorem tailTrace_450426 : CollatzResearch.WordTrace tailWord_450426 prefixEnd_450426 51396674951591097756341 := by
  unfold tailWord_450426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107096466547750870366783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10952257244127335654311421 4107096466547750870366783)
  ·
    refine ⟨6160644699821626305550175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4107096466547750870366783 6160644699821626305550175)
    ·
      refine ⟨9240967049732439458325263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6160644699821626305550175 9240967049732439458325263)
      ·
        refine ⟨13861450574598659187487895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9240967049732439458325263 13861450574598659187487895)
        ·
          refine ⟨20792175861897988781231843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13861450574598659187487895 20792175861897988781231843)
          ·
            refine ⟨31188263792846983171847765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20792175861897988781231843 31188263792846983171847765)
            ·
              refine ⟨365487466322425584045091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 31188263792846983171847765 365487466322425584045091)
              ·
                refine ⟨548231199483638376067637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365487466322425584045091 548231199483638376067637)
                ·
                  refine ⟨51396674951591097756341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 548231199483638376067637 51396674951591097756341)
                  ·
                    rfl

theorem cell22_450426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_450426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450426 prefixEnd_450426 := by exact prefixLift 450426
  have htrace : WordTrace (prefixWord ++ tailWord_450426) baseStart_450426 baseEnd_450426 := by
    simpa [prefixWord, tailWord_450426, baseEnd_450426] using wordTrace_append hprefix tailTrace_450426
  have hstable : (prefixWord ++ tailWord_450426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450426).length < 2 ^ (prefixWord ++ tailWord_450426).sum := by decide
  have hdescent : baseEnd_450426 < baseStart_450426 := by decide
  rcases family_descends (prefixWord ++ tailWord_450426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450529 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_450529 : Nat := 118140960795 + 450529 * 2 ^ 59
def prefixEnd_450529 : Nat := 4983230072969 + 3 ^ 40 * 450529 * 2
def baseEnd_450529 : Nat := 154225283859715357943707

theorem tailTrace_450529 : CollatzResearch.WordTrace tailWord_450529 prefixEnd_450529 154225283859715357943707 := by
  unfold tailWord_450529
  simp only [CollatzResearch.WordTrace]
  refine ⟨16432142584817852072466641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10954761723211901381644427 16432142584817852072466641)
  ·
    refine ⟨12324106938613389054349981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16432142584817852072466641 12324106938613389054349981)
    ·
      refine ⟨4621540101980020895381243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12324106938613389054349981 4621540101980020895381243)
      ·
        refine ⟨6932310152970031343071865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4621540101980020895381243 6932310152970031343071865)
        ·
          refine ⟨5199232614727523507303899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6932310152970031343071865 5199232614727523507303899)
          ·
            refine ⟨7798848922091285260955849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199232614727523507303899 7798848922091285260955849)
            ·
              refine ⟨5849136691568463945716887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7798848922091285260955849 5849136691568463945716887)
              ·
                refine ⟨8773705037352695918575331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849136691568463945716887 8773705037352695918575331)
                ·
                  refine ⟨13160557556029043877862997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8773705037352695918575331 13160557556029043877862997)
                  ·
                    refine ⟨154225283859715357943707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13160557556029043877862997 154225283859715357943707)
                    ·
                      rfl

theorem cell22_450529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_450529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450529 prefixEnd_450529 := by exact prefixLift 450529
  have htrace : WordTrace (prefixWord ++ tailWord_450529) baseStart_450529 baseEnd_450529 := by
    simpa [prefixWord, tailWord_450529, baseEnd_450529] using wordTrace_append hprefix tailTrace_450529
  have hstable : (prefixWord ++ tailWord_450529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450529).length < 2 ^ (prefixWord ++ tailWord_450529).sum := by decide
  have hdescent : baseEnd_450529 < baseStart_450529 := by decide
  rcases family_descends (prefixWord ++ tailWord_450529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450550 : List Nat := [5, 1, 1, 1, 4, 2, 2, 6]
def baseStart_450550 : Nat := 118140960795 + 450550 * 2 ^ 59
def prefixEnd_450550 : Nat := 4983230072969 + 3 ^ 40 * 450550 * 2
def baseEnd_450550 : Nat := 17136941398764255907627

theorem tailTrace_450550 : CollatzResearch.WordTrace tailWord_450550 prefixEnd_450550 17136941398764255907627 := by
  unfold tailWord_450550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027056782358860791186319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10955272345161181772654069 1027056782358860791186319)
  ·
    refine ⟨1540585173538291186779479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1027056782358860791186319 1540585173538291186779479)
    ·
      refine ⟨2310877760307436780169219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1540585173538291186779479 2310877760307436780169219)
      ·
        refine ⟨3466316640461155170253829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2310877760307436780169219 3466316640461155170253829)
        ·
          refine ⟨649934370086466594422593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3466316640461155170253829 649934370086466594422593)
          ·
            refine ⟨487450777564849945816945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649934370086466594422593 487450777564849945816945)
            ·
              refine ⟨365588083173637459362709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487450777564849945816945 365588083173637459362709)
              ·
                refine ⟨17136941398764255907627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365588083173637459362709 17136941398764255907627)
                ·
                  rfl

theorem cell22_450550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_450550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450550 prefixEnd_450550 := by exact prefixLift 450550
  have htrace : WordTrace (prefixWord ++ tailWord_450550) baseStart_450550 baseEnd_450550 := by
    simpa [prefixWord, tailWord_450550, baseEnd_450550] using wordTrace_append hprefix tailTrace_450550
  have hstable : (prefixWord ++ tailWord_450550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450550).length < 2 ^ (prefixWord ++ tailWord_450550).sum := by decide
  have hdescent : baseEnd_450550 < baseStart_450550 := by decide
  rcases family_descends (prefixWord ++ tailWord_450550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450559 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 1, 7]
def baseStart_450559 : Nat := 118140960795 + 450559 * 2 ^ 59
def prefixEnd_450559 : Nat := 4983230072969 + 3 ^ 40 * 450559 * 2
def baseEnd_450559 : Nat := 154235553472805279693615

theorem tailTrace_450559 : CollatzResearch.WordTrace tailWord_450559 prefixEnd_450559 154235553472805279693615 := by
  unfold tailWord_450559
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433236774709167196058731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10955491183139444797372487 16433236774709167196058731)
  ·
    refine ⟨24649855162063750794088097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16433236774709167196058731 24649855162063750794088097)
    ·
      refine ⟨18487391371547813095566073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24649855162063750794088097 18487391371547813095566073)
      ·
        refine ⟨13865543528660859821674555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18487391371547813095566073 13865543528660859821674555)
        ·
          refine ⟨20798315292991289732511833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13865543528660859821674555 20798315292991289732511833)
          ·
            refine ⟨15598736469743467299383875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20798315292991289732511833 15598736469743467299383875)
            ·
              refine ⟨23398104704615200949075813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15598736469743467299383875 23398104704615200949075813)
              ·
                refine ⟨4387144632115350177951715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23398104704615200949075813 4387144632115350177951715)
                ·
                  refine ⟨6580716948173025266927573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387144632115350177951715 6580716948173025266927573)
                  ·
                    refine ⟨154235553472805279693615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6580716948173025266927573 154235553472805279693615)
                    ·
                      rfl

theorem cell22_450559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_450559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450559 prefixEnd_450559 := by exact prefixLift 450559
  have htrace : WordTrace (prefixWord ++ tailWord_450559) baseStart_450559 baseEnd_450559 := by
    simpa [prefixWord, tailWord_450559, baseEnd_450559] using wordTrace_append hprefix tailTrace_450559
  have hstable : (prefixWord ++ tailWord_450559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450559).length < 2 ^ (prefixWord ++ tailWord_450559).sum := by decide
  have hdescent : baseEnd_450559 < baseStart_450559 := by decide
  rcases family_descends (prefixWord ++ tailWord_450559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450565 : List Nat := [1, 3, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_450565 : Nat := 118140960795 + 450565 * 2 ^ 59
def prefixEnd_450565 : Nat := 4983230072969 + 3 ^ 40 * 450565 * 2
def baseEnd_450565 : Nat := 154237607395423264043597

theorem tailTrace_450565 : CollatzResearch.WordTrace tailWord_450565 prefixEnd_450565 154237607395423264043597 := by
  unfold tailWord_450565
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433455612687430220777149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10955637075124953480518099 16433455612687430220777149)
  ·
    refine ⟨6162545854757786332791431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16433455612687430220777149 6162545854757786332791431)
    ·
      refine ⟨9243818782136679499187147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162545854757786332791431 9243818782136679499187147)
      ·
        refine ⟨13865728173205019248780721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9243818782136679499187147 13865728173205019248780721)
        ·
          refine ⟨10399296129903764436585541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13865728173205019248780721 10399296129903764436585541)
          ·
            refine ⟨1949868024356955831859789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10399296129903764436585541 1949868024356955831859789)
            ·
              refine ⟨731200509133858436947421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1949868024356955831859789 731200509133858436947421)
              ·
                refine ⟨274200190925196913855283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731200509133858436947421 274200190925196913855283)
                ·
                  refine ⟨411300286387795370782925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274200190925196913855283 411300286387795370782925)
                  ·
                    refine ⟨154237607395423264043597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411300286387795370782925 154237607395423264043597)
                    ·
                      rfl

theorem cell22_450565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_450565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450565 prefixEnd_450565 := by exact prefixLift 450565
  have htrace : WordTrace (prefixWord ++ tailWord_450565) baseStart_450565 baseEnd_450565 := by
    simpa [prefixWord, tailWord_450565, baseEnd_450565] using wordTrace_append hprefix tailTrace_450565
  have hstable : (prefixWord ++ tailWord_450565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450565).length < 2 ^ (prefixWord ++ tailWord_450565).sum := by decide
  have hdescent : baseEnd_450565 < baseStart_450565 := by decide
  rcases family_descends (prefixWord ++ tailWord_450565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450591 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 3, 4]
def baseStart_450591 : Nat := 118140960795 + 450591 * 2 ^ 59
def prefixEnd_450591 : Nat := 4983230072969 + 3 ^ 40 * 450591 * 2
def baseEnd_450591 : Nat := 154246507726767862893517

theorem tailTrace_450591 : CollatzResearch.WordTrace tailWord_450591 prefixEnd_450591 154246507726767862893517 := by
  unfold tailWord_450591
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434403910593236661223627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10956269273728824440815751 16434403910593236661223627)
  ·
    refine ⟨24651605865889854991835441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16434403910593236661223627 24651605865889854991835441)
    ·
      refine ⟨18488704399417391243876581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24651605865889854991835441 18488704399417391243876581)
      ·
        refine ⟨3466632074890760858226859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18488704399417391243876581 3466632074890760858226859)
        ·
          refine ⟨5199948112336141287340289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466632074890760858226859 5199948112336141287340289)
          ·
            refine ⟨3899961084252105965505217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5199948112336141287340289 3899961084252105965505217)
            ·
              refine ⟨2924970813189079474128913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3899961084252105965505217 2924970813189079474128913)
              ·
                refine ⟨2193728109891809605596685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924970813189079474128913 2193728109891809605596685)
                ·
                  refine ⟨822648041209428602098757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2193728109891809605596685 822648041209428602098757)
                  ·
                    refine ⟨154246507726767862893517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 822648041209428602098757 154246507726767862893517)
                    ·
                      rfl

theorem cell22_450591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_450591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450591 prefixEnd_450591 := by exact prefixLift 450591
  have htrace : WordTrace (prefixWord ++ tailWord_450591) baseStart_450591 baseEnd_450591 := by
    simpa [prefixWord, tailWord_450591, baseEnd_450591] using wordTrace_append hprefix tailTrace_450591
  have hstable : (prefixWord ++ tailWord_450591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450591).length < 2 ^ (prefixWord ++ tailWord_450591).sum := by decide
  have hdescent : baseEnd_450591 < baseStart_450591 := by decide
  rcases family_descends (prefixWord ++ tailWord_450591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450608 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_450608 : Nat := 118140960795 + 450608 * 2 ^ 59
def prefixEnd_450608 : Nat := 4983230072969 + 3 ^ 40 * 450608 * 2
def baseEnd_450608 : Nat := 154252327174185485218465

theorem tailTrace_450608 : CollatzResearch.WordTrace tailWord_450608 prefixEnd_450608 154252327174185485218465 := by
  unfold tailWord_450608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217511975765824282296239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10956682634354432376394985 8217511975765824282296239)
  ·
    refine ⟨12326267963648736423444359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8217511975765824282296239 12326267963648736423444359)
    ·
      refine ⟨18489401945473104635166539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12326267963648736423444359 18489401945473104635166539)
      ·
        refine ⟨27734102918209656952749809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18489401945473104635166539 27734102918209656952749809)
        ·
          refine ⟨20800577188657242714562357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27734102918209656952749809 20800577188657242714562357)
          ·
            refine ⟨1950054111436616504490221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20800577188657242714562357 1950054111436616504490221)
            ·
              refine ⟨731270291788731189183833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950054111436616504490221 731270291788731189183833)
              ·
                refine ⟨548452718841548391887875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731270291788731189183833 548452718841548391887875)
                ·
                  refine ⟨822679078262322587831813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548452718841548391887875 822679078262322587831813)
                  ·
                    refine ⟨154252327174185485218465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 822679078262322587831813 154252327174185485218465)
                    ·
                      rfl

theorem cell22_450608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_450608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450608 prefixEnd_450608 := by exact prefixLift 450608
  have htrace : WordTrace (prefixWord ++ tailWord_450608) baseStart_450608 baseEnd_450608 := by
    simpa [prefixWord, tailWord_450608, baseEnd_450608] using wordTrace_append hprefix tailTrace_450608
  have hstable : (prefixWord ++ tailWord_450608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450608).length < 2 ^ (prefixWord ++ tailWord_450608).sum := by decide
  have hdescent : baseEnd_450608 < baseStart_450608 := by decide
  rcases family_descends (prefixWord ++ tailWord_450608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450668 : List Nat := [2, 2, 1, 1, 3, 4, 3, 6]
def baseStart_450668 : Nat := 118140960795 + 450668 * 2 ^ 59
def prefixEnd_450668 : Nat := 4983230072969 + 3 ^ 40 * 450668 * 2
def baseEnd_450668 : Nat := 17141429600040592079809

theorem tailTrace_450668 : CollatzResearch.WordTrace tailWord_450668 prefixEnd_450668 17141429600040592079809 := by
  unfold tailWord_450668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218606165657139405888329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10958141554209519207851105 8218606165657139405888329)
  ·
    refine ⟨6163954624242854554416247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8218606165657139405888329 6163954624242854554416247)
    ·
      refine ⟨9245931936364281831624371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163954624242854554416247 9245931936364281831624371)
      ·
        refine ⟨13868897904546422747436557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9245931936364281831624371 13868897904546422747436557)
        ·
          refine ⟨5200836714204908530288709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13868897904546422747436557 5200836714204908530288709)
          ·
            refine ⟨975156883913420349429133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5200836714204908530288709 975156883913420349429133)
            ·
              refine ⟨365683831467532631035925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 975156883913420349429133 365683831467532631035925)
              ·
                refine ⟨17141429600040592079809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365683831467532631035925 17141429600040592079809)
                ·
                  rfl

theorem cell22_450668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 6].length) (baseStart_450668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450668 prefixEnd_450668 := by exact prefixLift 450668
  have htrace : WordTrace (prefixWord ++ tailWord_450668) baseStart_450668 baseEnd_450668 := by
    simpa [prefixWord, tailWord_450668, baseEnd_450668] using wordTrace_append hprefix tailTrace_450668
  have hstable : (prefixWord ++ tailWord_450668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450668).length < 2 ^ (prefixWord ++ tailWord_450668).sum := by decide
  have hdescent : baseEnd_450668 < baseStart_450668 := by decide
  rcases family_descends (prefixWord ++ tailWord_450668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450689 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 2, 3]
def baseStart_450689 : Nat := 118140960795 + 450689 * 2 ^ 59
def prefixEnd_450689 : Nat := 4983230072969 + 3 ^ 40 * 450689 * 2
def baseEnd_450689 : Nat := 154280055129528273943217

theorem tailTrace_450689 : CollatzResearch.WordTrace tailWord_450689 prefixEnd_450689 154280055129528273943217 := by
  unfold tailWord_450689
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437978264238199398291121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10958652176158799598860747 16437978264238199398291121)
  ·
    refine ⟨12328483698178649548718341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16437978264238199398291121 12328483698178649548718341)
    ·
      refine ⟨2311590693408496790384689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12328483698178649548718341 2311590693408496790384689)
      ·
        refine ⟨1733693020056372592788517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2311590693408496790384689 1733693020056372592788517)
        ·
          refine ⟨325067441260569861147847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1733693020056372592788517 325067441260569861147847)
          ·
            refine ⟨487601161890854791721771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325067441260569861147847 487601161890854791721771)
            ·
              refine ⟨731401742836282187582657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487601161890854791721771 731401742836282187582657)
              ·
                refine ⟨548551307127211640686993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731401742836282187582657 548551307127211640686993)
                ·
                  refine ⟨411413480345408730515245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548551307127211640686993 411413480345408730515245)
                  ·
                    refine ⟨154280055129528273943217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411413480345408730515245 154280055129528273943217)
                    ·
                      rfl

theorem cell22_450689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_450689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450689 prefixEnd_450689 := by exact prefixLift 450689
  have htrace : WordTrace (prefixWord ++ tailWord_450689) baseStart_450689 baseEnd_450689 := by
    simpa [prefixWord, tailWord_450689, baseEnd_450689] using wordTrace_append hprefix tailTrace_450689
  have hstable : (prefixWord ++ tailWord_450689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450689).length < 2 ^ (prefixWord ++ tailWord_450689).sum := by decide
  have hdescent : baseEnd_450689 < baseStart_450689 := by decide
  rcases family_descends (prefixWord ++ tailWord_450689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450764 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 5]
def baseStart_450764 : Nat := 118140960795 + 450764 * 2 ^ 59
def prefixEnd_450764 : Nat := 4983230072969 + 3 ^ 40 * 450764 * 2
def baseEnd_450764 : Nat := 51435243054084359439329

theorem tailTrace_450764 : CollatzResearch.WordTrace tailWord_450764 prefixEnd_450764 51435243054084359439329 := by
  unfold tailWord_450764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220356869483243603635673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10960475825977658138180897 8220356869483243603635673)
  ·
    refine ⟨6165267652112432702726755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8220356869483243603635673 6165267652112432702726755)
    ·
      refine ⟨9247901478168649054090133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6165267652112432702726755 9247901478168649054090133)
      ·
        refine ⟨433495381789155424410475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9247901478168649054090133 433495381789155424410475)
        ·
          refine ⟨650243072683733136615713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433495381789155424410475 650243072683733136615713)
          ·
            refine ⟨487682304512799852461785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650243072683733136615713 487682304512799852461785)
            ·
              refine ⟨365761728384599889346339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487682304512799852461785 365761728384599889346339)
              ·
                refine ⟨548642592576899834019509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365761728384599889346339 548642592576899834019509)
                ·
                  refine ⟨51435243054084359439329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 548642592576899834019509 51435243054084359439329)
                  ·
                    rfl

theorem cell22_450764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_450764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450764 prefixEnd_450764 := by exact prefixLift 450764
  have htrace : WordTrace (prefixWord ++ tailWord_450764) baseStart_450764 baseEnd_450764 := by
    simpa [prefixWord, tailWord_450764, baseEnd_450764] using wordTrace_append hprefix tailTrace_450764
  have hstable : (prefixWord ++ tailWord_450764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450764).length < 2 ^ (prefixWord ++ tailWord_450764).sum := by decide
  have hdescent : baseEnd_450764 < baseStart_450764 := by decide
  rcases family_descends (prefixWord ++ tailWord_450764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450863 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 2, 5]
def baseStart_450863 : Nat := 118140960795 + 450863 * 2 ^ 59
def prefixEnd_450863 : Nat := 4983230072969 + 3 ^ 40 * 450863 * 2
def baseEnd_450863 : Nat := 154339618885449820092683

theorem tailTrace_450863 : CollatzResearch.WordTrace tailWord_450863 prefixEnd_450863 154339618885449820092683 := by
  unfold tailWord_450863
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444324565607827115125243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10962883043738551410083495 16444324565607827115125243)
  ·
    refine ⟨24666486848411740672687865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16444324565607827115125243 24666486848411740672687865)
    ·
      refine ⟨18499865136308805504515899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24666486848411740672687865 18499865136308805504515899)
      ·
        refine ⟨27749797704463208256773849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18499865136308805504515899 27749797704463208256773849)
        ·
          refine ⟨20812348278347406192580387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27749797704463208256773849 20812348278347406192580387)
          ·
            refine ⟨31218522417521109288870581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20812348278347406192580387 31218522417521109288870581)
            ·
              refine ⟨2926736476642603995831617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31218522417521109288870581 2926736476642603995831617)
              ·
                refine ⟨2195052357481952996873713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926736476642603995831617 2195052357481952996873713)
                ·
                  refine ⟨1646289268111464747655285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2195052357481952996873713 1646289268111464747655285)
                  ·
                    refine ⟨154339618885449820092683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1646289268111464747655285 154339618885449820092683)
                    ·
                      rfl

theorem cell22_450863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_450863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450863 prefixEnd_450863 := by exact prefixLift 450863
  have htrace : WordTrace (prefixWord ++ tailWord_450863) baseStart_450863 baseEnd_450863 := by
    simpa [prefixWord, tailWord_450863, baseEnd_450863] using wordTrace_append hprefix tailTrace_450863
  have hstable : (prefixWord ++ tailWord_450863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450863).length < 2 ^ (prefixWord ++ tailWord_450863).sum := by decide
  have hdescent : baseEnd_450863 < baseStart_450863 := by decide
  rcases family_descends (prefixWord ++ tailWord_450863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450865 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 7]
def baseStart_450865 : Nat := 118140960795 + 450865 * 2 ^ 59
def prefixEnd_450865 : Nat := 4983230072969 + 3 ^ 40 * 450865 * 2
def baseEnd_450865 : Nat := 51446767842107493847559

theorem tailTrace_450865 : CollatzResearch.WordTrace tailWord_450865 prefixEnd_450865 51446767842107493847559 := by
  unfold tailWord_450865
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444397511600581456698049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10962931674400387637798699 16444397511600581456698049)
  ·
    refine ⟨12333298133700436092523537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16444397511600581456698049 12333298133700436092523537)
    ·
      refine ⟨9249973600275327069392653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12333298133700436092523537 9249973600275327069392653)
      ·
        refine ⟨3468740100103247651022245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9249973600275327069392653 3468740100103247651022245)
        ·
          refine ⟨650388768769358934566671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3468740100103247651022245 650388768769358934566671)
          ·
            refine ⟨975583153154038401850007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650388768769358934566671 975583153154038401850007)
            ·
              refine ⟨1463374729731057602775011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975583153154038401850007 1463374729731057602775011)
              ·
                refine ⟨2195062094596586404162517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463374729731057602775011 2195062094596586404162517)
                ·
                  refine ⟨51446767842107493847559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2195062094596586404162517 51446767842107493847559)
                  ·
                    rfl

theorem cell22_450865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_450865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450865 prefixEnd_450865 := by exact prefixLift 450865
  have htrace : WordTrace (prefixWord ++ tailWord_450865) baseStart_450865 baseEnd_450865 := by
    simpa [prefixWord, tailWord_450865, baseEnd_450865] using wordTrace_append hprefix tailTrace_450865
  have hstable : (prefixWord ++ tailWord_450865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450865).length < 2 ^ (prefixWord ++ tailWord_450865).sum := by decide
  have hdescent : baseEnd_450865 < baseStart_450865 := by decide
  rcases family_descends (prefixWord ++ tailWord_450865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450974 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_450974 : Nat := 118140960795 + 450974 * 2 ^ 59
def prefixEnd_450974 : Nat := 4983230072969 + 3 ^ 40 * 450974 * 2
def baseEnd_450974 : Nat := 154377616453882530567343

theorem tailTrace_450974 : CollatzResearch.WordTrace tailWord_450974 prefixEnd_450974 154377616453882530567343 := by
  unfold tailWord_450974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2056046633525711634051997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10965582045470462048277317 2056046633525711634051997)
  ·
    refine ⟨771017487572141862769499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2056046633525711634051997 771017487572141862769499)
    ·
      refine ⟨1156526231358212794154249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771017487572141862769499 1156526231358212794154249)
      ·
        refine ⟨867394673518659595615687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1156526231358212794154249 867394673518659595615687)
        ·
          refine ⟨1301092010277989393423531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867394673518659595615687 1301092010277989393423531)
          ·
            refine ⟨1951638015416984090135297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301092010277989393423531 1951638015416984090135297)
            ·
              refine ⟨1463728511562738067601473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951638015416984090135297 1463728511562738067601473)
              ·
                refine ⟨1097796383672053550701105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463728511562738067601473 1097796383672053550701105)
                ·
                  refine ⟨823347287754040163025829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1097796383672053550701105 823347287754040163025829)
                  ·
                    refine ⟨154377616453882530567343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823347287754040163025829 154377616453882530567343)
                    ·
                      rfl

theorem cell22_450974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_450974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450974 prefixEnd_450974 := by exact prefixLift 450974
  have htrace : WordTrace (prefixWord ++ tailWord_450974) baseStart_450974 baseEnd_450974 := by
    simpa [prefixWord, tailWord_450974, baseEnd_450974] using wordTrace_append hprefix tailTrace_450974
  have hstable : (prefixWord ++ tailWord_450974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450974).length < 2 ^ (prefixWord ++ tailWord_450974).sum := by decide
  have hdescent : baseEnd_450974 < baseStart_450974 := by decide
  rcases family_descends (prefixWord ++ tailWord_450974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450989 : List Nat := [1, 5, 2, 2, 2, 2, 1, 7]
def baseStart_450989 : Nat := 118140960795 + 450989 * 2 ^ 59
def prefixEnd_450989 : Nat := 4983230072969 + 3 ^ 40 * 450989 * 2
def baseEnd_450989 : Nat := 17153639028936387938033

theorem tailTrace_450989 : CollatzResearch.WordTrace tailWord_450989 prefixEnd_450989 17153639028936387938033 := by
  unfold tailWord_450989
  simp only [CollatzResearch.WordTrace]
  refine ⟨16448920163151350634212021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10965946775434233756141347 16448920163151350634212021)
  ·
    refine ⟨1542086265295439121957377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16448920163151350634212021 1542086265295439121957377)
    ·
      refine ⟨1156564698971579341468033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542086265295439121957377 1156564698971579341468033)
      ·
        refine ⟨867423524228684506101025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1156564698971579341468033 867423524228684506101025)
        ·
          refine ⟨650567643171513379575769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867423524228684506101025 650567643171513379575769)
          ·
            refine ⟨487925732378635034681827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650567643171513379575769 487925732378635034681827)
            ·
              refine ⟨731888598567952552022741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487925732378635034681827 731888598567952552022741)
              ·
                refine ⟨17153639028936387938033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 731888598567952552022741 17153639028936387938033)
                ·
                  rfl

theorem cell22_450989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 7].length) (baseStart_450989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_450989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_450989 prefixEnd_450989 := by exact prefixLift 450989
  have htrace : WordTrace (prefixWord ++ tailWord_450989) baseStart_450989 baseEnd_450989 := by
    simpa [prefixWord, tailWord_450989, baseEnd_450989] using wordTrace_append hprefix tailTrace_450989
  have hstable : (prefixWord ++ tailWord_450989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450989).length < 2 ^ (prefixWord ++ tailWord_450989).sum := by decide
  have hdescent : baseEnd_450989 < baseStart_450989 := by decide
  rcases family_descends (prefixWord ++ tailWord_450989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451004 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_451004 : Nat := 118140960795 + 451004 * 2 ^ 59
def prefixEnd_451004 : Nat := 4983230072969 + 3 ^ 40 * 451004 * 2
def baseEnd_451004 : Nat := 154387886066972452317251

theorem tailTrace_451004 : CollatzResearch.WordTrace tailWord_451004 prefixEnd_451004 154387886066972452317251 := by
  unfold tailWord_451004
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224733629048504098004033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10966311505398005464005377 8224733629048504098004033)
  ·
    refine ⟨6168550221786378073503025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8224733629048504098004033 6168550221786378073503025)
    ·
      refine ⟨4626412666339783555127269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6168550221786378073503025 4626412666339783555127269)
      ·
        refine ⟨867452374938709416586363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4626412666339783555127269 867452374938709416586363)
        ·
          refine ⟨1301178562408064124879545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867452374938709416586363 1301178562408064124879545)
          ·
            refine ⟨975883921806048093659659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301178562408064124879545 975883921806048093659659)
            ·
              refine ⟨1463825882709072140489489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975883921806048093659659 1463825882709072140489489)
              ·
                refine ⟨1097869412031804105367117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463825882709072140489489 1097869412031804105367117)
                ·
                  refine ⟨411701029511926539512669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097869412031804105367117 411701029511926539512669)
                  ·
                    refine ⟨154387886066972452317251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411701029511926539512669 154387886066972452317251)
                    ·
                      rfl

theorem cell22_451004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_451004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451004 prefixEnd_451004 := by exact prefixLift 451004
  have htrace : WordTrace (prefixWord ++ tailWord_451004) baseStart_451004 baseEnd_451004 := by
    simpa [prefixWord, tailWord_451004, baseEnd_451004] using wordTrace_append hprefix tailTrace_451004
  have hstable : (prefixWord ++ tailWord_451004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451004).length < 2 ^ (prefixWord ++ tailWord_451004).sum := by decide
  have hdescent : baseEnd_451004 < baseStart_451004 := by decide
  rcases family_descends (prefixWord ++ tailWord_451004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451062 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_451062 : Nat := 118140960795 + 451062 * 2 ^ 59
def prefixEnd_451062 : Nat := 4983230072969 + 3 ^ 40 * 451062 * 2
def baseEnd_451062 : Nat := 51469246884093211455691

theorem tailTrace_451062 : CollatzResearch.WordTrace tailWord_451062 prefixEnd_451062 51469246884093211455691 := by
  unfold tailWord_451062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028223918242930256351215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10967721794591256067746293 1028223918242930256351215)
  ·
    refine ⟨1542335877364395384526823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028223918242930256351215 1542335877364395384526823)
    ·
      refine ⟨2313503816046593076790235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542335877364395384526823 2313503816046593076790235)
      ·
        refine ⟨3470255724069889615185353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313503816046593076790235 3470255724069889615185353)
        ·
          refine ⟨2602691793052417211389015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3470255724069889615185353 2602691793052417211389015)
          ·
            refine ⟨3904037689578625817083523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602691793052417211389015 3904037689578625817083523)
            ·
              refine ⟨5856056534367938725625285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904037689578625817083523 5856056534367938725625285)
              ·
                refine ⟨1098010600193988511054741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5856056534367938725625285 1098010600193988511054741)
                ·
                  refine ⟨51469246884093211455691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1098010600193988511054741 51469246884093211455691)
                  ·
                    rfl

theorem cell22_451062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_451062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451062 prefixEnd_451062 := by exact prefixLift 451062
  have htrace : WordTrace (prefixWord ++ tailWord_451062) baseStart_451062 baseEnd_451062 := by
    simpa [prefixWord, tailWord_451062, baseEnd_451062] using wordTrace_append hprefix tailTrace_451062
  have hstable : (prefixWord ++ tailWord_451062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451062).length < 2 ^ (prefixWord ++ tailWord_451062).sum := by decide
  have hdescent : baseEnd_451062 < baseStart_451062 := by decide
  rcases family_descends (prefixWord ++ tailWord_451062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451075 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 1, 6]
def baseStart_451075 : Nat := 118140960795 + 451075 * 2 ^ 59
def prefixEnd_451075 : Nat := 4983230072969 + 3 ^ 40 * 451075 * 2
def baseEnd_451075 : Nat := 154412190817951933792033

theorem tailTrace_451075 : CollatzResearch.WordTrace tailWord_451075 prefixEnd_451075 154412190817951933792033 := by
  unfold tailWord_451075
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452056840839787321842679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10968037893893191547895119 16452056840839787321842679)
  ·
    refine ⟨24678085261259680982764019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16452056840839787321842679 24678085261259680982764019)
    ·
      refine ⟨37017127891889521474146029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24678085261259680982764019 37017127891889521474146029)
      ·
        refine ⟨13881422959458570552804761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37017127891889521474146029 13881422959458570552804761)
        ·
          refine ⟨10411067219593927914603571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13881422959458570552804761 10411067219593927914603571)
          ·
            refine ⟨15616600829390891871905357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10411067219593927914603571 15616600829390891871905357)
            ·
              refine ⟨5856225311021584451964509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15616600829390891871905357 5856225311021584451964509)
              ·
                refine ⟨2196084491633094169486691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5856225311021584451964509 2196084491633094169486691)
                ·
                  refine ⟨3294126737449641254230037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196084491633094169486691 3294126737449641254230037)
                  ·
                    refine ⟨154412190817951933792033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3294126737449641254230037 154412190817951933792033)
                    ·
                      rfl

theorem cell22_451075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_451075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451075 prefixEnd_451075 := by exact prefixLift 451075
  have htrace : WordTrace (prefixWord ++ tailWord_451075) baseStart_451075 baseEnd_451075 := by
    simpa [prefixWord, tailWord_451075, baseEnd_451075] using wordTrace_append hprefix tailTrace_451075
  have hstable : (prefixWord ++ tailWord_451075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451075).length < 2 ^ (prefixWord ++ tailWord_451075).sum := by decide
  have hdescent : baseEnd_451075 < baseStart_451075 := by decide
  rcases family_descends (prefixWord ++ tailWord_451075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451077 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_451077 : Nat := 118140960795 + 451077 * 2 ^ 59
def prefixEnd_451077 : Nat := 4983230072969 + 3 ^ 40 * 451077 * 2
def baseEnd_451077 : Nat := 154412875458824595242027

theorem tailTrace_451077 : CollatzResearch.WordTrace tailWord_451077 prefixEnd_451077 154412875458824595242027 := by
  unfold tailWord_451077
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452129786832541663415485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10968086524555027775610323 16452129786832541663415485)
  ·
    refine ⟨6169548670062203123780807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16452129786832541663415485 6169548670062203123780807)
    ·
      refine ⟨9254323005093304685671211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6169548670062203123780807 9254323005093304685671211)
      ·
        refine ⟨13881484507639957028506817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9254323005093304685671211 13881484507639957028506817)
        ·
          refine ⟨10411113380729967771380113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13881484507639957028506817 10411113380729967771380113)
          ·
            refine ⟨7808335035547475828535085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10411113380729967771380113 7808335035547475828535085)
            ·
              refine ⟨2928125638330303435700657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7808335035547475828535085 2928125638330303435700657)
              ·
                refine ⟨2196094228747727576775493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928125638330303435700657 2196094228747727576775493)
                ·
                  refine ⟨411767667890198920645405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196094228747727576775493 411767667890198920645405)
                  ·
                    refine ⟨154412875458824595242027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411767667890198920645405 154412875458824595242027)
                    ·
                      rfl

theorem cell22_451077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_451077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451077 prefixEnd_451077 := by exact prefixLift 451077
  have htrace : WordTrace (prefixWord ++ tailWord_451077) baseStart_451077 baseEnd_451077 := by
    simpa [prefixWord, tailWord_451077, baseEnd_451077] using wordTrace_append hprefix tailTrace_451077
  have hstable : (prefixWord ++ tailWord_451077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451077).length < 2 ^ (prefixWord ++ tailWord_451077).sum := by decide
  have hdescent : baseEnd_451077 < baseStart_451077 := by decide
  rcases family_descends (prefixWord ++ tailWord_451077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451096 : List Nat := [2, 1, 2, 3, 3, 2, 3, 2, 4]
def baseStart_451096 : Nat := 118140960795 + 451096 * 2 ^ 59
def prefixEnd_451096 : Nat := 4983230072969 + 3 ^ 40 * 451096 * 2
def baseEnd_451096 : Nat := 51473126515704959672323

theorem tailTrace_451096 : CollatzResearch.WordTrace tailWord_451096 prefixEnd_451096 51473126515704959672323 := by
  unfold tailWord_451096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226411386881853954178571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10968548515842471938904761 8226411386881853954178571)
  ·
    refine ⟨12339617080322780931267857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8226411386881853954178571 12339617080322780931267857)
    ·
      refine ⟨9254712810242085698450893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12339617080322780931267857 9254712810242085698450893)
      ·
        refine ⟨3470517303840782136919085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9254712810242085698450893 3470517303840782136919085)
        ·
          refine ⟨1301443988940293301344657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3470517303840782136919085 1301443988940293301344657)
          ·
            refine ⟨976082991705219976008493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301443988940293301344657 976082991705219976008493)
            ·
              refine ⟨366031121889457491003185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 976082991705219976008493 366031121889457491003185)
              ·
                refine ⟨274523341417093118252389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366031121889457491003185 274523341417093118252389)
                ·
                  refine ⟨51473126515704959672323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274523341417093118252389 51473126515704959672323)
                  ·
                    rfl

theorem cell22_451096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_451096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451096 prefixEnd_451096 := by exact prefixLift 451096
  have htrace : WordTrace (prefixWord ++ tailWord_451096) baseStart_451096 baseEnd_451096 := by
    simpa [prefixWord, tailWord_451096, baseEnd_451096] using wordTrace_append hprefix tailTrace_451096
  have hstable : (prefixWord ++ tailWord_451096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451096).length < 2 ^ (prefixWord ++ tailWord_451096).sum := by decide
  have hdescent : baseEnd_451096 < baseStart_451096 := by decide
  rcases family_descends (prefixWord ++ tailWord_451096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451107 : List Nat := [1, 1, 1, 4, 4, 2, 2, 7]
def baseStart_451107 : Nat := 118140960795 + 451107 * 2 ^ 59
def prefixEnd_451107 : Nat := 4983230072969 + 3 ^ 40 * 451107 * 2
def baseEnd_451107 : Nat := 17158127230212724110215

theorem tailTrace_451107 : CollatzResearch.WordTrace tailWord_451107 prefixEnd_451107 17158127230212724110215 := by
  unfold tailWord_451107
  simp only [CollatzResearch.WordTrace]
  refine ⟨16453223976723856787007575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10968815984482571191338383 16453223976723856787007575)
  ·
    refine ⟨24679835965085785180511363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16453223976723856787007575 24679835965085785180511363)
    ·
      refine ⟨37019753947628677770767045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24679835965085785180511363 37019753947628677770767045)
      ·
        refine ⟨6941203865180377082018821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37019753947628677770767045 6941203865180377082018821)
        ·
          refine ⟨1301475724721320702878529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6941203865180377082018821 1301475724721320702878529)
          ·
            refine ⟨976106793540990527158897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301475724721320702878529 976106793540990527158897)
            ·
              refine ⟨732080095155742895369173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976106793540990527158897 732080095155742895369173)
              ·
                refine ⟨17158127230212724110215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 732080095155742895369173 17158127230212724110215)
                ·
                  rfl

theorem cell22_451107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 7].length) (baseStart_451107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451107 prefixEnd_451107 := by exact prefixLift 451107
  have htrace : WordTrace (prefixWord ++ tailWord_451107) baseStart_451107 baseEnd_451107 := by
    simpa [prefixWord, tailWord_451107, baseEnd_451107] using wordTrace_append hprefix tailTrace_451107
  have hstable : (prefixWord ++ tailWord_451107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451107).length < 2 ^ (prefixWord ++ tailWord_451107).sum := by decide
  have hdescent : baseEnd_451107 < baseStart_451107 := by decide
  rcases family_descends (prefixWord ++ tailWord_451107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451126 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_451126 : Nat := 118140960795 + 451126 * 2 ^ 59
def prefixEnd_451126 : Nat := 4983230072969 + 3 ^ 40 * 451126 * 2
def baseEnd_451126 : Nat := 154429649160204800766877

theorem tailTrace_451126 : CollatzResearch.WordTrace tailWord_451126 prefixEnd_451126 154429649160204800766877 := by
  unfold tailWord_451126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028369810228438939496827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10969277975770015354632821 1028369810228438939496827)
  ·
    refine ⟨1542554715342658409245241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028369810228438939496827 1542554715342658409245241)
    ·
      refine ⟨1156916036506993806933931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542554715342658409245241 1156916036506993806933931)
      ·
        refine ⟨1735374054760490710400897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156916036506993806933931 1735374054760490710400897)
        ·
          refine ⟨1301530541070368032800673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1735374054760490710400897 1301530541070368032800673)
          ·
            refine ⟨976147905802776024600505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301530541070368032800673 976147905802776024600505)
            ·
              refine ⟨732110929352082018450379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976147905802776024600505 732110929352082018450379)
              ·
                refine ⟨1098166394028123027675569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732110929352082018450379 1098166394028123027675569)
                ·
                  refine ⟨823624795521092270756677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098166394028123027675569 823624795521092270756677)
                  ·
                    refine ⟨154429649160204800766877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823624795521092270756677 154429649160204800766877)
                    ·
                      rfl

theorem cell22_451126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_451126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451126 prefixEnd_451126 := by exact prefixLift 451126
  have htrace : WordTrace (prefixWord ++ tailWord_451126) baseStart_451126 baseEnd_451126 := by
    simpa [prefixWord, tailWord_451126, baseEnd_451126] using wordTrace_append hprefix tailTrace_451126
  have hstable : (prefixWord ++ tailWord_451126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451126).length < 2 ^ (prefixWord ++ tailWord_451126).sum := by decide
  have hdescent : baseEnd_451126 < baseStart_451126 := by decide
  rcases family_descends (prefixWord ++ tailWord_451126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451190 : List Nat := [5, 1, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_451190 : Nat := 118140960795 + 451190 * 2 ^ 59
def prefixEnd_451190 : Nat := 4983230072969 + 3 ^ 40 * 451190 * 2
def baseEnd_451190 : Nat := 154451557668129967166681

theorem tailTrace_451190 : CollatzResearch.WordTrace tailWord_451190 prefixEnd_451190 154451557668129967166681 := by
  unfold tailWord_451190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028515702213947622642439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10970834156948774641519349 1028515702213947622642439)
  ·
    refine ⟨1542773553320921433963659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028515702213947622642439 1542773553320921433963659)
    ·
      refine ⟨2314160329981382150945489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542773553320921433963659 2314160329981382150945489)
      ·
        refine ⟨1735620247486036613209117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2314160329981382150945489 1735620247486036613209117)
        ·
          refine ⟨650857592807263729953419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1735620247486036613209117 650857592807263729953419)
          ·
            refine ⟨976286389210895594930129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650857592807263729953419 976286389210895594930129)
            ·
              refine ⟨732214791908171696197597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976286389210895594930129 732214791908171696197597)
              ·
                refine ⟨274580546965564386074099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732214791908171696197597 274580546965564386074099)
                ·
                  refine ⟨411870820448346579111149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274580546965564386074099 411870820448346579111149)
                  ·
                    refine ⟨154451557668129967166681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 411870820448346579111149 154451557668129967166681)
                    ·
                      rfl

theorem cell22_451190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_451190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451190 prefixEnd_451190 := by exact prefixLift 451190
  have htrace : WordTrace (prefixWord ++ tailWord_451190) baseStart_451190 baseEnd_451190 := by
    simpa [prefixWord, tailWord_451190, baseEnd_451190] using wordTrace_append hprefix tailTrace_451190
  have hstable : (prefixWord ++ tailWord_451190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451190).length < 2 ^ (prefixWord ++ tailWord_451190).sum := by decide
  have hdescent : baseEnd_451190 < baseStart_451190 := by decide
  rcases family_descends (prefixWord ++ tailWord_451190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451214 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_451214 : Nat := 118140960795 + 451214 * 2 ^ 59
def prefixEnd_451214 : Nat := 4983230072969 + 3 ^ 40 * 451214 * 2
def baseEnd_451214 : Nat := 51486591119533968188869

theorem tailTrace_451214 : CollatzResearch.WordTrace tailWord_451214 prefixEnd_451214 51486591119533968188869 := by
  unfold tailWord_451214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057140823417026757644087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10971417724890809374101797 2057140823417026757644087)
  ·
    refine ⟨3085711235125540136466131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2057140823417026757644087 3085711235125540136466131)
    ·
      refine ⟨4628566852688310204699197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3085711235125540136466131 4628566852688310204699197)
      ·
        refine ⟨1735712569758116326762199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4628566852688310204699197 1735712569758116326762199)
        ·
          refine ⟨2603568854637174490143299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735712569758116326762199 2603568854637174490143299)
          ·
            refine ⟨3905353281955761735214949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603568854637174490143299 3905353281955761735214949)
            ·
              refine ⟨732253740366705325352803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3905353281955761735214949 732253740366705325352803)
              ·
                refine ⟨1098380610550057988029205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732253740366705325352803 1098380610550057988029205)
                ·
                  refine ⟨51486591119533968188869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1098380610550057988029205 51486591119533968188869)
                  ·
                    rfl

theorem cell22_451214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_451214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451214 prefixEnd_451214 := by exact prefixLift 451214
  have htrace : WordTrace (prefixWord ++ tailWord_451214) baseStart_451214 baseEnd_451214 := by
    simpa [prefixWord, tailWord_451214, baseEnd_451214] using wordTrace_append hprefix tailTrace_451214
  have hstable : (prefixWord ++ tailWord_451214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451214).length < 2 ^ (prefixWord ++ tailWord_451214).sum := by decide
  have hdescent : baseEnd_451214 < baseStart_451214 := by decide
  rcases family_descends (prefixWord ++ tailWord_451214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451229 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_451229 : Nat := 118140960795 + 451229 * 2 ^ 59
def prefixEnd_451229 : Nat := 4983230072969 + 3 ^ 40 * 451229 * 2
def baseEnd_451229 : Nat := 154464908165146865441561

theorem tailTrace_451229 : CollatzResearch.WordTrace tailWord_451229 prefixEnd_451229 154464908165146865441561 := by
  unfold tailWord_451229
  simp only [CollatzResearch.WordTrace]
  refine ⟨16457673682281871622948741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10971782454854581081965827 16457673682281871622948741)
  ·
    refine ⟨3085813815427850929302889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16457673682281871622948741 3085813815427850929302889)
    ·
      refine ⟨2314360361570888196977167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3085813815427850929302889 2314360361570888196977167)
      ·
        refine ⟨3471540542356332295465751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314360361570888196977167 3471540542356332295465751)
        ·
          refine ⟨5207310813534498443198627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471540542356332295465751 5207310813534498443198627)
          ·
            refine ⟨7810966220301747664797941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207310813534498443198627 7810966220301747664797941)
            ·
              refine ⟨732278083153288843574807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7810966220301747664797941 732278083153288843574807)
              ·
                refine ⟨1098417124729933265362211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732278083153288843574807 1098417124729933265362211)
                ·
                  refine ⟨1647625687094899898043317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098417124729933265362211 1647625687094899898043317)
                  ·
                    refine ⟨154464908165146865441561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1647625687094899898043317 154464908165146865441561)
                    ·
                      rfl

theorem cell22_451229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_451229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451229 prefixEnd_451229 := by exact prefixLift 451229
  have htrace : WordTrace (prefixWord ++ tailWord_451229) baseStart_451229 baseEnd_451229 := by
    simpa [prefixWord, tailWord_451229, baseEnd_451229] using wordTrace_append hprefix tailTrace_451229
  have hstable : (prefixWord ++ tailWord_451229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451229).length < 2 ^ (prefixWord ++ tailWord_451229).sum := by decide
  have hdescent : baseEnd_451229 < baseStart_451229 := by decide
  rcases family_descends (prefixWord ++ tailWord_451229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451265 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 6]
def baseStart_451265 : Nat := 118140960795 + 451265 * 2 ^ 59
def prefixEnd_451265 : Nat := 4983230072969 + 3 ^ 40 * 451265 * 2
def baseEnd_451265 : Nat := 51492410566951590513817

theorem tailTrace_451265 : CollatzResearch.WordTrace tailWord_451265 prefixEnd_451265 51492410566951590513817 := by
  unfold tailWord_451265
  simp only [CollatzResearch.WordTrace]
  refine ⟨16458986710151449771259249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10972657806767633180839499 16458986710151449771259249)
  ·
    refine ⟨12344240032613587328444437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16458986710151449771259249 12344240032613587328444437)
    ·
      refine ⟨578636251528761906020833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12344240032613587328444437 578636251528761906020833)
      ·
        refine ⟨433977188646571429515625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578636251528761906020833 433977188646571429515625)
        ·
          refine ⟨325482891484928572136719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433977188646571429515625 325482891484928572136719)
          ·
            refine ⟨488224337227392858205079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325482891484928572136719 488224337227392858205079)
            ·
              refine ⟨732336505841089287307619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488224337227392858205079 732336505841089287307619)
              ·
                refine ⟨1098504758761633930961429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732336505841089287307619 1098504758761633930961429)
                ·
                  refine ⟨51492410566951590513817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1098504758761633930961429 51492410566951590513817)
                  ·
                    rfl

theorem cell22_451265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_451265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451265 prefixEnd_451265 := by exact prefixLift 451265
  have htrace : WordTrace (prefixWord ++ tailWord_451265) baseStart_451265 baseEnd_451265 := by
    simpa [prefixWord, tailWord_451265, baseEnd_451265] using wordTrace_append hprefix tailTrace_451265
  have hstable : (prefixWord ++ tailWord_451265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451265).length < 2 ^ (prefixWord ++ tailWord_451265).sum := by decide
  have hdescent : baseEnd_451265 < baseStart_451265 := by decide
  rcases family_descends (prefixWord ++ tailWord_451265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451349 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 6]
def baseStart_451349 : Nat := 118140960795 + 451349 * 2 ^ 59
def prefixEnd_451349 : Nat := 4983230072969 + 3 ^ 40 * 451349 * 2
def baseEnd_451349 : Nat := 51501995539168850813731

theorem tailTrace_451349 : CollatzResearch.WordTrace tailWord_451349 prefixEnd_451349 51501995539168850813731 := by
  unfold tailWord_451349
  simp only [CollatzResearch.WordTrace]
  refine ⟨16462050441847132117317101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10974700294564754744878067 16462050441847132117317101)
  ·
    refine ⟨6173268915692674543993913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16462050441847132117317101 6173268915692674543993913)
    ·
      refine ⟨4629951686769505907995435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6173268915692674543993913 4629951686769505907995435)
      ·
        refine ⟨6944927530154258861993153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629951686769505907995435 6944927530154258861993153)
        ·
          refine ⟨5208695647615694146494865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6944927530154258861993153 5208695647615694146494865)
          ·
            refine ⟨3906521735711770609871149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5208695647615694146494865 3906521735711770609871149)
            ·
              refine ⟨1464945650891913978701681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3906521735711770609871149 1464945650891913978701681)
              ·
                refine ⟨1098709238168935484026261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464945650891913978701681 1098709238168935484026261)
                ·
                  refine ⟨51501995539168850813731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1098709238168935484026261 51501995539168850813731)
                  ·
                    rfl

theorem cell22_451349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_451349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451349 prefixEnd_451349 := by exact prefixLift 451349
  have htrace : WordTrace (prefixWord ++ tailWord_451349) baseStart_451349 baseEnd_451349 := by
    simpa [prefixWord, tailWord_451349, baseEnd_451349] using wordTrace_append hprefix tailTrace_451349
  have hstable : (prefixWord ++ tailWord_451349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451349).length < 2 ^ (prefixWord ++ tailWord_451349).sum := by decide
  have hdescent : baseEnd_451349 < baseStart_451349 := by decide
  rcases family_descends (prefixWord ++ tailWord_451349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451443 : List Nat := [1, 1, 1, 2, 2, 1, 4, 6, 1, 3]
def baseStart_451443 : Nat := 118140960795 + 451443 * 2 ^ 59
def prefixEnd_451443 : Nat := 4983230072969 + 3 ^ 40 * 451443 * 2
def baseEnd_451443 : Nat := 154538164738521640590905

theorem tailTrace_451443 : CollatzResearch.WordTrace tailWord_451443 prefixEnd_451443 154538164738521640590905 := by
  unfold tailWord_451443
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465478903506586171238983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10976985935671057447492655 16465478903506586171238983)
  ·
    refine ⟨24698218355259879256858475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16465478903506586171238983 24698218355259879256858475)
    ·
      refine ⟨37047327532889818885287713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24698218355259879256858475 37047327532889818885287713)
      ·
        refine ⟨27785495649667364163965785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37047327532889818885287713 27785495649667364163965785)
        ·
          refine ⟨20839121737250523122974339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27785495649667364163965785 20839121737250523122974339)
          ·
            refine ⟨31258682605875784684461509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20839121737250523122974339 31258682605875784684461509)
            ·
              refine ⟨5861002988601709628336533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31258682605875784684461509 5861002988601709628336533)
              ·
                refine ⟨274734515090705138828275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5861002988601709628336533 274734515090705138828275)
                ·
                  refine ⟨412101772636057708242413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274734515090705138828275 412101772636057708242413)
                  ·
                    refine ⟨154538164738521640590905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 412101772636057708242413 154538164738521640590905)
                    ·
                      rfl

theorem cell22_451443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 3].length) (baseStart_451443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451443 prefixEnd_451443 := by exact prefixLift 451443
  have htrace : WordTrace (prefixWord ++ tailWord_451443) baseStart_451443 baseEnd_451443 := by
    simpa [prefixWord, tailWord_451443, baseEnd_451443] using wordTrace_append hprefix tailTrace_451443
  have hstable : (prefixWord ++ tailWord_451443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451443).length < 2 ^ (prefixWord ++ tailWord_451443).sum := by decide
  have hdescent : baseEnd_451443 < baseStart_451443 := by decide
  rcases family_descends (prefixWord ++ tailWord_451443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451531 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 1, 6]
def baseStart_451531 : Nat := 118140960795 + 451531 * 2 ^ 59
def prefixEnd_451531 : Nat := 4983230072969 + 3 ^ 40 * 451531 * 2
def baseEnd_451531 : Nat := 154568288936918744390635

theorem tailTrace_451531 : CollatzResearch.WordTrace tailWord_451531 prefixEnd_451531 154568288936918744390635 := by
  unfold tailWord_451531
  simp only [CollatzResearch.WordTrace]
  refine ⟨16468688527187777200442447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10979125684791851466961631 16468688527187777200442447)
  ·
    refine ⟨24703032790781665800663671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16468688527187777200442447 24703032790781665800663671)
    ·
      refine ⟨37054549186172498700995507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24703032790781665800663671 37054549186172498700995507)
      ·
        refine ⟨55581823779258748051493261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37054549186172498700995507 55581823779258748051493261)
        ·
          refine ⟨20843183917222030519309973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55581823779258748051493261 20843183917222030519309973)
          ·
            refine ⟨977024246119782680592655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20843183917222030519309973 977024246119782680592655)
            ·
              refine ⟨1465536369179674020888983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977024246119782680592655 1465536369179674020888983)
              ·
                refine ⟨2198304553769511031333475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465536369179674020888983 2198304553769511031333475)
                ·
                  refine ⟨3297456830654266547000213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198304553769511031333475 3297456830654266547000213)
                  ·
                    refine ⟨154568288936918744390635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3297456830654266547000213 154568288936918744390635)
                    ·
                      rfl

theorem cell22_451531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_451531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451531 prefixEnd_451531 := by exact prefixLift 451531
  have htrace : WordTrace (prefixWord ++ tailWord_451531) baseStart_451531 baseEnd_451531 := by
    simpa [prefixWord, tailWord_451531, baseEnd_451531] using wordTrace_append hprefix tailTrace_451531
  have hstable : (prefixWord ++ tailWord_451531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451531).length < 2 ^ (prefixWord ++ tailWord_451531).sum := by decide
  have hdescent : baseEnd_451531 < baseStart_451531 := by decide
  rcases family_descends (prefixWord ++ tailWord_451531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451546 : List Nat := [3, 1, 1, 2, 4, 2, 9]
def baseStart_451546 : Nat := 118140960795 + 451546 * 2 ^ 59
def prefixEnd_451546 : Nat := 4983230072969 + 3 ^ 40 * 451546 * 2
def baseEnd_451546 : Nat := 5724941620128285380207

theorem tailTrace_451546 : CollatzResearch.WordTrace tailWord_451546 prefixEnd_451546 5724941620128285380207 := by
  unfold tailWord_451546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117308905533358690559623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10979490414755623174825661 4117308905533358690559623)
  ·
    refine ⟨6175963358300038035839435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117308905533358690559623 6175963358300038035839435)
    ·
      refine ⟨9263945037450057053759153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175963358300038035839435 9263945037450057053759153)
      ·
        refine ⟨6947958778087542790319365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9263945037450057053759153 6947958778087542790319365)
        ·
          refine ⟨1302742270891414273184881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6947958778087542790319365 1302742270891414273184881)
          ·
            refine ⟨977056703168560704888661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302742270891414273184881 977056703168560704888661)
            ·
              refine ⟨5724941620128285380207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 977056703168560704888661 5724941620128285380207)
              ·
                rfl

theorem cell22_451546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 9].length) (baseStart_451546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451546 prefixEnd_451546 := by exact prefixLift 451546
  have htrace : WordTrace (prefixWord ++ tailWord_451546) baseStart_451546 baseEnd_451546 := by
    simpa [prefixWord, tailWord_451546, baseEnd_451546] using wordTrace_append hprefix tailTrace_451546
  have hstable : (prefixWord ++ tailWord_451546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451546).length < 2 ^ (prefixWord ++ tailWord_451546).sum := by decide
  have hdescent : baseEnd_451546 < baseStart_451546 := by decide
  rcases family_descends (prefixWord ++ tailWord_451546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451586 : List Nat := [3, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_451586 : Nat := 118140960795 + 451586 * 2 ^ 59
def prefixEnd_451586 : Nat := 4983230072969 + 3 ^ 40 * 451586 * 2
def baseEnd_451586 : Nat := 51529038853638978088489

theorem tailTrace_451586 : CollatzResearch.WordTrace tailWord_451586 prefixEnd_451586 51529038853638978088489 := by
  unfold tailWord_451586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117673635497130398423653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10980463027992347729129741 4117673635497130398423653)
  ·
    refine ⟨772063806655711949704435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4117673635497130398423653 772063806655711949704435)
    ·
      refine ⟨1158095709983567924556653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 772063806655711949704435 1158095709983567924556653)
      ·
        refine ⟨434285891243837971708745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1158095709983567924556653 434285891243837971708745)
        ·
          refine ⟨325714418432878478781559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434285891243837971708745 325714418432878478781559)
          ·
            refine ⟨488571627649317718172339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325714418432878478781559 488571627649317718172339)
            ·
              refine ⟨732857441473976577258509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488571627649317718172339 732857441473976577258509)
              ·
                refine ⟨274821540552741216471941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732857441473976577258509 274821540552741216471941)
                ·
                  refine ⟨51529038853638978088489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274821540552741216471941 51529038853638978088489)
                  ·
                    rfl

theorem cell22_451586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_451586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451586 prefixEnd_451586 := by exact prefixLift 451586
  have htrace : WordTrace (prefixWord ++ tailWord_451586) baseStart_451586 baseEnd_451586 := by
    simpa [prefixWord, tailWord_451586, baseEnd_451586] using wordTrace_append hprefix tailTrace_451586
  have hstable : (prefixWord ++ tailWord_451586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451586).length < 2 ^ (prefixWord ++ tailWord_451586).sum := by decide
  have hdescent : baseEnd_451586 < baseStart_451586 := by decide
  rcases family_descends (prefixWord ++ tailWord_451586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451591 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 9]
def baseStart_451591 : Nat := 118140960795 + 451591 * 2 ^ 59
def prefixEnd_451591 : Nat := 4983230072969 + 3 ^ 40 * 451591 * 2
def baseEnd_451591 : Nat := 51529609387699529296817

theorem tailTrace_451591 : CollatzResearch.WordTrace tailWord_451591 prefixEnd_451591 51529609387699529296817 := by
  unfold tailWord_451591
  simp only [CollatzResearch.WordTrace]
  refine ⟨16470876906970407447626627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10980584604646938298417751 16470876906970407447626627)
  ·
    refine ⟨24706315360455611171439941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16470876906970407447626627 24706315360455611171439941)
    ·
      refine ⟨4632434130085427094644989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24706315360455611171439941 4632434130085427094644989)
      ·
        refine ⟨1737162798782035160491871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4632434130085427094644989 1737162798782035160491871)
        ·
          refine ⟨2605744198173052740737807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737162798782035160491871 2605744198173052740737807)
          ·
            refine ⟨3908616297259579111106711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605744198173052740737807 3908616297259579111106711)
            ·
              refine ⟨5862924445889368666660067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908616297259579111106711 5862924445889368666660067)
              ·
                refine ⟨8794386668834052999990101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862924445889368666660067 8794386668834052999990101)
                ·
                  refine ⟨51529609387699529296817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8794386668834052999990101 51529609387699529296817)
                  ·
                    rfl

theorem cell22_451591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 9].length) (baseStart_451591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451591 prefixEnd_451591 := by exact prefixLift 451591
  have htrace : WordTrace (prefixWord ++ tailWord_451591) baseStart_451591 baseEnd_451591 := by
    simpa [prefixWord, tailWord_451591, baseEnd_451591] using wordTrace_append hprefix tailTrace_451591
  have hstable : (prefixWord ++ tailWord_451591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451591).length < 2 ^ (prefixWord ++ tailWord_451591).sum := by decide
  have hdescent : baseEnd_451591 < baseStart_451591 := by decide
  rcases family_descends (prefixWord ++ tailWord_451591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451612 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_451612 : Nat := 118140960795 + 451612 * 2 ^ 59
def prefixEnd_451612 : Nat := 4983230072969 + 3 ^ 40 * 451612 * 2
def baseEnd_451612 : Nat := 154596016892261533115387

theorem tailTrace_451612 : CollatzResearch.WordTrace tailWord_451612 prefixEnd_451612 154596016892261533115387 := by
  unfold tailWord_451612
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235821419947164017070545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10981095226596218689427393 8235821419947164017070545)
  ·
    refine ⟨6176866064960373012802909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8235821419947164017070545 6176866064960373012802909)
    ·
      refine ⟨2316324774360139879801091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6176866064960373012802909 2316324774360139879801091)
      ·
        refine ⟨3474487161540209819701637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316324774360139879801091 3474487161540209819701637)
        ·
          refine ⟨651466342788789341194057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3474487161540209819701637 651466342788789341194057)
          ·
            refine ⟨488599757091592005895543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651466342788789341194057 488599757091592005895543)
            ·
              refine ⟨732899635637388008843315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488599757091592005895543 732899635637388008843315)
              ·
                refine ⟨1099349453456082013264973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732899635637388008843315 1099349453456082013264973)
                ·
                  refine ⟨412256045046030754974365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1099349453456082013264973 412256045046030754974365)
                  ·
                    refine ⟨154596016892261533115387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 412256045046030754974365 154596016892261533115387)
                    ·
                      rfl

theorem cell22_451612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_451612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451612 prefixEnd_451612 := by exact prefixLift 451612
  have htrace : WordTrace (prefixWord ++ tailWord_451612) baseStart_451612 baseEnd_451612 := by
    simpa [prefixWord, tailWord_451612, baseEnd_451612] using wordTrace_append hprefix tailTrace_451612
  have hstable : (prefixWord ++ tailWord_451612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451612).length < 2 ^ (prefixWord ++ tailWord_451612).sum := by decide
  have hdescent : baseEnd_451612 < baseStart_451612 := by decide
  rcases family_descends (prefixWord ++ tailWord_451612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451685 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_451685 : Nat := 118140960795 + 451685 * 2 ^ 59
def prefixEnd_451685 : Nat := 4983230072969 + 3 ^ 40 * 451685 * 2
def baseEnd_451685 : Nat := 154621006284113676040163

theorem tailTrace_451685 : CollatzResearch.WordTrace tailWord_451685 prefixEnd_451685 154621006284113676040163 := by
  unfold tailWord_451685
  simp only [CollatzResearch.WordTrace]
  refine ⟨16474305368629861501548509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10982870245753241001032339 16474305368629861501548509)
  ·
    refine ⟨6177864513236198063080691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16474305368629861501548509 6177864513236198063080691)
    ·
      refine ⟨9266796769854297094621037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6177864513236198063080691 9266796769854297094621037)
      ·
        refine ⟨3475048788695361410482889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9266796769854297094621037 3475048788695361410482889)
        ·
          refine ⟨2606286591521521057862167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3475048788695361410482889 2606286591521521057862167)
          ·
            refine ⟨3909429887282281586793251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606286591521521057862167 3909429887282281586793251)
            ·
              refine ⟨5864144830923422380189877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909429887282281586793251 5864144830923422380189877)
              ·
                refine ⟨549763577899070848142801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5864144830923422380189877 549763577899070848142801)
                ·
                  refine ⟨412322683424303136107101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549763577899070848142801 412322683424303136107101)
                  ·
                    refine ⟨154621006284113676040163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 412322683424303136107101 154621006284113676040163)
                    ·
                      rfl

theorem cell22_451685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_451685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451685 prefixEnd_451685 := by exact prefixLift 451685
  have htrace : WordTrace (prefixWord ++ tailWord_451685) baseStart_451685 baseEnd_451685 := by
    simpa [prefixWord, tailWord_451685, baseEnd_451685] using wordTrace_append hprefix tailTrace_451685
  have hstable : (prefixWord ++ tailWord_451685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451685).length < 2 ^ (prefixWord ++ tailWord_451685).sum := by decide
  have hdescent : baseEnd_451685 < baseStart_451685 := by decide
  rcases family_descends (prefixWord ++ tailWord_451685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451820 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_451820 : Nat := 118140960795 + 451820 * 2 ^ 59
def prefixEnd_451820 : Nat := 4983230072969 + 3 ^ 40 * 451820 * 2
def baseEnd_451820 : Nat := 154667219543018323914749

theorem tailTrace_451820 : CollatzResearch.WordTrace tailWord_451820 prefixEnd_451820 154667219543018323914749 := by
  unfold tailWord_451820
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239614611570389778856457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10986152815427186371808609 8239614611570389778856457)
  ·
    refine ⟨6179710958677792334142343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8239614611570389778856457 6179710958677792334142343)
    ·
      refine ⟨9269566438016688501213515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6179710958677792334142343 9269566438016688501213515)
      ·
        refine ⟨13904349657025032751820273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269566438016688501213515 13904349657025032751820273)
        ·
          refine ⟨10428262242768774563865205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13904349657025032751820273 10428262242768774563865205)
          ·
            refine ⟨977649585259572615362363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10428262242768774563865205 977649585259572615362363)
            ·
              refine ⟨1466474377889358923043545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977649585259572615362363 1466474377889358923043545)
              ·
                refine ⟨1099855783417019192282659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466474377889358923043545 1099855783417019192282659)
                ·
                  refine ⟨1649783675125528788423989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099855783417019192282659 1649783675125528788423989)
                  ·
                    refine ⟨154667219543018323914749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1649783675125528788423989 154667219543018323914749)
                    ·
                      rfl

theorem cell22_451820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_451820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451820 prefixEnd_451820 := by exact prefixLift 451820
  have htrace : WordTrace (prefixWord ++ tailWord_451820) baseStart_451820 baseEnd_451820 := by
    simpa [prefixWord, tailWord_451820, baseEnd_451820] using wordTrace_append hprefix tailTrace_451820
  have hstable : (prefixWord ++ tailWord_451820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451820).length < 2 ^ (prefixWord ++ tailWord_451820).sum := by decide
  have hdescent : baseEnd_451820 < baseStart_451820 := by decide
  rcases family_descends (prefixWord ++ tailWord_451820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451839 : List Nat := [1, 1, 2, 2, 1, 7, 2, 2, 4]
def baseStart_451839 : Nat := 118140960795 + 451839 * 2 ^ 59
def prefixEnd_451839 : Nat := 4983230072969 + 3 ^ 40 * 451839 * 2
def baseEnd_451839 : Nat := 51557907877102869229897

theorem tailTrace_451839 : CollatzResearch.WordTrace tailWord_451839 prefixEnd_451839 51557907877102869229897 := by
  unfold tailWord_451839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16479922210071945802654571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10986614806714630535103047 16479922210071945802654571)
  ·
    refine ⟨24719883315107918703981857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16479922210071945802654571 24719883315107918703981857)
    ·
      refine ⟨18539912486330939027986393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24719883315107918703981857 18539912486330939027986393)
      ·
        refine ⟨13904934364748204270989795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18539912486330939027986393 13904934364748204270989795)
        ·
          refine ⟨20857401547122306406484693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13904934364748204270989795 20857401547122306406484693)
          ·
            refine ⟨488845348760679056401985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20857401547122306406484693 488845348760679056401985)
            ·
              refine ⟨366634011570509292301489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488845348760679056401985 366634011570509292301489)
              ·
                refine ⟨274975508677881969226117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366634011570509292301489 274975508677881969226117)
                ·
                  refine ⟨51557907877102869229897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274975508677881969226117 51557907877102869229897)
                  ·
                    rfl

theorem cell22_451839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 4].length) (baseStart_451839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451839 prefixEnd_451839 := by exact prefixLift 451839
  have htrace : WordTrace (prefixWord ++ tailWord_451839) baseStart_451839 baseEnd_451839 := by
    simpa [prefixWord, tailWord_451839, baseEnd_451839] using wordTrace_append hprefix tailTrace_451839
  have hstable : (prefixWord ++ tailWord_451839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451839).length < 2 ^ (prefixWord ++ tailWord_451839).sum := by decide
  have hdescent : baseEnd_451839 < baseStart_451839 := by decide
  rcases family_descends (prefixWord ++ tailWord_451839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451869 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_451869 : Nat := 118140960795 + 451869 * 2 ^ 59
def prefixEnd_451869 : Nat := 4983230072969 + 3 ^ 40 * 451869 * 2
def baseEnd_451869 : Nat := 154683993244398529439599

theorem tailTrace_451869 : CollatzResearch.WordTrace tailWord_451869 prefixEnd_451869 154683993244398529439599 := by
  unfold tailWord_451869
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481016399963260926246661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10987344266642173950831107 16481016399963260926246661)
  ·
    refine ⟨3090190574993111423671249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16481016399963260926246661 3090190574993111423671249)
    ·
      refine ⟨2317642931244833567753437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3090190574993111423671249 2317642931244833567753437)
      ·
        refine ⟨869116099216812587907539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2317642931244833567753437 869116099216812587907539)
        ·
          refine ⟨1303674148825218881861309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869116099216812587907539 1303674148825218881861309)
          ·
            refine ⟨488877805809457080697991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1303674148825218881861309 488877805809457080697991)
            ·
              refine ⟨733316708714185621046987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488877805809457080697991 733316708714185621046987)
              ·
                refine ⟨1099975063071278431570481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733316708714185621046987 1099975063071278431570481)
                ·
                  refine ⟨824981297303458823677861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099975063071278431570481 824981297303458823677861)
                  ·
                    refine ⟨154683993244398529439599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824981297303458823677861 154683993244398529439599)
                    ·
                      rfl

theorem cell22_451869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_451869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451869 prefixEnd_451869 := by exact prefixLift 451869
  have htrace : WordTrace (prefixWord ++ tailWord_451869) baseStart_451869 baseEnd_451869 := by
    simpa [prefixWord, tailWord_451869, baseEnd_451869] using wordTrace_append hprefix tailTrace_451869
  have hstable : (prefixWord ++ tailWord_451869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451869).length < 2 ^ (prefixWord ++ tailWord_451869).sum := by decide
  have hdescent : baseEnd_451869 < baseStart_451869 := by decide
  rcases family_descends (prefixWord ++ tailWord_451869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451950 : List Nat := [4, 1, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_451950 : Nat := 118140960795 + 451950 * 2 ^ 59
def prefixEnd_451950 : Nat := 4983230072969 + 3 ^ 40 * 451950 * 2
def baseEnd_451950 : Nat := 154711721199741318164351

theorem tailTrace_451950 : CollatzResearch.WordTrace tailWord_451950 prefixEnd_451950 154711721199741318164351 := by
  unfold tailWord_451950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060496339083726469993163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10989313808446541173296869 2060496339083726469993163)
  ·
    refine ⟨3090744508625589704989745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060496339083726469993163 3090744508625589704989745)
    ·
      refine ⟨2318058381469192278742309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3090744508625589704989745 2318058381469192278742309)
      ·
        refine ⟨434635946525473552264183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2318058381469192278742309 434635946525473552264183)
        ·
          refine ⟨651953919788210328396275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434635946525473552264183 651953919788210328396275)
          ·
            refine ⟨977930879682315492594413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651953919788210328396275 977930879682315492594413)
            ·
              refine ⟨366724079880868309722905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 977930879682315492594413 366724079880868309722905)
              ·
                refine ⟨275043059910651232292179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366724079880868309722905 275043059910651232292179)
                ·
                  refine ⟨412564589865976848438269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275043059910651232292179 412564589865976848438269)
                  ·
                    refine ⟨154711721199741318164351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 412564589865976848438269 154711721199741318164351)
                    ·
                      rfl

theorem cell22_451950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_451950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_451950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_451950 prefixEnd_451950 := by exact prefixLift 451950
  have htrace : WordTrace (prefixWord ++ tailWord_451950) baseStart_451950 baseEnd_451950 := by
    simpa [prefixWord, tailWord_451950, baseEnd_451950] using wordTrace_append hprefix tailTrace_451950
  have hstable : (prefixWord ++ tailWord_451950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451950).length < 2 ^ (prefixWord ++ tailWord_451950).sum := by decide
  have hdescent : baseEnd_451950 < baseStart_451950 := by decide
  rcases family_descends (prefixWord ++ tailWord_451950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452092 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 6]
def baseStart_452092 : Nat := 118140960795 + 452092 * 2 ^ 59
def prefixEnd_452092 : Nat := 4983230072969 + 3 ^ 40 * 452092 * 2
def baseEnd_452092 : Nat := 51586776900566760371305

theorem tailTrace_452092 : CollatzResearch.WordTrace tailWord_452092 prefixEnd_452092 51586776900566760371305 := by
  unfold tailWord_452092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8244574939077685005807265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10992766585436913341076353 8244574939077685005807265)
  ·
    refine ⟨6183431204308263754355449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8244574939077685005807265 6183431204308263754355449)
    ·
      refine ⟨4637573403231197815766587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6183431204308263754355449 4637573403231197815766587)
      ·
        refine ⟨6956360104846796723649881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637573403231197815766587 6956360104846796723649881)
        ·
          refine ⟨5217270078635097542737411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6956360104846796723649881 5217270078635097542737411)
          ·
            refine ⟨7825905117952646314106117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217270078635097542737411 7825905117952646314106117)
            ·
              refine ⟨1467357209616121183894897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7825905117952646314106117 1467357209616121183894897)
              ·
                refine ⟨1100517907212090887921173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467357209616121183894897 1100517907212090887921173)
                ·
                  refine ⟨51586776900566760371305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1100517907212090887921173 51586776900566760371305)
                  ·
                    rfl

theorem cell22_452092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_452092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452092 prefixEnd_452092 := by exact prefixLift 452092
  have htrace : WordTrace (prefixWord ++ tailWord_452092) baseStart_452092 baseEnd_452092 := by
    simpa [prefixWord, tailWord_452092, baseEnd_452092] using wordTrace_append hprefix tailTrace_452092
  have hstable : (prefixWord ++ tailWord_452092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452092).length < 2 ^ (prefixWord ++ tailWord_452092).sum := by decide
  have hdescent : baseEnd_452092 < baseStart_452092 := by decide
  rcases family_descends (prefixWord ++ tailWord_452092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452124 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_452124 : Nat := 118140960795 + 452124 * 2 ^ 59
def prefixEnd_452124 : Nat := 4983230072969 + 3 ^ 40 * 452124 * 2
def baseEnd_452124 : Nat := 154771284955662864313817

theorem tailTrace_452124 : CollatzResearch.WordTrace tailWord_452124 prefixEnd_452124 154771284955662864313817 := by
  unfold tailWord_452124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245158507019719738389713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10993544676026292984519617 8245158507019719738389713)
  ·
    refine ⟨6183868880264789803792285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8245158507019719738389713 6183868880264789803792285)
    ·
      refine ⟨2318950830099296176422107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6183868880264789803792285 2318950830099296176422107)
      ·
        refine ⟨3478426245148944264633161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318950830099296176422107 3478426245148944264633161)
        ·
          refine ⟨2608819683861708198474871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478426245148944264633161 2608819683861708198474871)
          ·
            refine ⟨3913229525792562297712307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608819683861708198474871 3913229525792562297712307)
            ·
              refine ⟨5869844288688843446568461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913229525792562297712307 5869844288688843446568461)
              ·
                refine ⟨2201191608258316292463173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5869844288688843446568461 2201191608258316292463173)
                ·
                  refine ⟨412723426548434304836845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2201191608258316292463173 412723426548434304836845)
                  ·
                    refine ⟨154771284955662864313817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 412723426548434304836845 154771284955662864313817)
                    ·
                      rfl

theorem cell22_452124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_452124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452124 prefixEnd_452124 := by exact prefixLift 452124
  have htrace : WordTrace (prefixWord ++ tailWord_452124) baseStart_452124 baseEnd_452124 := by
    simpa [prefixWord, tailWord_452124, baseEnd_452124] using wordTrace_append hprefix tailTrace_452124
  have hstable : (prefixWord ++ tailWord_452124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452124).length < 2 ^ (prefixWord ++ tailWord_452124).sum := by decide
  have hdescent : baseEnd_452124 < baseStart_452124 := by decide
  rcases family_descends (prefixWord ++ tailWord_452124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452156 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_452156 : Nat := 118140960795 + 452156 * 2 ^ 59
def prefixEnd_452156 : Nat := 4983230072969 + 3 ^ 40 * 452156 * 2
def baseEnd_452156 : Nat := 154782239209625447513719

theorem tailTrace_452156 : CollatzResearch.WordTrace tailWord_452156 prefixEnd_452156 154782239209625447513719 := by
  unfold tailWord_452156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245742074961754470972161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10994322766615672627962881 8245742074961754470972161)
  ·
    refine ⟨6184306556221315853229121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8245742074961754470972161 6184306556221315853229121)
    ·
      refine ⟨4638229917165986889921841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6184306556221315853229121 4638229917165986889921841)
      ·
        refine ⟨3478672437874490167441381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4638229917165986889921841 3478672437874490167441381)
        ·
          refine ⟨652251082101466906395259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3478672437874490167441381 652251082101466906395259)
          ·
            refine ⟨978376623152200359592889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652251082101466906395259 978376623152200359592889)
            ·
              refine ⟨733782467364150269694667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978376623152200359592889 733782467364150269694667)
              ·
                refine ⟨1100673701046225404542001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733782467364150269694667 1100673701046225404542001)
                ·
                  refine ⟨825505275784669053406501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100673701046225404542001 825505275784669053406501)
                  ·
                    refine ⟨154782239209625447513719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 825505275784669053406501 154782239209625447513719)
                    ·
                      rfl

theorem cell22_452156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_452156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452156 prefixEnd_452156 := by exact prefixLift 452156
  have htrace : WordTrace (prefixWord ++ tailWord_452156) baseStart_452156 baseEnd_452156 := by
    simpa [prefixWord, tailWord_452156, baseEnd_452156] using wordTrace_append hprefix tailTrace_452156
  have hstable : (prefixWord ++ tailWord_452156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452156).length < 2 ^ (prefixWord ++ tailWord_452156).sum := by decide
  have hdescent : baseEnd_452156 < baseStart_452156 := by decide
  rcases family_descends (prefixWord ++ tailWord_452156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452199 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 5]
def baseStart_452199 : Nat := 118140960795 + 452199 * 2 ^ 59
def prefixEnd_452199 : Nat := 4983230072969 + 3 ^ 40 * 452199 * 2
def baseEnd_452199 : Nat := 51598986329462556229529

theorem tailTrace_452199 : CollatzResearch.WordTrace tailWord_452199 prefixEnd_452199 51598986329462556229529 := by
  unfold tailWord_452199
  simp only [CollatzResearch.WordTrace]
  refine ⟨16493052488767727285759651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10995368325845151523839767 16493052488767727285759651)
  ·
    refine ⟨24739578733151590928639477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16493052488767727285759651 24739578733151590928639477)
    ·
      refine ⟨2319335506232961649559951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24739578733151590928639477 2319335506232961649559951)
      ·
        refine ⟨3479003259349442474339927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319335506232961649559951 3479003259349442474339927)
        ·
          refine ⟨5218504889024163711509891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479003259349442474339927 5218504889024163711509891)
          ·
            refine ⟨7827757333536245567264837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218504889024163711509891 7827757333536245567264837)
            ·
              refine ⟨1467704500038046043862157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7827757333536245567264837 1467704500038046043862157)
              ·
                refine ⟨550389187514267266448309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467704500038046043862157 550389187514267266448309)
                ·
                  refine ⟨51598986329462556229529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 550389187514267266448309 51598986329462556229529)
                  ·
                    rfl

theorem cell22_452199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 5].length) (baseStart_452199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452199 prefixEnd_452199 := by exact prefixLift 452199
  have htrace : WordTrace (prefixWord ++ tailWord_452199) baseStart_452199 baseEnd_452199 := by
    simpa [prefixWord, tailWord_452199, baseEnd_452199] using wordTrace_append hprefix tailTrace_452199
  have hstable : (prefixWord ++ tailWord_452199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452199).length < 2 ^ (prefixWord ++ tailWord_452199).sum := by decide
  have hdescent : baseEnd_452199 < baseStart_452199 := by decide
  rcases family_descends (prefixWord ++ tailWord_452199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452227 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 10]
def baseStart_452227 : Nat := 118140960795 + 452227 * 2 ^ 59
def prefixEnd_452227 : Nat := 4983230072969 + 3 ^ 40 * 452227 * 2
def baseEnd_452227 : Nat := 51602181320201642996167

theorem tailTrace_452227 : CollatzResearch.WordTrace tailWord_452227 prefixEnd_452227 51602181320201642996167 := by
  unfold tailWord_452227
  simp only [CollatzResearch.WordTrace]
  refine ⟨16494073732666288067778935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10996049155110858711852623 16494073732666288067778935)
  ·
    refine ⟨24741110598999432101668403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16494073732666288067778935 24741110598999432101668403)
    ·
      refine ⟨37111665898499148152502605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24741110598999432101668403 37111665898499148152502605)
      ·
        refine ⟨13916874711937180557188477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37111665898499148152502605 13916874711937180557188477)
        ·
          refine ⟨5218828016976442708945679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13916874711937180557188477 5218828016976442708945679)
          ·
            refine ⟨7828242025464664063418519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218828016976442708945679 7828242025464664063418519)
            ·
              refine ⟨11742363038196996095127779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828242025464664063418519 11742363038196996095127779)
              ·
                refine ⟨17613544557295494142691669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742363038196996095127779 17613544557295494142691669)
                ·
                  refine ⟨51602181320201642996167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 17613544557295494142691669 51602181320201642996167)
                  ·
                    rfl

theorem cell22_452227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_452227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452227 prefixEnd_452227 := by exact prefixLift 452227
  have htrace : WordTrace (prefixWord ++ tailWord_452227) baseStart_452227 baseEnd_452227 := by
    simpa [prefixWord, tailWord_452227, baseEnd_452227] using wordTrace_append hprefix tailTrace_452227
  have hstable : (prefixWord ++ tailWord_452227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452227).length < 2 ^ (prefixWord ++ tailWord_452227).sum := by decide
  have hdescent : baseEnd_452227 < baseStart_452227 := by decide
  rcases family_descends (prefixWord ++ tailWord_452227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452274 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_452274 : Nat := 118140960795 + 452274 * 2 ^ 59
def prefixEnd_452274 : Nat := 4983230072969 + 3 ^ 40 * 452274 * 2
def baseEnd_452274 : Nat := 154822633021112473063357

theorem tailTrace_452274 : CollatzResearch.WordTrace tailWord_452274 prefixEnd_452274 154822633021112473063357 := by
  unfold tailWord_452274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123946990874003773684969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10997191975664010063159917 4123946990874003773684969)
  ·
    refine ⟨3092960243155502830263727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4123946990874003773684969 3092960243155502830263727)
    ·
      refine ⟨4639440364733254245395591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092960243155502830263727 4639440364733254245395591)
      ·
        refine ⟨6959160547099881368093387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639440364733254245395591 6959160547099881368093387)
        ·
          refine ⟨10438740820649822052140081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959160547099881368093387 10438740820649822052140081)
          ·
            refine ⟨7829055615487366539105061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10438740820649822052140081 7829055615487366539105061)
            ·
              refine ⟨1467947927903881226082199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7829055615487366539105061 1467947927903881226082199)
              ·
                refine ⟨2201921891855821839123299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467947927903881226082199 2201921891855821839123299)
                ·
                  refine ⟨3302882837783732758684949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201921891855821839123299 3302882837783732758684949)
                  ·
                    refine ⟨154822633021112473063357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3302882837783732758684949 154822633021112473063357)
                    ·
                      rfl

theorem cell22_452274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_452274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452274 prefixEnd_452274 := by exact prefixLift 452274
  have htrace : WordTrace (prefixWord ++ tailWord_452274) baseStart_452274 baseEnd_452274 := by
    simpa [prefixWord, tailWord_452274, baseEnd_452274] using wordTrace_append hprefix tailTrace_452274
  have hstable : (prefixWord ++ tailWord_452274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452274).length < 2 ^ (prefixWord ++ tailWord_452274).sum := by decide
  have hdescent : baseEnd_452274 < baseStart_452274 := by decide
  rcases family_descends (prefixWord ++ tailWord_452274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452306 : List Nat := [3, 2, 2, 2, 2, 2, 2, 7]
def baseStart_452306 : Nat := 118140960795 + 452306 * 2 ^ 59
def prefixEnd_452306 : Nat := 4983230072969 + 3 ^ 40 * 452306 * 2
def baseEnd_452306 : Nat := 17203731919452784029251

theorem tailTrace_452306 : CollatzResearch.WordTrace tailWord_452306 prefixEnd_452306 17203731919452784029251 := by
  unfold tailWord_452306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124238774845021139976193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10997970066253389706603181 4124238774845021139976193)
  ·
    refine ⟨3093179081133765854982145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4124238774845021139976193 3093179081133765854982145)
    ·
      refine ⟨2319884310850324391236609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3093179081133765854982145 2319884310850324391236609)
      ·
        refine ⟨1739913233137743293427457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2319884310850324391236609 1739913233137743293427457)
        ·
          refine ⟨1304934924853307470070593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1739913233137743293427457 1304934924853307470070593)
          ·
            refine ⟨978701193639980602552945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304934924853307470070593 978701193639980602552945)
            ·
              refine ⟨734025895229985451914709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978701193639980602552945 734025895229985451914709)
              ·
                refine ⟨17203731919452784029251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 734025895229985451914709 17203731919452784029251)
                ·
                  rfl

theorem cell22_452306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_452306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452306 prefixEnd_452306 := by exact prefixLift 452306
  have htrace : WordTrace (prefixWord ++ tailWord_452306) baseStart_452306 baseEnd_452306 := by
    simpa [prefixWord, tailWord_452306, baseEnd_452306] using wordTrace_append hprefix tailTrace_452306
  have hstable : (prefixWord ++ tailWord_452306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452306).length < 2 ^ (prefixWord ++ tailWord_452306).sum := by decide
  have hdescent : baseEnd_452306 < baseStart_452306 := by decide
  rcases family_descends (prefixWord ++ tailWord_452306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452355 : List Nat := [1, 1, 1, 3, 2, 2, 6, 2, 1, 3]
def baseStart_452355 : Nat := 118140960795 + 452355 * 2 ^ 59
def prefixEnd_452355 : Nat := 4983230072969 + 3 ^ 40 * 452355 * 2
def baseEnd_452355 : Nat := 154850360976455261788109

theorem tailTrace_452355 : CollatzResearch.WordTrace tailWord_452355 prefixEnd_452355 154850360976455261788109 := by
  unfold tailWord_452355
  simp only [CollatzResearch.WordTrace]
  refine ⟨16498742276202565928438519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10999161517468377285625679 16498742276202565928438519)
  ·
    refine ⟨24748113414303848892657779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16498742276202565928438519 24748113414303848892657779)
    ·
      refine ⟨37122170121455773338986669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24748113414303848892657779 37122170121455773338986669)
      ·
        refine ⟨13920813795545915002120001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37122170121455773338986669 13920813795545915002120001)
        ·
          refine ⟨10440610346659436251590001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13920813795545915002120001 10440610346659436251590001)
          ·
            refine ⟨7830457759994577188692501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10440610346659436251590001 7830457759994577188692501)
            ·
              refine ⟨367052707499745805719961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7830457759994577188692501 367052707499745805719961)
              ·
                refine ⟨275289530624809354289971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367052707499745805719961 275289530624809354289971)
                ·
                  refine ⟨412934295937214031434957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275289530624809354289971 412934295937214031434957)
                  ·
                    refine ⟨154850360976455261788109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 412934295937214031434957 154850360976455261788109)
                    ·
                      rfl

theorem cell22_452355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 3].length) (baseStart_452355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452355 prefixEnd_452355 := by exact prefixLift 452355
  have htrace : WordTrace (prefixWord ++ tailWord_452355) baseStart_452355 baseEnd_452355 := by
    simpa [prefixWord, tailWord_452355, baseEnd_452355] using wordTrace_append hprefix tailTrace_452355
  have hstable : (prefixWord ++ tailWord_452355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452355).length < 2 ^ (prefixWord ++ tailWord_452355).sum := by decide
  have hdescent : baseEnd_452355 < baseStart_452355 := by decide
  rcases family_descends (prefixWord ++ tailWord_452355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452379 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 6]
def baseStart_452379 : Nat := 118140960795 + 452379 * 2 ^ 59
def prefixEnd_452379 : Nat := 4983230072969 + 3 ^ 40 * 452379 * 2
def baseEnd_452379 : Nat := 51619525555642399729345

theorem tailTrace_452379 : CollatzResearch.WordTrace tailWord_452379 prefixEnd_452379 51619525555642399729345 := by
  unfold tailWord_452379
  simp only [CollatzResearch.WordTrace]
  refine ⟨16499617628115618027312191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10999745085410412018208127 16499617628115618027312191)
  ·
    refine ⟨24749426442173427040968287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16499617628115618027312191 24749426442173427040968287)
    ·
      refine ⟨37124139663260140561452431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24749426442173427040968287 37124139663260140561452431)
      ·
        refine ⟨55686209494890210842178647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37124139663260140561452431 55686209494890210842178647)
        ·
          refine ⟨83529314242335316263267971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55686209494890210842178647 83529314242335316263267971)
          ·
            refine ⟨125293971363502974394901957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83529314242335316263267971 125293971363502974394901957)
            ·
              refine ⟨23492619630656807699044117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125293971363502974394901957 23492619630656807699044117)
              ·
                refine ⟨1101216545187037860892693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23492619630656807699044117 1101216545187037860892693)
                ·
                  refine ⟨51619525555642399729345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1101216545187037860892693 51619525555642399729345)
                  ·
                    rfl

theorem cell22_452379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 6].length) (baseStart_452379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452379 prefixEnd_452379 := by exact prefixLift 452379
  have htrace : WordTrace (prefixWord ++ tailWord_452379) baseStart_452379 baseEnd_452379 := by
    simpa [prefixWord, tailWord_452379, baseEnd_452379] using wordTrace_append hprefix tailTrace_452379
  have hstable : (prefixWord ++ tailWord_452379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452379).length < 2 ^ (prefixWord ++ tailWord_452379).sum := by decide
  have hdescent : baseEnd_452379 < baseStart_452379 := by decide
  rcases family_descends (prefixWord ++ tailWord_452379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452413 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 6]
def baseStart_452413 : Nat := 118140960795 + 452413 * 2 ^ 59
def prefixEnd_452413 : Nat := 4983230072969 + 3 ^ 40 * 452413 * 2
def baseEnd_452413 : Nat := 51623405187254147945977

theorem tailTrace_452413 : CollatzResearch.WordTrace tailWord_452413 prefixEnd_452413 51623405187254147945977 := by
  unfold tailWord_452413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500857709992441834049893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11000571806661627889366595 16500857709992441834049893)
  ·
    refine ⟨3093910820623582843884355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16500857709992441834049893 3093910820623582843884355)
    ·
      refine ⟨4640866230935374265826533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3093910820623582843884355 4640866230935374265826533)
      ·
        refine ⟨870162418300382674842475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4640866230935374265826533 870162418300382674842475)
        ·
          refine ⟨1305243627450574012263713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870162418300382674842475 1305243627450574012263713)
          ·
            refine ⟨978932720587930509197785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1305243627450574012263713 978932720587930509197785)
            ·
              refine ⟨734199540440947881898339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978932720587930509197785 734199540440947881898339)
              ·
                refine ⟨1101299310661421822847509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734199540440947881898339 1101299310661421822847509)
                ·
                  refine ⟨51623405187254147945977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1101299310661421822847509 51623405187254147945977)
                  ·
                    rfl

theorem cell22_452413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_452413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452413 prefixEnd_452413 := by exact prefixLift 452413
  have htrace : WordTrace (prefixWord ++ tailWord_452413) baseStart_452413 baseEnd_452413 := by
    simpa [prefixWord, tailWord_452413, baseEnd_452413] using wordTrace_append hprefix tailTrace_452413
  have hstable : (prefixWord ++ tailWord_452413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452413).length < 2 ^ (prefixWord ++ tailWord_452413).sum := by decide
  have hdescent : baseEnd_452413 < baseStart_452413 := by decide
  rcases family_descends (prefixWord ++ tailWord_452413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452531 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 6]
def baseStart_452531 : Nat := 118140960795 + 452531 * 2 ^ 59
def prefixEnd_452531 : Nat := 4983230072969 + 3 ^ 40 * 452531 * 2
def baseEnd_452531 : Nat := 51636869791083156462523

theorem tailTrace_452531 : CollatzResearch.WordTrace tailWord_452531 prefixEnd_452531 51636869791083156462523 := by
  unfold tailWord_452531
  simp only [CollatzResearch.WordTrace]
  refine ⟨16505161523564947986845447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11003441015709965324563631 16505161523564947986845447)
  ·
    refine ⟨24757742285347421980268171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16505161523564947986845447 24757742285347421980268171)
    ·
      refine ⟨37136613428021132970402257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24757742285347421980268171 37136613428021132970402257)
      ·
        refine ⟨27852460071015849727801693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37136613428021132970402257 27852460071015849727801693)
        ·
          refine ⟨10444672526630943647925635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27852460071015849727801693 10444672526630943647925635)
          ·
            refine ⟨15667008789946415471888453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444672526630943647925635 15667008789946415471888453)
            ·
              refine ⟨2937564148114952900979085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15667008789946415471888453 2937564148114952900979085)
              ·
                refine ⟨1101586555543107337867157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2937564148114952900979085 1101586555543107337867157)
                ·
                  refine ⟨51636869791083156462523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1101586555543107337867157 51636869791083156462523)
                  ·
                    rfl

theorem cell22_452531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 6].length) (baseStart_452531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452531 prefixEnd_452531 := by exact prefixLift 452531
  have htrace : WordTrace (prefixWord ++ tailWord_452531) baseStart_452531 baseEnd_452531 := by
    simpa [prefixWord, tailWord_452531, baseEnd_452531] using wordTrace_append hprefix tailTrace_452531
  have hstable : (prefixWord ++ tailWord_452531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452531).length < 2 ^ (prefixWord ++ tailWord_452531).sum := by decide
  have hdescent : baseEnd_452531 < baseStart_452531 := by decide
  rcases family_descends (prefixWord ++ tailWord_452531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452533 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_452533 : Nat := 118140960795 + 452533 * 2 ^ 59
def prefixEnd_452533 : Nat := 4983230072969 + 3 ^ 40 * 452533 * 2
def baseEnd_452533 : Nat := 154911294014122130837563

theorem tailTrace_452533 : CollatzResearch.WordTrace tailWord_452533 prefixEnd_452533 154911294014122130837563 := by
  unfold tailWord_452533
  simp only [CollatzResearch.WordTrace]
  refine ⟨16505234469557702328418253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11003489646371801552278835 16505234469557702328418253)
  ·
    refine ⟨6189462926084138373156845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16505234469557702328418253 6189462926084138373156845)
    ·
      refine ⟨2321048597281551889933817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6189462926084138373156845 2321048597281551889933817)
      ·
        refine ⟨1740786447961163917450363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2321048597281551889933817 1740786447961163917450363)
        ·
          refine ⟨2611179671941745876175545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740786447961163917450363 2611179671941745876175545)
          ·
            refine ⟨1958384753956309407131659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611179671941745876175545 1958384753956309407131659)
            ·
              refine ⟨2937577130934464110697489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958384753956309407131659 2937577130934464110697489)
              ·
                refine ⟨2203182848200848083023117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937577130934464110697489 2203182848200848083023117)
                ·
                  refine ⟨826193568075318031133669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2203182848200848083023117 826193568075318031133669)
                  ·
                    refine ⟨154911294014122130837563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 826193568075318031133669 154911294014122130837563)
                    ·
                      rfl

theorem cell22_452533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_452533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452533 prefixEnd_452533 := by exact prefixLift 452533
  have htrace : WordTrace (prefixWord ++ tailWord_452533) baseStart_452533 baseEnd_452533 := by
    simpa [prefixWord, tailWord_452533, baseEnd_452533] using wordTrace_append hprefix tailTrace_452533
  have hstable : (prefixWord ++ tailWord_452533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452533).length < 2 ^ (prefixWord ++ tailWord_452533).sum := by decide
  have hdescent : baseEnd_452533 < baseStart_452533 := by decide
  rcases family_descends (prefixWord ++ tailWord_452533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452565 : List Nat := [1, 3, 2, 3, 2, 1, 1, 5, 4]
def baseStart_452565 : Nat := 118140960795 + 452565 * 2 ^ 59
def prefixEnd_452565 : Nat := 4983230072969 + 3 ^ 40 * 452565 * 2
def baseEnd_452565 : Nat := 51640749422694904679155

theorem tailTrace_452565 : CollatzResearch.WordTrace tailWord_452565 prefixEnd_452565 51640749422694904679155 := by
  unfold tailWord_452565
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506401605441771793583149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11004267736961181195722099 16506401605441771793583149)
  ·
    refine ⟨6189900602040664422593681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16506401605441771793583149 6189900602040664422593681)
    ·
      refine ⟨4642425451530498316945261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6189900602040664422593681 4642425451530498316945261)
      ·
        refine ⟨1740909544323936868854473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4642425451530498316945261 1740909544323936868854473)
        ·
          refine ⟨1305682158242952651640855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1740909544323936868854473 1305682158242952651640855)
          ·
            refine ⟨1958523237364428977461283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305682158242952651640855 1958523237364428977461283)
            ·
              refine ⟨2937784856046643466191925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958523237364428977461283 2937784856046643466191925)
              ·
                refine ⟨275417330254372824955493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2937784856046643466191925 275417330254372824955493)
                ·
                  refine ⟨51640749422694904679155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275417330254372824955493 51640749422694904679155)
                  ·
                    rfl

theorem cell22_452565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_452565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452565 prefixEnd_452565 := by exact prefixLift 452565
  have htrace : WordTrace (prefixWord ++ tailWord_452565) baseStart_452565 baseEnd_452565 := by
    simpa [prefixWord, tailWord_452565, baseEnd_452565] using wordTrace_append hprefix tailTrace_452565
  have hstable : (prefixWord ++ tailWord_452565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452565).length < 2 ^ (prefixWord ++ tailWord_452565).sum := by decide
  have hdescent : baseEnd_452565 < baseStart_452565 := by decide
  rcases family_descends (prefixWord ++ tailWord_452565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452608 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 5, 3]
def baseStart_452608 : Nat := 118140960795 + 452608 * 2 ^ 59
def prefixEnd_452608 : Nat := 4983230072969 + 3 ^ 40 * 452608 * 2
def baseEnd_452608 : Nat := 154936968046846935212333

theorem tailTrace_452608 : CollatzResearch.WordTrace tailWord_452608 prefixEnd_452608 154936968046846935212333 := by
  unfold tailWord_452608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253984972142995068699239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11005313296190660091598985 8253984972142995068699239)
  ·
    refine ⟨12380977458214492603048859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8253984972142995068699239 12380977458214492603048859)
    ·
      refine ⟨18571466187321738904573289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12380977458214492603048859 18571466187321738904573289)
      ·
        refine ⟨13928599640491304178429967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18571466187321738904573289 13928599640491304178429967)
        ·
          refine ⟨20892899460736956267644951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13928599640491304178429967 20892899460736956267644951)
          ·
            refine ⟨31339349191105434401467427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20892899460736956267644951 31339349191105434401467427)
            ·
              refine ⟨47009023786658151602201141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31339349191105434401467427 47009023786658151602201141)
              ·
                refine ⟨4407095979999201712706357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47009023786658151602201141 4407095979999201712706357)
                ·
                  refine ⟨413165248124925160566221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4407095979999201712706357 413165248124925160566221)
                  ·
                    refine ⟨154936968046846935212333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413165248124925160566221 154936968046846935212333)
                    ·
                      rfl

theorem cell22_452608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_452608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452608 prefixEnd_452608 := by exact prefixLift 452608
  have htrace : WordTrace (prefixWord ++ tailWord_452608) baseStart_452608 baseEnd_452608 := by
    simpa [prefixWord, tailWord_452608, baseEnd_452608] using wordTrace_append hprefix tailTrace_452608
  have hstable : (prefixWord ++ tailWord_452608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452608).length < 2 ^ (prefixWord ++ tailWord_452608).sum := by decide
  have hdescent : baseEnd_452608 < baseStart_452608 := by decide
  rcases family_descends (prefixWord ++ tailWord_452608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452648 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 2, 3]
def baseStart_452648 : Nat := 118140960795 + 452648 * 2 ^ 59
def prefixEnd_452648 : Nat := 4983230072969 + 3 ^ 40 * 452648 * 2
def baseEnd_452648 : Nat := 154950660864300164212211

theorem tailTrace_452648 : CollatzResearch.WordTrace tailWord_452648 prefixEnd_452648 154950660864300164212211 := by
  unfold tailWord_452648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254714432070538484427299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11006285909427384645903065 8254714432070538484427299)
  ·
    refine ⟨12382071648105807726640949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8254714432070538484427299 12382071648105807726640949)
    ·
      refine ⟨1160819217009919474372589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12382071648105807726640949 1160819217009919474372589)
      ·
        refine ⟨435307206378719802889721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1160819217009919474372589 435307206378719802889721)
        ·
          refine ⟨326480404784039852167291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435307206378719802889721 326480404784039852167291)
          ·
            refine ⟨489720607176059778250937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326480404784039852167291 489720607176059778250937)
            ·
              refine ⟨367290455382044833688203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489720607176059778250937 367290455382044833688203)
              ·
                refine ⟨550935683073067250532305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367290455382044833688203 550935683073067250532305)
                ·
                  refine ⟨413201762304800437899229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550935683073067250532305 413201762304800437899229)
                  ·
                    refine ⟨154950660864300164212211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413201762304800437899229 154950660864300164212211)
                    ·
                      rfl

theorem cell22_452648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_452648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452648 prefixEnd_452648 := by exact prefixLift 452648
  have htrace : WordTrace (prefixWord ++ tailWord_452648) baseStart_452648 baseEnd_452648 := by
    simpa [prefixWord, tailWord_452648, baseEnd_452648] using wordTrace_append hprefix tailTrace_452648
  have hstable : (prefixWord ++ tailWord_452648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452648).length < 2 ^ (prefixWord ++ tailWord_452648).sum := by decide
  have hdescent : baseEnd_452648 < baseStart_452648 := by decide
  rcases family_descends (prefixWord ++ tailWord_452648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452698 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_452698 : Nat := 118140960795 + 452698 * 2 ^ 59
def prefixEnd_452698 : Nat := 4983230072969 + 3 ^ 40 * 452698 * 2
def baseEnd_452698 : Nat := 154967776886116700462057

theorem tailTrace_452698 : CollatzResearch.WordTrace tailWord_452698 prefixEnd_452698 154967776886116700462057 := by
  unfold tailWord_452698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127813128489983877043687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11007501675973290338783165 4127813128489983877043687)
  ·
    refine ⟨6191719692734975815565531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4127813128489983877043687 6191719692734975815565531)
    ·
      refine ⟨9287579539102463723348297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6191719692734975815565531 9287579539102463723348297)
      ·
        refine ⟨6965684654326847792511223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9287579539102463723348297 6965684654326847792511223)
        ·
          refine ⟨10448526981490271688766835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965684654326847792511223 10448526981490271688766835)
          ·
            refine ⟨15672790472235407533150253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448526981490271688766835 15672790472235407533150253)
            ·
              refine ⟨5877296427088277824931345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15672790472235407533150253 5877296427088277824931345)
              ·
                refine ⟨4407972320316208368698509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5877296427088277824931345 4407972320316208368698509)
                ·
                  refine ⟨1652989620118578138261941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4407972320316208368698509 1652989620118578138261941)
                  ·
                    refine ⟨154967776886116700462057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1652989620118578138261941 154967776886116700462057)
                    ·
                      rfl

theorem cell22_452698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_452698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452698 prefixEnd_452698 := by exact prefixLift 452698
  have htrace : WordTrace (prefixWord ++ tailWord_452698) baseStart_452698 baseEnd_452698 := by
    simpa [prefixWord, tailWord_452698, baseEnd_452698] using wordTrace_append hprefix tailTrace_452698
  have hstable : (prefixWord ++ tailWord_452698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452698).length < 2 ^ (prefixWord ++ tailWord_452698).sum := by decide
  have hdescent : baseEnd_452698 < baseStart_452698 := by decide
  rcases family_descends (prefixWord ++ tailWord_452698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452713 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_452713 : Nat := 118140960795 + 452713 * 2 ^ 59
def prefixEnd_452713 : Nat := 4983230072969 + 3 ^ 40 * 452713 * 2
def baseEnd_452713 : Nat := 154972911692661661337011

theorem tailTrace_452713 : CollatzResearch.WordTrace tailWord_452713 prefixEnd_452713 154972911692661661337011 := by
  unfold tailWord_452713
  simp only [CollatzResearch.WordTrace]
  refine ⟨16511799608905593069970793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11007866405937062046647195 16511799608905593069970793)
  ·
    refine ⟨12383849706679194802478095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16511799608905593069970793 12383849706679194802478095)
    ·
      refine ⟨18575774560018792203717143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12383849706679194802478095 18575774560018792203717143)
      ·
        refine ⟨27863661840028188305575715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18575774560018792203717143 27863661840028188305575715)
        ·
          refine ⟨41795492760042282458363573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27863661840028188305575715 41795492760042282458363573)
          ·
            refine ⟨3918327446253963980471585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41795492760042282458363573 3918327446253963980471585)
            ·
              refine ⟨2938745584690472985353689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918327446253963980471585 2938745584690472985353689)
              ·
                refine ⟨2204059188517854739015267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938745584690472985353689 2204059188517854739015267)
                ·
                  refine ⟨3306088782776782108522901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204059188517854739015267 3306088782776782108522901)
                  ·
                    refine ⟨154972911692661661337011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3306088782776782108522901 154972911692661661337011)
                    ·
                      rfl

theorem cell22_452713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_452713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452713 prefixEnd_452713 := by exact prefixLift 452713
  have htrace : WordTrace (prefixWord ++ tailWord_452713) baseStart_452713 baseEnd_452713 := by
    simpa [prefixWord, tailWord_452713, baseEnd_452713] using wordTrace_append hprefix tailTrace_452713
  have hstable : (prefixWord ++ tailWord_452713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452713).length < 2 ^ (prefixWord ++ tailWord_452713).sum := by decide
  have hdescent : baseEnd_452713 < baseStart_452713 := by decide
  rcases family_descends (prefixWord ++ tailWord_452713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452766 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_452766 : Nat := 118140960795 + 452766 * 2 ^ 59
def prefixEnd_452766 : Nat := 4983230072969 + 3 ^ 40 * 452766 * 2
def baseEnd_452766 : Nat := 154991054675787189761849

theorem tailTrace_452766 : CollatzResearch.WordTrace tailWord_452766 prefixEnd_452766 154991054675787189761849 := by
  unfold tailWord_452766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064216584714197890206269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11009155118475722081100101 2064216584714197890206269)
  ·
    refine ⟨774081219267824208827351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2064216584714197890206269 774081219267824208827351)
    ·
      refine ⟨1161121828901736313241027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774081219267824208827351 1161121828901736313241027)
      ·
        refine ⟨1741682743352604469861541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161121828901736313241027 1741682743352604469861541)
        ·
          refine ⟨326565514378613338099039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1741682743352604469861541 326565514378613338099039)
          ·
            refine ⟨489848271567920007148559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326565514378613338099039 489848271567920007148559)
            ·
              refine ⟨734772407351880010722839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489848271567920007148559 734772407351880010722839)
              ·
                refine ⟨1102158611027820016084259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734772407351880010722839 1102158611027820016084259)
                ·
                  refine ⟨1653237916541730024126389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102158611027820016084259 1653237916541730024126389)
                  ·
                    refine ⟨154991054675787189761849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1653237916541730024126389 154991054675787189761849)
                    ·
                      rfl

theorem cell22_452766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_452766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452766 prefixEnd_452766 := by exact prefixLift 452766
  have htrace : WordTrace (prefixWord ++ tailWord_452766) baseStart_452766 baseEnd_452766 := by
    simpa [prefixWord, tailWord_452766, baseEnd_452766] using wordTrace_append hprefix tailTrace_452766
  have hstable : (prefixWord ++ tailWord_452766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452766).length < 2 ^ (prefixWord ++ tailWord_452766).sum := by decide
  have hdescent : baseEnd_452766 < baseStart_452766 := by decide
  rcases family_descends (prefixWord ++ tailWord_452766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452794 : List Nat := [3, 1, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_452794 : Nat := 118140960795 + 452794 * 2 ^ 59
def prefixEnd_452794 : Nat := 4983230072969 + 3 ^ 40 * 452794 * 2
def baseEnd_452794 : Nat := 155000639648004450061763

theorem tailTrace_452794 : CollatzResearch.WordTrace tailWord_452794 prefixEnd_452794 155000639648004450061763 := by
  unfold tailWord_452794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128688480403035975917359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11009835947741429269112957 4128688480403035975917359)
  ·
    refine ⟨6193032720604553963876039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128688480403035975917359 6193032720604553963876039)
    ·
      refine ⟨9289549080906830945814059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193032720604553963876039 9289549080906830945814059)
      ·
        refine ⟨13934323621360246418721089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289549080906830945814059 13934323621360246418721089)
        ·
          refine ⟨10450742716020184814040817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13934323621360246418721089 10450742716020184814040817)
          ·
            refine ⟨7838057037015138610530613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10450742716020184814040817 7838057037015138610530613)
            ·
              refine ⟨734817847220169244737245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7838057037015138610530613 734817847220169244737245)
              ·
                refine ⟨275556692707563466776467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 734817847220169244737245 275556692707563466776467)
                ·
                  refine ⟨413335039061345200164701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275556692707563466776467 413335039061345200164701)
                  ·
                    refine ⟨155000639648004450061763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413335039061345200164701 155000639648004450061763)
                    ·
                      rfl

theorem cell22_452794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_452794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452794 prefixEnd_452794 := by exact prefixLift 452794
  have htrace : WordTrace (prefixWord ++ tailWord_452794) baseStart_452794 baseEnd_452794 := by
    simpa [prefixWord, tailWord_452794, baseEnd_452794] using wordTrace_append hprefix tailTrace_452794
  have hstable : (prefixWord ++ tailWord_452794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452794).length < 2 ^ (prefixWord ++ tailWord_452794).sum := by decide
  have hdescent : baseEnd_452794 < baseStart_452794 := by decide
  rcases family_descends (prefixWord ++ tailWord_452794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452803 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 10]
def baseStart_452803 : Nat := 118140960795 + 452803 * 2 ^ 59
def prefixEnd_452803 : Nat := 4983230072969 + 3 ^ 40 * 452803 * 2
def baseEnd_452803 : Nat := 155003720531931426586735

theorem tailTrace_452803 : CollatzResearch.WordTrace tailWord_452803 prefixEnd_452803 155003720531931426586735 := by
  unfold tailWord_452803
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515082178579538440747063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11010054785719692293831375 16515082178579538440747063)
  ·
    refine ⟨24772623267869307661120595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16515082178579538440747063 24772623267869307661120595)
    ·
      refine ⟨37158934901803961491680893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24772623267869307661120595 37158934901803961491680893)
      ·
        refine ⟨13934600588176485559380335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37158934901803961491680893 13934600588176485559380335)
        ·
          refine ⟨20901900882264728339070503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934600588176485559380335 20901900882264728339070503)
          ·
            refine ⟨31352851323397092508605755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20901900882264728339070503 31352851323397092508605755)
            ·
              refine ⟨47029276985095638762908633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31352851323397092508605755 47029276985095638762908633)
              ·
                refine ⟨35271957738821729072181475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47029276985095638762908633 35271957738821729072181475)
                ·
                  refine ⟨52907936608232593608272213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35271957738821729072181475 52907936608232593608272213)
                  ·
                    refine ⟨155003720531931426586735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 52907936608232593608272213 155003720531931426586735)
                    ·
                      rfl

theorem cell22_452803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_452803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452803 prefixEnd_452803 := by exact prefixLift 452803
  have htrace : WordTrace (prefixWord ++ tailWord_452803) baseStart_452803 baseEnd_452803 := by
    simpa [prefixWord, tailWord_452803, baseEnd_452803] using wordTrace_append hprefix tailTrace_452803
  have hstable : (prefixWord ++ tailWord_452803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452803).length < 2 ^ (prefixWord ++ tailWord_452803).sum := by decide
  have hdescent : baseEnd_452803 < baseStart_452803 := by decide
  rcases family_descends (prefixWord ++ tailWord_452803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452824 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 5]
def baseStart_452824 : Nat := 118140960795 + 452824 * 2 ^ 59
def prefixEnd_452824 : Nat := 4983230072969 + 3 ^ 40 * 452824 * 2
def baseEnd_452824 : Nat := 51670303087031457270557

theorem tailTrace_452824 : CollatzResearch.WordTrace tailWord_452824 prefixEnd_452824 51670303087031457270557 := by
  unfold tailWord_452824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257924055751729513630763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11010565407668972684841017 8257924055751729513630763)
  ·
    refine ⟨12386886083627594270446145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8257924055751729513630763 12386886083627594270446145)
    ·
      refine ⟨9290164562720695702834609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12386886083627594270446145 9290164562720695702834609)
      ·
        refine ⟨6967623422040521777125957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9290164562720695702834609 6967623422040521777125957)
        ·
          refine ⟨1306429391632597833211117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6967623422040521777125957 1306429391632597833211117)
          ·
            refine ⟨489911021862224187454169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1306429391632597833211117 489911021862224187454169)
            ·
              refine ⟨367433266396668140590627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489911021862224187454169 367433266396668140590627)
              ·
                refine ⟨551149899595002210885941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367433266396668140590627 551149899595002210885941)
                ·
                  refine ⟨51670303087031457270557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 551149899595002210885941 51670303087031457270557)
                  ·
                    rfl

theorem cell22_452824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_452824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452824 prefixEnd_452824 := by exact prefixLift 452824
  have htrace : WordTrace (prefixWord ++ tailWord_452824) baseStart_452824 baseEnd_452824 := by
    simpa [prefixWord, tailWord_452824, baseEnd_452824] using wordTrace_append hprefix tailTrace_452824
  have hstable : (prefixWord ++ tailWord_452824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452824).length < 2 ^ (prefixWord ++ tailWord_452824).sum := by decide
  have hdescent : baseEnd_452824 < baseStart_452824 := by decide
  rcases family_descends (prefixWord ++ tailWord_452824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452837 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_452837 : Nat := 118140960795 + 452837 * 2 ^ 59
def prefixEnd_452837 : Nat := 4983230072969 + 3 ^ 40 * 452837 * 2
def baseEnd_452837 : Nat := 155015359426766671236631

theorem tailTrace_452837 : CollatzResearch.WordTrace tailWord_452837 prefixEnd_452837 155015359426766671236631 := by
  unfold tailWord_452837
  simp only [CollatzResearch.WordTrace]
  refine ⟨16516322260456362247484765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11010881506970908164989843 16516322260456362247484765)
  ·
    refine ⟨6193620847671135842806787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16516322260456362247484765 6193620847671135842806787)
    ·
      refine ⟨9290431271506703764210181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193620847671135842806787 9290431271506703764210181)
      ·
        refine ⟨1741955863407506955789409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9290431271506703764210181 1741955863407506955789409)
        ·
          refine ⟨1306466897555630216842057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741955863407506955789409 1306466897555630216842057)
          ·
            refine ⟨979850173166722662631543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306466897555630216842057 979850173166722662631543)
            ·
              refine ⟨1469775259750083993947315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979850173166722662631543 1469775259750083993947315)
              ·
                refine ⟨2204662889625125990920973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469775259750083993947315 2204662889625125990920973)
                ·
                  refine ⟨826748583609422246595365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2204662889625125990920973 826748583609422246595365)
                  ·
                    refine ⟨155015359426766671236631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 826748583609422246595365 155015359426766671236631)
                    ·
                      rfl

theorem cell22_452837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_452837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452837 prefixEnd_452837 := by exact prefixLift 452837
  have htrace : WordTrace (prefixWord ++ tailWord_452837) baseStart_452837 baseEnd_452837 := by
    simpa [prefixWord, tailWord_452837, baseEnd_452837] using wordTrace_append hprefix tailTrace_452837
  have hstable : (prefixWord ++ tailWord_452837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452837).length < 2 ^ (prefixWord ++ tailWord_452837).sum := by decide
  have hdescent : baseEnd_452837 < baseStart_452837 := by decide
  rcases family_descends (prefixWord ++ tailWord_452837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452987 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 6]
def baseStart_452987 : Nat := 118140960795 + 452987 * 2 ^ 59
def prefixEnd_452987 : Nat := 4983230072969 + 3 ^ 40 * 452987 * 2
def baseEnd_452987 : Nat := 51688902497405426662057

theorem tailTrace_452987 : CollatzResearch.WordTrace tailWord_452987 prefixEnd_452987 51688902497405426662057 := by
  unfold tailWord_452987
  simp only [CollatzResearch.WordTrace]
  refine ⟨16521793209912937865445215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11014528806608625243630143 16521793209912937865445215)
  ·
    refine ⟨24782689814869406798167823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16521793209912937865445215 24782689814869406798167823)
    ·
      refine ⟨37174034722304110197251735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24782689814869406798167823 37174034722304110197251735)
      ·
        refine ⟨55761052083456165295877603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37174034722304110197251735 55761052083456165295877603)
        ·
          refine ⟨83641578125184247943816405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55761052083456165295877603 83641578125184247943816405)
          ·
            refine ⟨1960349487309005811183197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83641578125184247943816405 1960349487309005811183197)
            ·
              refine ⟨735131057740877179193699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1960349487309005811183197 735131057740877179193699)
              ·
                refine ⟨1102696586611315768790549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735131057740877179193699 1102696586611315768790549)
                ·
                  refine ⟨51688902497405426662057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1102696586611315768790549 51688902497405426662057)
                  ·
                    rfl

theorem cell22_452987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 6].length) (baseStart_452987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_452987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_452987 prefixEnd_452987 := by exact prefixLift 452987
  have htrace : WordTrace (prefixWord ++ tailWord_452987) baseStart_452987 baseEnd_452987 := by
    simpa [prefixWord, tailWord_452987, baseEnd_452987] using wordTrace_append hprefix tailTrace_452987
  have hstable : (prefixWord ++ tailWord_452987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452987).length < 2 ^ (prefixWord ++ tailWord_452987).sum := by decide
  have hdescent : baseEnd_452987 < baseStart_452987 := by decide
  rcases family_descends (prefixWord ++ tailWord_452987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453006 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_453006 : Nat := 118140960795 + 453006 * 2 ^ 59
def prefixEnd_453006 : Nat := 4983230072969 + 3 ^ 40 * 453006 * 2
def baseEnd_453006 : Nat := 155073211580506563761113

theorem tailTrace_453006 : CollatzResearch.WordTrace tailWord_453006 prefixEnd_453006 155073211580506563761113 := by
  unfold tailWord_453006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065310774605513013798359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11014990797896069406924581 2065310774605513013798359)
  ·
    refine ⟨3097966161908269520697539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2065310774605513013798359 3097966161908269520697539)
    ·
      refine ⟨4646949242862404281046309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3097966161908269520697539 4646949242862404281046309)
      ·
        refine ⟨871302983036700802696183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4646949242862404281046309 871302983036700802696183)
        ·
          refine ⟨1306954474555051204044275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871302983036700802696183 1306954474555051204044275)
          ·
            refine ⟨1960431711832576806066413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306954474555051204044275 1960431711832576806066413)
            ·
              refine ⟨735161891937216302274905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1960431711832576806066413 735161891937216302274905)
              ·
                refine ⟨551371418952912226706179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735161891937216302274905 551371418952912226706179)
                ·
                  refine ⟨827057128429368340059269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551371418952912226706179 827057128429368340059269)
                  ·
                    refine ⟨155073211580506563761113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827057128429368340059269 155073211580506563761113)
                    ·
                      rfl

theorem cell22_453006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_453006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453006 prefixEnd_453006 := by exact prefixLift 453006
  have htrace : WordTrace (prefixWord ++ tailWord_453006) baseStart_453006 baseEnd_453006 := by
    simpa [prefixWord, tailWord_453006, baseEnd_453006] using wordTrace_append hprefix tailTrace_453006
  have hstable : (prefixWord ++ tailWord_453006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453006).length < 2 ^ (prefixWord ++ tailWord_453006).sum := by decide
  have hdescent : baseEnd_453006 < baseStart_453006 := by decide
  rcases family_descends (prefixWord ++ tailWord_453006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453049 : List Nat := [1, 2, 1, 4, 3, 3, 1, 7]
def baseStart_453049 : Nat := 118140960795 + 453049 * 2 ^ 59
def prefixEnd_453049 : Nat := 4983230072969 + 3 ^ 40 * 453049 * 2
def baseEnd_453049 : Nat := 17231992373252087215109

theorem tailTrace_453049 : CollatzResearch.WordTrace tailWord_453049 prefixEnd_453049 17231992373252087215109 := by
  unfold tailWord_453049
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524054535688322454202201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11016036357125548302801467 16524054535688322454202201)
  ·
    refine ⟨12393040901766241840651651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16524054535688322454202201 12393040901766241840651651)
    ·
      refine ⟨18589561352649362760977477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393040901766241840651651 18589561352649362760977477)
      ·
        refine ⟨3485542753621755517683277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18589561352649362760977477 3485542753621755517683277)
        ·
          refine ⟨1307078532608158319131229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3485542753621755517683277 1307078532608158319131229)
          ·
            refine ⟨490154449728059369674211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1307078532608158319131229 490154449728059369674211)
            ·
              refine ⟨735231674592089054511317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490154449728059369674211 735231674592089054511317)
              ·
                refine ⟨17231992373252087215109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 735231674592089054511317 17231992373252087215109)
                ·
                  rfl

theorem cell22_453049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 7].length) (baseStart_453049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453049 prefixEnd_453049 := by exact prefixLift 453049
  have htrace : WordTrace (prefixWord ++ tailWord_453049) baseStart_453049 baseEnd_453049 := by
    simpa [prefixWord, tailWord_453049, baseEnd_453049] using wordTrace_append hprefix tailTrace_453049
  have hstable : (prefixWord ++ tailWord_453049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453049).length < 2 ^ (prefixWord ++ tailWord_453049).sum := by decide
  have hdescent : baseEnd_453049 < baseStart_453049 := by decide
  rcases family_descends (prefixWord ++ tailWord_453049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453064 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 5, 3]
def baseStart_453064 : Nat := 118140960795 + 453064 * 2 ^ 59
def prefixEnd_453064 : Nat := 4983230072969 + 3 ^ 40 * 453064 * 2
def baseEnd_453064 : Nat := 155093066165813745810935

theorem tailTrace_453064 : CollatzResearch.WordTrace tailWord_453064 prefixEnd_453064 155093066165813745810935 := by
  unfold tailWord_453064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8262300815316990007999123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11016401087089320010665497 8262300815316990007999123)
  ·
    refine ⟨12393451222975485011998685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8262300815316990007999123 12393451222975485011998685)
    ·
      refine ⟨4647544208615806879499507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12393451222975485011998685 4647544208615806879499507)
      ·
        refine ⟨6971316312923710319249261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4647544208615806879499507 6971316312923710319249261)
        ·
          refine ⟨2614243617346391369718473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6971316312923710319249261 2614243617346391369718473)
          ·
            refine ⟨1960682713009793527288855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614243617346391369718473 1960682713009793527288855)
            ·
              refine ⟨2941024069514690290933283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960682713009793527288855 2941024069514690290933283)
              ·
                refine ⟨4411536104272035436399925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941024069514690290933283 4411536104272035436399925)
                ·
                  refine ⟨413581509775503322162493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4411536104272035436399925 413581509775503322162493)
                  ·
                    refine ⟨155093066165813745810935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413581509775503322162493 155093066165813745810935)
                    ·
                      rfl

theorem cell22_453064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_453064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453064 prefixEnd_453064 := by exact prefixLift 453064
  have htrace : WordTrace (prefixWord ++ tailWord_453064) baseStart_453064 baseEnd_453064 := by
    simpa [prefixWord, tailWord_453064, baseEnd_453064] using wordTrace_append hprefix tailTrace_453064
  have hstable : (prefixWord ++ tailWord_453064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453064).length < 2 ^ (prefixWord ++ tailWord_453064).sum := by decide
  have hdescent : baseEnd_453064 < baseStart_453064 := by decide
  rcases family_descends (prefixWord ++ tailWord_453064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453068 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_453068 : Nat := 118140960795 + 453068 * 2 ^ 59
def prefixEnd_453068 : Nat := 4983230072969 + 3 ^ 40 * 453068 * 2
def baseEnd_453068 : Nat := 155094435447559068710923

theorem tailTrace_453068 : CollatzResearch.WordTrace tailWord_453068 prefixEnd_453068 155094435447559068710923 := by
  unfold tailWord_453068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8262373761309744349571929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11016498348412992466095905 8262373761309744349571929)
  ·
    refine ⟨6196780320982308262178947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8262373761309744349571929 6196780320982308262178947)
    ·
      refine ⟨9295170481473462393268421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6196780320982308262178947 9295170481473462393268421)
      ·
        refine ⟨1742844465276274198737829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9295170481473462393268421 1742844465276274198737829)
        ·
          refine ⟨326783337239301412263343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1742844465276274198737829 326783337239301412263343)
          ·
            refine ⟨490175005858952118395015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326783337239301412263343 490175005858952118395015)
            ·
              refine ⟨735262508788428177592523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490175005858952118395015 735262508788428177592523)
              ·
                refine ⟨1102893763182642266388785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735262508788428177592523 1102893763182642266388785)
                ·
                  refine ⟨827170322386981699791589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1102893763182642266388785 827170322386981699791589)
                  ·
                    refine ⟨155094435447559068710923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827170322386981699791589 155094435447559068710923)
                    ·
                      rfl

theorem cell22_453068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_453068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453068 prefixEnd_453068 := by exact prefixLift 453068
  have htrace : WordTrace (prefixWord ++ tailWord_453068) baseStart_453068 baseEnd_453068 := by
    simpa [prefixWord, tailWord_453068, baseEnd_453068] using wordTrace_append hprefix tailTrace_453068
  have hstable : (prefixWord ++ tailWord_453068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453068).length < 2 ^ (prefixWord ++ tailWord_453068).sum := by decide
  have hdescent : baseEnd_453068 < baseStart_453068 := by decide
  rcases family_descends (prefixWord ++ tailWord_453068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453098 : List Nat := [3, 1, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_453098 : Nat := 118140960795 + 453098 * 2 ^ 59
def prefixEnd_453098 : Nat := 4983230072969 + 3 ^ 40 * 453098 * 2
def baseEnd_453098 : Nat := 155104705060648990460831

theorem tailTrace_453098 : CollatzResearch.WordTrace tailWord_453098 prefixEnd_453098 155104705060648990460831 := by
  unfold tailWord_453098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4131460428127700955683987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11017227808340535881823965 4131460428127700955683987)
  ·
    refine ⟨6197190642191551433525981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4131460428127700955683987 6197190642191551433525981)
    ·
      refine ⟨2323946490821831787572243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6197190642191551433525981 2323946490821831787572243)
      ·
        refine ⟨3485919736232747681358365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323946490821831787572243 3485919736232747681358365)
        ·
          refine ⟨1307219901087280380509387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3485919736232747681358365 1307219901087280380509387)
          ·
            refine ⟨1960829851630920570764081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307219901087280380509387 1960829851630920570764081)
            ·
              refine ⟨1470622388723190428073061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960829851630920570764081 1470622388723190428073061)
              ·
                refine ⟨275741697885598205263699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1470622388723190428073061 275741697885598205263699)
                ·
                  refine ⟨413612546828397307895549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275741697885598205263699 413612546828397307895549)
                  ·
                    refine ⟨155104705060648990460831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413612546828397307895549 155104705060648990460831)
                    ·
                      rfl

theorem cell22_453098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_453098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453098 prefixEnd_453098 := by exact prefixLift 453098
  have htrace : WordTrace (prefixWord ++ tailWord_453098) baseStart_453098 baseEnd_453098 := by
    simpa [prefixWord, tailWord_453098, baseEnd_453098] using wordTrace_append hprefix tailTrace_453098
  have hstable : (prefixWord ++ tailWord_453098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453098).length < 2 ^ (prefixWord ++ tailWord_453098).sum := by decide
  have hdescent : baseEnd_453098 < baseStart_453098 := by decide
  rcases family_descends (prefixWord ++ tailWord_453098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453171 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 2, 3]
def baseStart_453171 : Nat := 118140960795 + 453171 * 2 ^ 59
def prefixEnd_453171 : Nat := 4983230072969 + 3 ^ 40 * 453171 * 2
def baseEnd_453171 : Nat := 155129694452501133385607

theorem tailTrace_453171 : CollatzResearch.WordTrace tailWord_453171 prefixEnd_453171 155129694452501133385607 := by
  unfold tailWord_453171
  simp only [CollatzResearch.WordTrace]
  refine ⟨16528504241246337290143367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11019002827497558193428911 16528504241246337290143367)
  ·
    refine ⟨24792756361869505935215051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16528504241246337290143367 24792756361869505935215051)
    ·
      refine ⟨37189134542804258902822577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24792756361869505935215051 37189134542804258902822577)
      ·
        refine ⟨27891850907103194177116933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37189134542804258902822577 27891850907103194177116933)
        ·
          refine ⟨5229722045081848908209425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27891850907103194177116933 5229722045081848908209425)
          ·
            refine ⟨3922291533811386681157069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5229722045081848908209425 3922291533811386681157069)
            ·
              refine ⟨1470859325179270005433901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3922291533811386681157069 1470859325179270005433901)
              ·
                refine ⟨551572246942226252037713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470859325179270005433901 551572246942226252037713)
                ·
                  refine ⟨413679185206669689028285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551572246942226252037713 413679185206669689028285)
                  ·
                    refine ⟨155129694452501133385607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413679185206669689028285 155129694452501133385607)
                    ·
                      rfl

theorem cell22_453171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 3].length) (baseStart_453171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453171 prefixEnd_453171 := by exact prefixLift 453171
  have htrace : WordTrace (prefixWord ++ tailWord_453171) baseStart_453171 baseEnd_453171 := by
    simpa [prefixWord, tailWord_453171, baseEnd_453171] using wordTrace_append hprefix tailTrace_453171
  have hstable : (prefixWord ++ tailWord_453171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453171).length < 2 ^ (prefixWord ++ tailWord_453171).sum := by decide
  have hdescent : baseEnd_453171 < baseStart_453171 := by decide
  rcases family_descends (prefixWord ++ tailWord_453171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453259 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 5, 4]
def baseStart_453259 : Nat := 118140960795 + 453259 * 2 ^ 59
def prefixEnd_453259 : Nat := 4983230072969 + 3 ^ 40 * 453259 * 2
def baseEnd_453259 : Nat := 155159818650898237185337

theorem tailTrace_453259 : CollatzResearch.WordTrace tailWord_453259 prefixEnd_453259 155159818650898237185337 := by
  unfold tailWord_453259
  simp only [CollatzResearch.WordTrace]
  refine ⟨16531713864927528319346831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11021142576618352212897887 16531713864927528319346831)
  ·
    refine ⟨24797570797391292479020247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16531713864927528319346831 24797570797391292479020247)
    ·
      refine ⟨37196356196086938718530371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24797570797391292479020247 37196356196086938718530371)
      ·
        refine ⟨55794534294130408077795557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37196356196086938718530371 55794534294130408077795557)
        ·
          refine ⟨10461475180149451514586667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55794534294130408077795557 10461475180149451514586667)
          ·
            refine ⟨15692212770224177271880001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461475180149451514586667 15692212770224177271880001)
            ·
              refine ⟨11769159577668132953910001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15692212770224177271880001 11769159577668132953910001)
              ·
                refine ⟨8826869683251099715432501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11769159577668132953910001 8826869683251099715432501)
                ·
                  refine ⟨827519032804790598321797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8826869683251099715432501 827519032804790598321797)
                  ·
                    refine ⟨155159818650898237185337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827519032804790598321797 155159818650898237185337)
                    ·
                      rfl

theorem cell22_453259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_453259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453259 prefixEnd_453259 := by exact prefixLift 453259
  have htrace : WordTrace (prefixWord ++ tailWord_453259) baseStart_453259 baseEnd_453259 := by
    simpa [prefixWord, tailWord_453259, baseEnd_453259] using wordTrace_append hprefix tailTrace_453259
  have hstable : (prefixWord ++ tailWord_453259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453259).length < 2 ^ (prefixWord ++ tailWord_453259).sum := by decide
  have hdescent : baseEnd_453259 < baseStart_453259 := by decide
  rcases family_descends (prefixWord ++ tailWord_453259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453293 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_453293 : Nat := 118140960795 + 453293 * 2 ^ 59
def prefixEnd_453293 : Nat := 4983230072969 + 3 ^ 40 * 453293 * 2
def baseEnd_453293 : Nat := 155171457545733481835233

theorem tailTrace_453293 : CollatzResearch.WordTrace tailWord_453293 prefixEnd_453293 155171457545733481835233 := by
  unfold tailWord_453293
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532953946804352126084533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11021969297869568084056355 16532953946804352126084533)
  ·
    refine ⟨1549964432512908011820425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16532953946804352126084533 1549964432512908011820425)
    ·
      refine ⟨1162473324384681008865319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1549964432512908011820425 1162473324384681008865319)
      ·
        refine ⟨1743709986577021513297979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162473324384681008865319 1743709986577021513297979)
        ·
          refine ⟨2615564979865532269946969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743709986577021513297979 2615564979865532269946969)
          ·
            refine ⟨1961673734899149202460227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615564979865532269946969 1961673734899149202460227)
            ·
              refine ⟨2942510602348723803690341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961673734899149202460227 2942510602348723803690341)
              ·
                refine ⟨551720737940385713191939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2942510602348723803690341 551720737940385713191939)
                ·
                  refine ⟨827581106910578569787909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551720737940385713191939 827581106910578569787909)
                  ·
                    refine ⟨155171457545733481835233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 827581106910578569787909 155171457545733481835233)
                    ·
                      rfl

theorem cell22_453293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_453293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453293 prefixEnd_453293 := by exact prefixLift 453293
  have htrace : WordTrace (prefixWord ++ tailWord_453293) baseStart_453293 baseEnd_453293 := by
    simpa [prefixWord, tailWord_453293, baseEnd_453293] using wordTrace_append hprefix tailTrace_453293
  have hstable : (prefixWord ++ tailWord_453293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453293).length < 2 ^ (prefixWord ++ tailWord_453293).sum := by decide
  have hdescent : baseEnd_453293 < baseStart_453293 := by decide
  rcases family_descends (prefixWord ++ tailWord_453293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453306 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_453306 : Nat := 118140960795 + 453306 * 2 ^ 59
def prefixEnd_453306 : Nat := 4983230072969 + 3 ^ 40 * 453306 * 2
def baseEnd_453306 : Nat := 155175907711405781260193

theorem tailTrace_453306 : CollatzResearch.WordTrace tailWord_453306 prefixEnd_453306 155175907711405781260193 := by
  unfold tailWord_453306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133357023939313836576943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11022285397171503564205181 4133357023939313836576943)
  ·
    refine ⟨6200035535908970754865415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133357023939313836576943 6200035535908970754865415)
    ·
      refine ⟨9300053303863456132298123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6200035535908970754865415 9300053303863456132298123)
      ·
        refine ⟨13950079955795184198447185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300053303863456132298123 13950079955795184198447185)
        ·
          refine ⟨10462559966846388148835389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13950079955795184198447185 10462559966846388148835389)
          ·
            refine ⟨3923459987567395555813271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10462559966846388148835389 3923459987567395555813271)
            ·
              refine ⟨5885189981351093333719907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923459987567395555813271 5885189981351093333719907)
              ·
                refine ⟨8827784972026640000579861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5885189981351093333719907 8827784972026640000579861)
                ·
                  refine ⟨413802420563748750027181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8827784972026640000579861 413802420563748750027181)
                  ·
                    refine ⟨155175907711405781260193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413802420563748750027181 155175907711405781260193)
                    ·
                      rfl

theorem cell22_453306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_453306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453306 prefixEnd_453306 := by exact prefixLift 453306
  have htrace : WordTrace (prefixWord ++ tailWord_453306) baseStart_453306 baseEnd_453306 := by
    simpa [prefixWord, tailWord_453306, baseEnd_453306] using wordTrace_append hprefix tailTrace_453306
  have hstable : (prefixWord ++ tailWord_453306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453306).length < 2 ^ (prefixWord ++ tailWord_453306).sum := by decide
  have hdescent : baseEnd_453306 < baseStart_453306 := by decide
  rcases family_descends (prefixWord ++ tailWord_453306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453336 : List Nat := [2, 1, 2, 2, 3, 3, 2, 7]
def baseStart_453336 : Nat := 118140960795 + 453336 * 2 ^ 59
def prefixEnd_453336 : Nat := 4983230072969 + 3 ^ 40 * 453336 * 2
def baseEnd_453336 : Nat := 17242908591610633667789

theorem tailTrace_453336 : CollatzResearch.WordTrace tailWord_453336 prefixEnd_453336 17242908591610633667789 := by
  unfold tailWord_453336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8267261142824285234949931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11023014857099046979933241 8267261142824285234949931)
  ·
    refine ⟨12400891714236427852424897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8267261142824285234949931 12400891714236427852424897)
    ·
      refine ⟨9300668785677320889318673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12400891714236427852424897 9300668785677320889318673)
      ·
        refine ⟨6975501589257990666989005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9300668785677320889318673 6975501589257990666989005)
        ·
          refine ⟨2615813095971746500120877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6975501589257990666989005 2615813095971746500120877)
          ·
            refine ⟨980929910989404937545329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2615813095971746500120877 980929910989404937545329)
            ·
              refine ⟨735697433242053703158997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980929910989404937545329 735697433242053703158997)
              ·
                refine ⟨17242908591610633667789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 735697433242053703158997 17242908591610633667789)
                ·
                  rfl

theorem cell22_453336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_453336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453336 prefixEnd_453336 := by exact prefixLift 453336
  have htrace : WordTrace (prefixWord ++ tailWord_453336) baseStart_453336 baseEnd_453336 := by
    simpa [prefixWord, tailWord_453336, baseEnd_453336] using wordTrace_append hprefix tailTrace_453336
  have hstable : (prefixWord ++ tailWord_453336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453336).length < 2 ^ (prefixWord ++ tailWord_453336).sum := by decide
  have hdescent : baseEnd_453336 < baseStart_453336 := by decide
  rcases family_descends (prefixWord ++ tailWord_453336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453426 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_453426 : Nat := 118140960795 + 453426 * 2 ^ 59
def prefixEnd_453426 : Nat := 4983230072969 + 3 ^ 40 * 453426 * 2
def baseEnd_453426 : Nat := 51738995387921822753275

theorem tailTrace_453426 : CollatzResearch.WordTrace tailWord_453426 prefixEnd_453426 51738995387921822753275 := by
  unfold tailWord_453426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134451213830628960169033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11025203236881677227117421 4134451213830628960169033)
  ·
    refine ⟨3100838410372971720126775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4134451213830628960169033 3100838410372971720126775)
    ·
      refine ⟨4651257615559457580190163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100838410372971720126775 4651257615559457580190163)
      ·
        refine ⟨6976886423339186370285245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651257615559457580190163 6976886423339186370285245)
        ·
          refine ⟨2616332408752194888856967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6976886423339186370285245 2616332408752194888856967)
          ·
            refine ⟨3924498613128292333285451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616332408752194888856967 3924498613128292333285451)
            ·
              refine ⟨5886747919692438499928177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924498613128292333285451 5886747919692438499928177)
              ·
                refine ⟨4415060939769328874946133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886747919692438499928177 4415060939769328874946133)
                ·
                  refine ⟨51738995387921822753275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4415060939769328874946133 51738995387921822753275)
                  ·
                    rfl

theorem cell22_453426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_453426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453426 prefixEnd_453426 := by exact prefixLift 453426
  have htrace : WordTrace (prefixWord ++ tailWord_453426) baseStart_453426 baseEnd_453426 := by
    simpa [prefixWord, tailWord_453426, baseEnd_453426] using wordTrace_append hprefix tailTrace_453426
  have hstable : (prefixWord ++ tailWord_453426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453426).length < 2 ^ (prefixWord ++ tailWord_453426).sum := by decide
  have hdescent : baseEnd_453426 < baseStart_453426 := by decide
  rcases family_descends (prefixWord ++ tailWord_453426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453443 : List Nat := [1, 1, 1, 3, 1, 4, 1, 6, 4]
def baseStart_453443 : Nat := 118140960795 + 453443 * 2 ^ 59
def prefixEnd_453443 : Nat := 4983230072969 + 3 ^ 40 * 453443 * 2
def baseEnd_453443 : Nat := 51740935203727696861591

theorem tailTrace_453443 : CollatzResearch.WordTrace tailWord_453443 prefixEnd_453443 51740935203727696861591 := by
  unfold tailWord_453443
  simp only [CollatzResearch.WordTrace]
  refine ⟨16538424896260927744044983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11025616597507285162696655 16538424896260927744044983)
  ·
    refine ⟨24807637344391391616067475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16538424896260927744044983 24807637344391391616067475)
    ·
      refine ⟨37211456016587087424101213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24807637344391391616067475 37211456016587087424101213)
      ·
        refine ⟨13954296006220157784037955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37211456016587087424101213 13954296006220157784037955)
        ·
          refine ⟨20931444009330236676056933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954296006220157784037955 20931444009330236676056933)
          ·
            refine ⟨3924645751749419376760675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20931444009330236676056933 3924645751749419376760675)
            ·
              refine ⟨5886968627624129065141013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924645751749419376760675 5886968627624129065141013)
              ·
                refine ⟨275951654419881049928485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5886968627624129065141013 275951654419881049928485)
                ·
                  refine ⟨51740935203727696861591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275951654419881049928485 51740935203727696861591)
                  ·
                    rfl

theorem cell22_453443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 4].length) (baseStart_453443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453443 prefixEnd_453443 := by exact prefixLift 453443
  have htrace : WordTrace (prefixWord ++ tailWord_453443) baseStart_453443 baseEnd_453443 := by
    simpa [prefixWord, tailWord_453443, baseEnd_453443] using wordTrace_append hprefix tailTrace_453443
  have hstable : (prefixWord ++ tailWord_453443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453443).length < 2 ^ (prefixWord ++ tailWord_453443).sum := by decide
  have hdescent : baseEnd_453443 < baseStart_453443 := by decide
  rcases family_descends (prefixWord ++ tailWord_453443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453456 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_453456 : Nat := 118140960795 + 453456 * 2 ^ 59
def prefixEnd_453456 : Nat := 4983230072969 + 3 ^ 40 * 453456 * 2
def baseEnd_453456 : Nat := 155227255776855390009733

theorem tailTrace_453456 : CollatzResearch.WordTrace tailWord_453456 prefixEnd_453456 155227255776855390009733 := by
  unfold tailWord_453456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8269449522606915482134111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11025932696809220642845481 8269449522606915482134111)
  ·
    refine ⟨12404174283910373223201167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8269449522606915482134111 12404174283910373223201167)
    ·
      refine ⟨18606261425865559834801751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12404174283910373223201167 18606261425865559834801751)
      ·
        refine ⟨27909392138798339752202627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18606261425865559834801751 27909392138798339752202627)
        ·
          refine ⟨41864088208197509628303941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27909392138798339752202627 41864088208197509628303941)
          ·
            refine ⟨7849516539037033055306989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41864088208197509628303941 7849516539037033055306989)
            ·
              refine ⟨2943568702138887395740121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7849516539037033055306989 2943568702138887395740121)
              ·
                refine ⟨2207676526604165546805091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943568702138887395740121 2207676526604165546805091)
                ·
                  refine ⟨3311514789906248320207637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207676526604165546805091 3311514789906248320207637)
                  ·
                    refine ⟨155227255776855390009733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3311514789906248320207637 155227255776855390009733)
                    ·
                      rfl

theorem cell22_453456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_453456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453456 prefixEnd_453456 := by exact prefixLift 453456
  have htrace : WordTrace (prefixWord ++ tailWord_453456) baseStart_453456 baseEnd_453456 := by
    simpa [prefixWord, tailWord_453456, baseEnd_453456] using wordTrace_append hprefix tailTrace_453456
  have hstable : (prefixWord ++ tailWord_453456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453456).length < 2 ^ (prefixWord ++ tailWord_453456).sum := by decide
  have hdescent : baseEnd_453456 < baseStart_453456 := by decide
  rcases family_descends (prefixWord ++ tailWord_453456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453471 : List Nat := [1, 1, 2, 3, 1, 3, 3, 8]
def baseStart_453471 : Nat := 118140960795 + 453471 * 2 ^ 59
def prefixEnd_453471 : Nat := 4983230072969 + 3 ^ 40 * 453471 * 2
def baseEnd_453471 : Nat := 17248043398155594542743

theorem tailTrace_453471 : CollatzResearch.WordTrace tailWord_453471 prefixEnd_453471 17248043398155594542743 := by
  unfold tailWord_453471
  simp only [CollatzResearch.WordTrace]
  refine ⟨16539446140159488526064267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11026297426772992350709511 16539446140159488526064267)
  ·
    refine ⟨24809169210239232789096401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16539446140159488526064267 24809169210239232789096401)
    ·
      refine ⟨18606876907679424591822301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24809169210239232789096401 18606876907679424591822301)
      ·
        refine ⟨6977578840379784221933363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18606876907679424591822301 6977578840379784221933363)
        ·
          refine ⟨10466368260569676332900045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6977578840379784221933363 10466368260569676332900045)
          ·
            refine ⟨3924888097713628624837517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10466368260569676332900045 3924888097713628624837517)
            ·
              refine ⟨1471833036642610734314069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3924888097713628624837517 1471833036642610734314069)
              ·
                refine ⟨17248043398155594542743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1471833036642610734314069 17248043398155594542743)
                ·
                  rfl

theorem cell22_453471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 8].length) (baseStart_453471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453471 prefixEnd_453471 := by exact prefixLift 453471
  have htrace : WordTrace (prefixWord ++ tailWord_453471) baseStart_453471 baseEnd_453471 := by
    simpa [prefixWord, tailWord_453471, baseEnd_453471] using wordTrace_append hprefix tailTrace_453471
  have hstable : (prefixWord ++ tailWord_453471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453471).length < 2 ^ (prefixWord ++ tailWord_453471).sum := by decide
  have hdescent : baseEnd_453471 < baseStart_453471 := by decide
  rcases family_descends (prefixWord ++ tailWord_453471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453494 : List Nat := [5, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_453494 : Nat := 118140960795 + 453494 * 2 ^ 59
def prefixEnd_453494 : Nat := 4983230072969 + 3 ^ 40 * 453494 * 2
def baseEnd_453494 : Nat := 51746754651145319186539

theorem tailTrace_453494 : CollatzResearch.WordTrace tailWord_453494 prefixEnd_453494 51746754651145319186539 := by
  unfold tailWord_453494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033767813692260215884471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11026856679384108969434357 1033767813692260215884471)
  ·
    refine ⟨1550651720538390323826707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1033767813692260215884471 1550651720538390323826707)
    ·
      refine ⟨2325977580807585485740061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550651720538390323826707 2325977580807585485740061)
      ·
        refine ⟨872241592802844557152523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2325977580807585485740061 872241592802844557152523)
        ·
          refine ⟨1308362389204266835728785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872241592802844557152523 1308362389204266835728785)
          ·
            refine ⟨981271791903200126796589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308362389204266835728785 981271791903200126796589)
            ·
              refine ⟨367976921963700047548721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981271791903200126796589 367976921963700047548721)
              ·
                refine ⟨275982691472775035661541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367976921963700047548721 275982691472775035661541)
                ·
                  refine ⟨51746754651145319186539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275982691472775035661541 51746754651145319186539)
                  ·
                    rfl

theorem cell22_453494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_453494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453494 prefixEnd_453494 := by exact prefixLift 453494
  have htrace : WordTrace (prefixWord ++ tailWord_453494) baseStart_453494 baseEnd_453494 := by
    simpa [prefixWord, tailWord_453494, baseEnd_453494] using wordTrace_append hprefix tailTrace_453494
  have hstable : (prefixWord ++ tailWord_453494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453494).length < 2 ^ (prefixWord ++ tailWord_453494).sum := by decide
  have hdescent : baseEnd_453494 < baseStart_453494 := by decide
  rcases family_descends (prefixWord ++ tailWord_453494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453565 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_453565 : Nat := 118140960795 + 453565 * 2 ^ 59
def prefixEnd_453565 : Nat := 4983230072969 + 3 ^ 40 * 453565 * 2
def baseEnd_453565 : Nat := 155264568704415439034399

theorem tailTrace_453565 : CollatzResearch.WordTrace tailWord_453565 prefixEnd_453565 155264568704415439034399 := by
  unfold tailWord_453565
  simp only [CollatzResearch.WordTrace]
  refine ⟨16542874601818942579986149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11028583067879295053324099 16542874601818942579986149)
  ·
    refine ⟨3101788987841051733747403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16542874601818942579986149 3101788987841051733747403)
    ·
      refine ⟨4652683481761577600621105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101788987841051733747403 4652683481761577600621105)
      ·
        refine ⟨3489512611321183200465829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4652683481761577600621105 3489512611321183200465829)
        ·
          refine ⟨654283614622721850087343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3489512611321183200465829 654283614622721850087343)
          ·
            refine ⟨981425421934082775131015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654283614622721850087343 981425421934082775131015)
            ·
              refine ⟨1472138132901124162696523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981425421934082775131015 1472138132901124162696523)
              ·
                refine ⟨2208207199351686244044785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472138132901124162696523 2208207199351686244044785)
                ·
                  refine ⟨1656155399513764683033589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2208207199351686244044785 1656155399513764683033589)
                  ·
                    refine ⟨155264568704415439034399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1656155399513764683033589 155264568704415439034399)
                    ·
                      rfl

theorem cell22_453565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_453565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453565 prefixEnd_453565 := by exact prefixLift 453565
  have htrace : WordTrace (prefixWord ++ tailWord_453565) baseStart_453565 baseEnd_453565 := by
    simpa [prefixWord, tailWord_453565, baseEnd_453565] using wordTrace_append hprefix tailTrace_453565
  have hstable : (prefixWord ++ tailWord_453565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453565).length < 2 ^ (prefixWord ++ tailWord_453565).sum := by decide
  have hdescent : baseEnd_453565 < baseStart_453565 := by decide
  rcases family_descends (prefixWord ++ tailWord_453565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453580 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_453580 : Nat := 118140960795 + 453580 * 2 ^ 59
def prefixEnd_453580 : Nat := 4983230072969 + 3 ^ 40 * 453580 * 2
def baseEnd_453580 : Nat := 155269703510960399909353

theorem tailTrace_453580 : CollatzResearch.WordTrace tailWord_453580 prefixEnd_453580 155269703510960399909353 := by
  unfold tailWord_453580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8271710848382300070891097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11028947797843066761188129 8271710848382300070891097)
  ·
    refine ⟨6203783136286725053168323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8271710848382300070891097 6203783136286725053168323)
    ·
      refine ⟨9305674704430087579752485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6203783136286725053168323 9305674704430087579752485)
      ·
        refine ⟨1744814007080641421203591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9305674704430087579752485 1744814007080641421203591)
        ·
          refine ⟨2617221010620962131805387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744814007080641421203591 2617221010620962131805387)
          ·
            refine ⟨3925831515931443197708081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617221010620962131805387 3925831515931443197708081)
            ·
              refine ⟨2944373636948582398281061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925831515931443197708081 2944373636948582398281061)
              ·
                refine ⟨552070056927859199677699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2944373636948582398281061 552070056927859199677699)
                ·
                  refine ⟨828105085391788799516549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552070056927859199677699 828105085391788799516549)
                  ·
                    refine ⟨155269703510960399909353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 828105085391788799516549 155269703510960399909353)
                    ·
                      rfl

theorem cell22_453580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_453580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453580 prefixEnd_453580 := by exact prefixLift 453580
  have htrace : WordTrace (prefixWord ++ tailWord_453580) baseStart_453580 baseEnd_453580 := by
    simpa [prefixWord, tailWord_453580, baseEnd_453580] using wordTrace_append hprefix tailTrace_453580
  have hstable : (prefixWord ++ tailWord_453580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453580).length < 2 ^ (prefixWord ++ tailWord_453580).sum := by decide
  have hdescent : baseEnd_453580 < baseStart_453580 := by decide
  rcases family_descends (prefixWord ++ tailWord_453580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453597 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_453597 : Nat := 118140960795 + 453597 * 2 ^ 59
def prefixEnd_453597 : Nat := 4983230072969 + 3 ^ 40 * 453597 * 2
def baseEnd_453597 : Nat := 155275522958378022234301

theorem tailTrace_453597 : CollatzResearch.WordTrace tailWord_453597 prefixEnd_453597 155275522958378022234301 := by
  unfold tailWord_453597
  simp only [CollatzResearch.WordTrace]
  refine ⟨16544041737703012045151045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11029361158468674696767363 16544041737703012045151045)
  ·
    refine ⟨3102007825819314758465821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16544041737703012045151045 3102007825819314758465821)
    ·
      refine ⟨1163252934682243034424683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3102007825819314758465821 1163252934682243034424683)
      ·
        refine ⟨1744879402023364551637025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163252934682243034424683 1744879402023364551637025)
        ·
          refine ⟨1308659551517523413727769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744879402023364551637025 1308659551517523413727769)
          ·
            refine ⟨981494663638142560295827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308659551517523413727769 981494663638142560295827)
            ·
              refine ⟨1472241995457213840443741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981494663638142560295827 1472241995457213840443741)
              ·
                refine ⟨552090748296455190166403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472241995457213840443741 552090748296455190166403)
                ·
                  refine ⟨828136122444682785249605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552090748296455190166403 828136122444682785249605)
                  ·
                    refine ⟨155275522958378022234301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 828136122444682785249605 155275522958378022234301)
                    ·
                      rfl

theorem cell22_453597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_453597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453597 prefixEnd_453597 := by exact prefixLift 453597
  have htrace : WordTrace (prefixWord ++ tailWord_453597) baseStart_453597 baseEnd_453597 := by
    simpa [prefixWord, tailWord_453597, baseEnd_453597] using wordTrace_append hprefix tailTrace_453597
  have hstable : (prefixWord ++ tailWord_453597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453597).length < 2 ^ (prefixWord ++ tailWord_453597).sum := by decide
  have hdescent : baseEnd_453597 < baseStart_453597 := by decide
  rcases family_descends (prefixWord ++ tailWord_453597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453640 : List Nat := [2, 1, 3, 2, 1, 3, 4, 6]
def baseStart_453640 : Nat := 118140960795 + 453640 * 2 ^ 59
def prefixEnd_453640 : Nat := 4983230072969 + 3 ^ 40 * 453640 * 2
def baseEnd_453640 : Nat := 17254471415237804823241

theorem tailTrace_453640 : CollatzResearch.WordTrace tailWord_453640 prefixEnd_453640 17254471415237804823241 := by
  unfold tailWord_453640
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272805038273615194483187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11030406717698153592644249 8272805038273615194483187)
  ·
    refine ⟨12409207557410422791724781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8272805038273615194483187 12409207557410422791724781)
    ·
      refine ⟨4653452834028908546896793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12409207557410422791724781 4653452834028908546896793)
      ·
        refine ⟨3490089625521681410172595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653452834028908546896793 3490089625521681410172595)
        ·
          refine ⟨5235134438282522115258893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490089625521681410172595 5235134438282522115258893)
          ·
            refine ⟨1963175414355945793222085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5235134438282522115258893 1963175414355945793222085)
            ·
              refine ⟨368095390191739836229141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1963175414355945793222085 368095390191739836229141)
              ·
                refine ⟨17254471415237804823241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 368095390191739836229141 17254471415237804823241)
                ·
                  rfl

theorem cell22_453640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 6].length) (baseStart_453640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453640 prefixEnd_453640 := by exact prefixLift 453640
  have htrace : WordTrace (prefixWord ++ tailWord_453640) baseStart_453640 baseEnd_453640 := by
    simpa [prefixWord, tailWord_453640, baseEnd_453640] using wordTrace_append hprefix tailTrace_453640
  have hstable : (prefixWord ++ tailWord_453640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453640).length < 2 ^ (prefixWord ++ tailWord_453640).sum := by decide
  have hdescent : baseEnd_453640 < baseStart_453640 := by decide
  rcases family_descends (prefixWord ++ tailWord_453640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453683 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 1, 7]
def baseStart_453683 : Nat := 118140960795 + 453683 * 2 ^ 59
def prefixEnd_453683 : Nat := 4983230072969 + 3 ^ 40 * 453683 * 2
def baseEnd_453683 : Nat := 155304962515902464584037

theorem tailTrace_453683 : CollatzResearch.WordTrace tailWord_453683 prefixEnd_453683 155304962515902464584037 := by
  unfold tailWord_453683
  simp only [CollatzResearch.WordTrace]
  refine ⟨16547178415391448732781703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11031452276927632488521135 16547178415391448732781703)
  ·
    refine ⟨24820767623087173099172555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16547178415391448732781703 24820767623087173099172555)
    ·
      refine ⟨37231151434630759648758833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24820767623087173099172555 37231151434630759648758833)
      ·
        refine ⟨27923363575973069736569125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37231151434630759648758833 27923363575973069736569125)
        ·
          refine ⟨5235630670494950575606711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27923363575973069736569125 5235630670494950575606711)
          ·
            refine ⟨7853446005742425863410067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235630670494950575606711 7853446005742425863410067)
            ·
              refine ⟨11780169008613638795115101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7853446005742425863410067 11780169008613638795115101)
              ·
                refine ⟨4417563378230114548168163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11780169008613638795115101 4417563378230114548168163)
                ·
                  refine ⟨6626345067345171822252245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417563378230114548168163 6626345067345171822252245)
                  ·
                    refine ⟨155304962515902464584037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6626345067345171822252245 155304962515902464584037)
                    ·
                      rfl

theorem cell22_453683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_453683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453683 prefixEnd_453683 := by exact prefixLift 453683
  have htrace : WordTrace (prefixWord ++ tailWord_453683) baseStart_453683 baseEnd_453683 := by
    simpa [prefixWord, tailWord_453683, baseEnd_453683] using wordTrace_append hprefix tailTrace_453683
  have hstable : (prefixWord ++ tailWord_453683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453683).length < 2 ^ (prefixWord ++ tailWord_453683).sum := by decide
  have hdescent : baseEnd_453683 < baseStart_453683 := by decide
  rcases family_descends (prefixWord ++ tailWord_453683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453764 : List Nat := [2, 3, 2, 1, 2, 3, 2, 3, 4]
def baseStart_453764 : Nat := 118140960795 + 453764 * 2 ^ 59
def prefixEnd_453764 : Nat := 4983230072969 + 3 ^ 40 * 453764 * 2
def baseEnd_453764 : Nat := 51777563490415084436263

theorem tailTrace_453764 : CollatzResearch.WordTrace tailWord_453764 prefixEnd_453764 51777563490415084436263 := by
  unfold tailWord_453764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275066364048999783240173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11033421818731999710986897 8275066364048999783240173)
  ·
    refine ⟨3103149886518374918715065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8275066364048999783240173 3103149886518374918715065)
    ·
      refine ⟨2327362414888781189036299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3103149886518374918715065 2327362414888781189036299)
      ·
        refine ⟨3491043622333171783554449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327362414888781189036299 3491043622333171783554449)
        ·
          refine ⟨2618282716749878837665837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3491043622333171783554449 2618282716749878837665837)
          ·
            refine ⟨981856018781204564124689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2618282716749878837665837 981856018781204564124689)
            ·
              refine ⟨736392014085903423093517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981856018781204564124689 736392014085903423093517)
              ·
                refine ⟨276147005282213783660069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736392014085903423093517 276147005282213783660069)
                ·
                  refine ⟨51777563490415084436263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276147005282213783660069 51777563490415084436263)
                  ·
                    rfl

theorem cell22_453764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_453764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453764 prefixEnd_453764 := by exact prefixLift 453764
  have htrace : WordTrace (prefixWord ++ tailWord_453764) baseStart_453764 baseEnd_453764 := by
    simpa [prefixWord, tailWord_453764, baseEnd_453764] using wordTrace_append hprefix tailTrace_453764
  have hstable : (prefixWord ++ tailWord_453764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453764).length < 2 ^ (prefixWord ++ tailWord_453764).sum := by decide
  have hdescent : baseEnd_453764 < baseStart_453764 := by decide
  rcases family_descends (prefixWord ++ tailWord_453764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453796 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_453796 : Nat := 118140960795 + 453796 * 2 ^ 59
def prefixEnd_453796 : Nat := 4983230072969 + 3 ^ 40 * 453796 * 2
def baseEnd_453796 : Nat := 155343644725207836508691

theorem tailTrace_453796 : CollatzResearch.WordTrace tailWord_453796 prefixEnd_453796 155343644725207836508691 := by
  unfold tailWord_453796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275649931991034515822621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11034199909321379354430161 8275649931991034515822621)
  ·
    refine ⟨3103368724496637943433483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8275649931991034515822621 3103368724496637943433483)
    ·
      refine ⟨4655053086744956915150225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103368724496637943433483 4655053086744956915150225)
      ·
        refine ⟨3491289815058717686362669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4655053086744956915150225 3491289815058717686362669)
        ·
          refine ⟨1309233680647019132386001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3491289815058717686362669 1309233680647019132386001)
          ·
            refine ⟨981925260485264349289501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309233680647019132386001 981925260485264349289501)
            ·
              refine ⟨368221972681974130983563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981925260485264349289501 368221972681974130983563)
              ·
                refine ⟨552332959022961196475345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368221972681974130983563 552332959022961196475345)
                ·
                  refine ⟨414249719267220897356509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552332959022961196475345 414249719267220897356509)
                  ·
                    refine ⟨155343644725207836508691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 414249719267220897356509 155343644725207836508691)
                    ·
                      rfl

theorem cell22_453796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_453796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453796 prefixEnd_453796 := by exact prefixLift 453796
  have htrace : WordTrace (prefixWord ++ tailWord_453796) baseStart_453796 baseEnd_453796 := by
    simpa [prefixWord, tailWord_453796, baseEnd_453796] using wordTrace_append hprefix tailTrace_453796
  have hstable : (prefixWord ++ tailWord_453796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453796).length < 2 ^ (prefixWord ++ tailWord_453796).sum := by decide
  have hdescent : baseEnd_453796 < baseStart_453796 := by decide
  rcases family_descends (prefixWord ++ tailWord_453796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453807 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 3, 3]
def baseStart_453807 : Nat := 118140960795 + 453807 * 2 ^ 59
def prefixEnd_453807 : Nat := 4983230072969 + 3 ^ 40 * 453807 * 2
def baseEnd_453807 : Nat := 155347410250007474483657

theorem tailTrace_453807 : CollatzResearch.WordTrace tailWord_453807 prefixEnd_453807 155347410250007474483657 := by
  unfold tailWord_453807
  simp only [CollatzResearch.WordTrace]
  refine ⟨16551701066942217910295675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11034467377961478606863783 16551701066942217910295675)
  ·
    refine ⟨24827551600413326865443513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16551701066942217910295675 24827551600413326865443513)
    ·
      refine ⟨18620663700309995149082635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24827551600413326865443513 18620663700309995149082635)
      ·
        refine ⟨27930995550464992723623953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18620663700309995149082635 27930995550464992723623953)
        ·
          refine ⟨20948246662848744542717965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27930995550464992723623953 20948246662848744542717965)
          ·
            refine ⟨7855592498568279203519237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20948246662848744542717965 7855592498568279203519237)
            ·
              refine ⟨1472923593481552350659857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7855592498568279203519237 1472923593481552350659857)
              ·
                refine ⟨1104692695111164262994893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472923593481552350659857 1104692695111164262994893)
                ·
                  refine ⟨414259760666686598623085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104692695111164262994893 414259760666686598623085)
                  ·
                    refine ⟨155347410250007474483657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 414259760666686598623085 155347410250007474483657)
                    ·
                      rfl

theorem cell22_453807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_453807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453807 prefixEnd_453807 := by exact prefixLift 453807
  have htrace : WordTrace (prefixWord ++ tailWord_453807) baseStart_453807 baseEnd_453807 := by
    simpa [prefixWord, tailWord_453807, baseEnd_453807] using wordTrace_append hprefix tailTrace_453807
  have hstable : (prefixWord ++ tailWord_453807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453807).length < 2 ^ (prefixWord ++ tailWord_453807).sum := by decide
  have hdescent : baseEnd_453807 < baseStart_453807 := by decide
  rcases family_descends (prefixWord ++ tailWord_453807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453809 : List Nat := [1, 2, 2, 5, 1, 3, 2, 6]
def baseStart_453809 : Nat := 118140960795 + 453809 * 2 ^ 59
def prefixEnd_453809 : Nat := 4983230072969 + 3 ^ 40 * 453809 * 2
def baseEnd_453809 : Nat := 17260899432320015103739

theorem tailTrace_453809 : CollatzResearch.WordTrace tailWord_453809 prefixEnd_453809 17260899432320015103739 := by
  unfold tailWord_453809
  simp only [CollatzResearch.WordTrace]
  refine ⟨16551774012934972251868481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11034516008623314834578987 16551774012934972251868481)
  ·
    refine ⟨12413830509701229188901361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16551774012934972251868481 12413830509701229188901361)
    ·
      refine ⟨9310372882275921891676021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12413830509701229188901361 9310372882275921891676021)
      ·
        refine ⟨872847457713367677344627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9310372882275921891676021 872847457713367677344627)
        ·
          refine ⟨1309271186570051516016941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872847457713367677344627 1309271186570051516016941)
          ·
            refine ⟨490976694963769318506353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1309271186570051516016941 490976694963769318506353)
            ·
              refine ⟨368232521222826988879765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490976694963769318506353 368232521222826988879765)
              ·
                refine ⟨17260899432320015103739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 368232521222826988879765 17260899432320015103739)
                ·
                  rfl

theorem cell22_453809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 6].length) (baseStart_453809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453809 prefixEnd_453809 := by exact prefixLift 453809
  have htrace : WordTrace (prefixWord ++ tailWord_453809) baseStart_453809 baseEnd_453809 := by
    simpa [prefixWord, tailWord_453809, baseEnd_453809] using wordTrace_append hprefix tailTrace_453809
  have hstable : (prefixWord ++ tailWord_453809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453809).length < 2 ^ (prefixWord ++ tailWord_453809).sum := by decide
  have hdescent : baseEnd_453809 < baseStart_453809 := by decide
  rcases family_descends (prefixWord ++ tailWord_453809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453826 : List Nat := [3, 5, 1, 1, 2, 2, 8]
def baseStart_453826 : Nat := 118140960795 + 453826 * 2 ^ 59
def prefixEnd_453826 : Nat := 4983230072969 + 3 ^ 40 * 453826 * 2
def baseEnd_453826 : Nat := 5753848679196213268837

theorem tailTrace_453826 : CollatzResearch.WordTrace tailWord_453826 prefixEnd_453826 5753848679196213268837 := by
  unfold tailWord_453826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138098513468346038809333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11034929369248922770158221 4138098513468346038809333)
  ·
    refine ⟨387946735637657441138375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4138098513468346038809333 387946735637657441138375)
    ·
      refine ⟨581920103456486161707563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387946735637657441138375 581920103456486161707563)
      ·
        refine ⟨872880155184729242561345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581920103456486161707563 872880155184729242561345)
        ·
          refine ⟨654660116388546931921009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872880155184729242561345 654660116388546931921009)
          ·
            refine ⟨490995087291410198940757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654660116388546931921009 490995087291410198940757)
            ·
              refine ⟨5753848679196213268837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 490995087291410198940757 5753848679196213268837)
              ·
                rfl

theorem cell22_453826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 8].length) (baseStart_453826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453826 prefixEnd_453826 := by exact prefixLift 453826
  have htrace : WordTrace (prefixWord ++ tailWord_453826) baseStart_453826 baseEnd_453826 := by
    simpa [prefixWord, tailWord_453826, baseEnd_453826] using wordTrace_append hprefix tailTrace_453826
  have hstable : (prefixWord ++ tailWord_453826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453826).length < 2 ^ (prefixWord ++ tailWord_453826).sum := by decide
  have hdescent : baseEnd_453826 < baseStart_453826 := by decide
  rcases family_descends (prefixWord ++ tailWord_453826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453835 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 2, 5]
def baseStart_453835 : Nat := 118140960795 + 453835 * 2 ^ 59
def prefixEnd_453835 : Nat := 4983230072969 + 3 ^ 40 * 453835 * 2
def baseEnd_453835 : Nat := 155356995222224734783571

theorem tailTrace_453835 : CollatzResearch.WordTrace tailWord_453835 prefixEnd_453835 155356995222224734783571 := by
  unfold tailWord_453835
  simp only [CollatzResearch.WordTrace]
  refine ⟨16552722310840778692314959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11035148207227185794876639 16552722310840778692314959)
  ·
    refine ⟨24829083466261168038472439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16552722310840778692314959 24829083466261168038472439)
    ·
      refine ⟨37243625199391752057708659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24829083466261168038472439 37243625199391752057708659)
      ·
        refine ⟨55865437799087628086562989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37243625199391752057708659 55865437799087628086562989)
        ·
          refine ⟨20949539174657860532461121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55865437799087628086562989 20949539174657860532461121)
          ·
            refine ⟨15712154380993395399345841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20949539174657860532461121 15712154380993395399345841)
            ·
              refine ⟨11784115785745046549509381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15712154380993395399345841 11784115785745046549509381)
              ·
                refine ⟨2209521709827196228033009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11784115785745046549509381 2209521709827196228033009)
                ·
                  refine ⟨1657141282370397171024757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209521709827196228033009 1657141282370397171024757)
                  ·
                    refine ⟨155356995222224734783571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1657141282370397171024757 155356995222224734783571)
                    ·
                      rfl

theorem cell22_453835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_453835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453835 prefixEnd_453835 := by exact prefixLift 453835
  have htrace : WordTrace (prefixWord ++ tailWord_453835) baseStart_453835 baseEnd_453835 := by
    simpa [prefixWord, tailWord_453835, baseEnd_453835] using wordTrace_append hprefix tailTrace_453835
  have hstable : (prefixWord ++ tailWord_453835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453835).length < 2 ^ (prefixWord ++ tailWord_453835).sum := by decide
  have hdescent : baseEnd_453835 < baseStart_453835 := by decide
  rcases family_descends (prefixWord ++ tailWord_453835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453850 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_453850 : Nat := 118140960795 + 453850 * 2 ^ 59
def prefixEnd_453850 : Nat := 4983230072969 + 3 ^ 40 * 453850 * 2
def baseEnd_453850 : Nat := 155362130028769695658525

theorem tailTrace_453850 : CollatzResearch.WordTrace tailWord_453850 prefixEnd_453850 155362130028769695658525 := by
  unfold tailWord_453850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138317351446609063527751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11035512937190957502740669 4138317351446609063527751)
  ·
    refine ⟨6207476027169913595291627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4138317351446609063527751 6207476027169913595291627)
    ·
      refine ⟨9311214040754870392937441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207476027169913595291627 9311214040754870392937441)
      ·
        refine ⟨6983410530566152794703081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9311214040754870392937441 6983410530566152794703081)
        ·
          refine ⟨5237557897924614596027311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6983410530566152794703081 5237557897924614596027311)
          ·
            refine ⟨7856336846886921894040967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237557897924614596027311 7856336846886921894040967)
            ·
              refine ⟨11784505270330382841061451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856336846886921894040967 11784505270330382841061451)
              ·
                refine ⟨17676757905495574261592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11784505270330382841061451 17676757905495574261592177)
                ·
                  refine ⟨13257568429121680696194133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17676757905495574261592177 13257568429121680696194133)
                  ·
                    refine ⟨155362130028769695658525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13257568429121680696194133 155362130028769695658525)
                    ·
                      rfl

theorem cell22_453850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_453850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453850 prefixEnd_453850 := by exact prefixLift 453850
  have htrace : WordTrace (prefixWord ++ tailWord_453850) baseStart_453850 baseEnd_453850 := by
    simpa [prefixWord, tailWord_453850, baseEnd_453850] using wordTrace_append hprefix tailTrace_453850
  have hstable : (prefixWord ++ tailWord_453850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453850).length < 2 ^ (prefixWord ++ tailWord_453850).sum := by decide
  have hdescent : baseEnd_453850 < baseStart_453850 := by decide
  rcases family_descends (prefixWord ++ tailWord_453850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453867 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 3, 4]
def baseStart_453867 : Nat := 118140960795 + 453867 * 2 ^ 59
def prefixEnd_453867 : Nat := 4983230072969 + 3 ^ 40 * 453867 * 2
def baseEnd_453867 : Nat := 155367949476187317983473

theorem tailTrace_453867 : CollatzResearch.WordTrace tailWord_453867 prefixEnd_453867 155367949476187317983473 := by
  unfold tailWord_453867
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553889446724848157479855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11035926297816565438319903 16553889446724848157479855)
  ·
    refine ⟨24830834170087272236219783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16553889446724848157479855 24830834170087272236219783)
    ·
      refine ⟨37246251255130908354329675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24830834170087272236219783 37246251255130908354329675)
      ·
        refine ⟨55869376882696362531494513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37246251255130908354329675 55869376882696362531494513)
        ·
          refine ⟨41902032662022271898620885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55869376882696362531494513 41902032662022271898620885)
          ·
            refine ⟨982078890516146997623927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 41902032662022271898620885 982078890516146997623927)
            ·
              refine ⟨1473118335774220496435891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982078890516146997623927 1473118335774220496435891)
              ·
                refine ⟨2209677503661330744653837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473118335774220496435891 2209677503661330744653837)
                ·
                  refine ⟨828629063872999029245189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2209677503661330744653837 828629063872999029245189)
                  ·
                    refine ⟨155367949476187317983473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 828629063872999029245189 155367949476187317983473)
                    ·
                      rfl

theorem cell22_453867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_453867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453867 prefixEnd_453867 := by exact prefixLift 453867
  have htrace : WordTrace (prefixWord ++ tailWord_453867) baseStart_453867 baseEnd_453867 := by
    simpa [prefixWord, tailWord_453867, baseEnd_453867] using wordTrace_append hprefix tailTrace_453867
  have hstable : (prefixWord ++ tailWord_453867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453867).length < 2 ^ (prefixWord ++ tailWord_453867).sum := by decide
  have hdescent : baseEnd_453867 < baseStart_453867 := by decide
  rcases family_descends (prefixWord ++ tailWord_453867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453899 : List Nat := [1, 1, 1, 1, 5, 4, 1, 4, 4]
def baseStart_453899 : Nat := 118140960795 + 453899 * 2 ^ 59
def prefixEnd_453899 : Nat := 4983230072969 + 3 ^ 40 * 453899 * 2
def baseEnd_453899 : Nat := 51792967910049967061125

theorem tailTrace_453899 : CollatzResearch.WordTrace tailWord_453899 prefixEnd_453899 51792967910049967061125 := by
  unfold tailWord_453899
  simp only [CollatzResearch.WordTrace]
  refine ⟨16555056582608917622644751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11036704388405945081763167 16555056582608917622644751)
  ·
    refine ⟨24832584873913376433967127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16555056582608917622644751 24832584873913376433967127)
    ·
      refine ⟨37248877310870064650950691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24832584873913376433967127 37248877310870064650950691)
      ·
        refine ⟨55873315966305096976426037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37248877310870064650950691 55873315966305096976426037)
        ·
          refine ⟨5238123371841102841539941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55873315966305096976426037 5238123371841102841539941)
          ·
            refine ⟨982148132220206782788739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5238123371841102841539941 982148132220206782788739)
            ·
              refine ⟨1473222198330310174183109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982148132220206782788739 1473222198330310174183109)
              ·
                refine ⟨276229162186933157659333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1473222198330310174183109 276229162186933157659333)
                ·
                  refine ⟨51792967910049967061125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276229162186933157659333 51792967910049967061125)
                  ·
                    rfl

theorem cell22_453899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 4].length) (baseStart_453899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453899 prefixEnd_453899 := by exact prefixLift 453899
  have htrace : WordTrace (prefixWord ++ tailWord_453899) baseStart_453899 baseEnd_453899 := by
    simpa [prefixWord, tailWord_453899, baseEnd_453899] using wordTrace_append hprefix tailTrace_453899
  have hstable : (prefixWord ++ tailWord_453899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453899).length < 2 ^ (prefixWord ++ tailWord_453899).sum := by decide
  have hdescent : baseEnd_453899 < baseStart_453899 := by decide
  rcases family_descends (prefixWord ++ tailWord_453899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453914 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_453914 : Nat := 118140960795 + 453914 * 2 ^ 59
def prefixEnd_453914 : Nat := 4983230072969 + 3 ^ 40 * 453914 * 2
def baseEnd_453914 : Nat := 155384038536694862058329

theorem tailTrace_453914 : CollatzResearch.WordTrace tailWord_453914 prefixEnd_453914 155384038536694862058329 := by
  unfold tailWord_453914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138900919388643796110199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11037069118369716789627197 4138900919388643796110199)
  ·
    refine ⟨6208351379082965694165299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4138900919388643796110199 6208351379082965694165299)
    ·
      refine ⟨9312527068624448541247949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6208351379082965694165299 9312527068624448541247949)
      ·
        refine ⟨3492197650734168202967981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9312527068624448541247949 3492197650734168202967981)
        ·
          refine ⟨1309574119025313076112993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3492197650734168202967981 1309574119025313076112993)
          ·
            refine ⟨982180589268984807084745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309574119025313076112993 982180589268984807084745)
            ·
              refine ⟨736635441951738605313559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982180589268984807084745 736635441951738605313559)
              ·
                refine ⟨1104953162927607907970339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736635441951738605313559 1104953162927607907970339)
                ·
                  refine ⟨1657429744391411861955509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104953162927607907970339 1657429744391411861955509)
                  ·
                    refine ⟨155384038536694862058329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1657429744391411861955509 155384038536694862058329)
                    ·
                      rfl

theorem cell22_453914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_453914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453914 prefixEnd_453914 := by exact prefixLift 453914
  have htrace : WordTrace (prefixWord ++ tailWord_453914) baseStart_453914 baseEnd_453914 := by
    simpa [prefixWord, tailWord_453914, baseEnd_453914] using wordTrace_append hprefix tailTrace_453914
  have hstable : (prefixWord ++ tailWord_453914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453914).length < 2 ^ (prefixWord ++ tailWord_453914).sum := by decide
  have hdescent : baseEnd_453914 < baseStart_453914 := by decide
  rcases family_descends (prefixWord ++ tailWord_453914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453933 : List Nat := [1, 5, 3, 1, 1, 2, 2, 3, 4]
def baseStart_453933 : Nat := 118140960795 + 453933 * 2 ^ 59
def prefixEnd_453933 : Nat := 4983230072969 + 3 ^ 40 * 453933 * 2
def baseEnd_453933 : Nat := 51796847541661715277757

theorem tailTrace_453933 : CollatzResearch.WordTrace tailWord_453933 prefixEnd_453933 51796847541661715277757 := by
  unfold tailWord_453933
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556296664485741429382453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11037531109657160952921635 16556296664485741429382453)
  ·
    refine ⟨1552152812295538259004605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16556296664485741429382453 1552152812295538259004605)
    ·
      refine ⟨582057304610826847126727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1552152812295538259004605 582057304610826847126727)
      ·
        refine ⟨873085956916240270690091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582057304610826847126727 873085956916240270690091)
        ·
          refine ⟨1309628935374360406035137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873085956916240270690091 1309628935374360406035137)
          ·
            refine ⟨982221701530770304526353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309628935374360406035137 982221701530770304526353)
            ·
              refine ⟨736666276148077728394765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982221701530770304526353 736666276148077728394765)
              ·
                refine ⟨276249853555529148148037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736666276148077728394765 276249853555529148148037)
                ·
                  refine ⟨51796847541661715277757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276249853555529148148037 51796847541661715277757)
                  ·
                    rfl

theorem cell22_453933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_453933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453933 prefixEnd_453933 := by exact prefixLift 453933
  have htrace : WordTrace (prefixWord ++ tailWord_453933) baseStart_453933 baseEnd_453933 := by
    simpa [prefixWord, tailWord_453933, baseEnd_453933] using wordTrace_append hprefix tailTrace_453933
  have hstable : (prefixWord ++ tailWord_453933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453933).length < 2 ^ (prefixWord ++ tailWord_453933).sum := by decide
  have hdescent : baseEnd_453933 < baseStart_453933 := by decide
  rcases family_descends (prefixWord ++ tailWord_453933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453959 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 3, 3]
def baseStart_453959 : Nat := 118140960795 + 453959 * 2 ^ 59
def prefixEnd_453959 : Nat := 4983230072969 + 3 ^ 40 * 453959 * 2
def baseEnd_453959 : Nat := 155399442956329744683191

theorem tailTrace_453959 : CollatzResearch.WordTrace tailWord_453959 prefixEnd_453959 155399442956329744683191 := by
  unfold tailWord_453959
  simp only [CollatzResearch.WordTrace]
  refine ⟨16557244962391547869828931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11038163308261031913219287 16557244962391547869828931)
  ·
    refine ⟨24835867443587321804743397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16557244962391547869828931 24835867443587321804743397)
    ·
      refine ⟨4656725145672622838389387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24835867443587321804743397 4656725145672622838389387)
      ·
        refine ⟨6985087718508934257584081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656725145672622838389387 6985087718508934257584081)
        ·
          refine ⟨5238815788881700693188061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6985087718508934257584081 5238815788881700693188061)
          ·
            refine ⟨1964555920830637759945523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5238815788881700693188061 1964555920830637759945523)
            ·
              refine ⟨2946833881245956639918285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964555920830637759945523 2946833881245956639918285)
              ·
                refine ⟨1105062705467233739969357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946833881245956639918285 1105062705467233739969357)
                ·
                  refine ⟨414398514550212652488509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105062705467233739969357 414398514550212652488509)
                  ·
                    refine ⟨155399442956329744683191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 414398514550212652488509 155399442956329744683191)
                    ·
                      rfl

theorem cell22_453959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_453959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453959 prefixEnd_453959 := by exact prefixLift 453959
  have htrace : WordTrace (prefixWord ++ tailWord_453959) baseStart_453959 baseEnd_453959 := by
    simpa [prefixWord, tailWord_453959, baseEnd_453959] using wordTrace_append hprefix tailTrace_453959
  have hstable : (prefixWord ++ tailWord_453959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453959).length < 2 ^ (prefixWord ++ tailWord_453959).sum := by decide
  have hdescent : baseEnd_453959 < baseStart_453959 := by decide
  rcases family_descends (prefixWord ++ tailWord_453959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453965 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_453965 : Nat := 118140960795 + 453965 * 2 ^ 59
def prefixEnd_453965 : Nat := 4983230072969 + 3 ^ 40 * 453965 * 2
def baseEnd_453965 : Nat := 155401496878947729033173

theorem tailTrace_453965 : CollatzResearch.WordTrace tailWord_453965 prefixEnd_453965 155401496878947729033173 := by
  unfold tailWord_453965
  simp only [CollatzResearch.WordTrace]
  refine ⟨16557463800369810894547349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11038309200246540596364899 16557463800369810894547349)
  ·
    refine ⟨776131115642334885681907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16557463800369810894547349 776131115642334885681907)
    ·
      refine ⟨1164196673463502328522861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776131115642334885681907 1164196673463502328522861)
      ·
        refine ⟨436573752548813373196073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1164196673463502328522861 436573752548813373196073)
        ·
          refine ⟨327430314411610029897055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436573752548813373196073 327430314411610029897055)
          ·
            refine ⟨491145471617415044845583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327430314411610029897055 491145471617415044845583)
            ·
              refine ⟨736718207426122567268375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491145471617415044845583 736718207426122567268375)
              ·
                refine ⟨1105077311139183850902563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736718207426122567268375 1105077311139183850902563)
                ·
                  refine ⟨1657615966708775776353845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105077311139183850902563 1657615966708775776353845)
                  ·
                    refine ⟨155401496878947729033173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1657615966708775776353845 155401496878947729033173)
                    ·
                      rfl

theorem cell22_453965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_453965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_453965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_453965 prefixEnd_453965 := by exact prefixLift 453965
  have htrace : WordTrace (prefixWord ++ tailWord_453965) baseStart_453965 baseEnd_453965 := by
    simpa [prefixWord, tailWord_453965, baseEnd_453965] using wordTrace_append hprefix tailTrace_453965
  have hstable : (prefixWord ++ tailWord_453965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453965).length < 2 ^ (prefixWord ++ tailWord_453965).sum := by decide
  have hdescent : baseEnd_453965 < baseStart_453965 := by decide
  rcases family_descends (prefixWord ++ tailWord_453965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454036 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_454036 : Nat := 118140960795 + 454036 * 2 ^ 59
def prefixEnd_454036 : Nat := 4983230072969 + 3 ^ 40 * 454036 * 2
def baseEnd_454036 : Nat := 155425801629927210507955

theorem tailTrace_454036 : CollatzResearch.WordTrace tailWord_454036 prefixEnd_454036 155425801629927210507955 := by
  unfold tailWord_454036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280026691556295010190981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11040035588741726680254641 8280026691556295010190981)
  ·
    refine ⟨1552505004666805314410809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8280026691556295010190981 1552505004666805314410809)
    ·
      refine ⟨1164378753500103985808107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1552505004666805314410809 1164378753500103985808107)
      ·
        refine ⟨1746568130250155978712161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164378753500103985808107 1746568130250155978712161)
        ·
          refine ⟨1309926097687616984034121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746568130250155978712161 1309926097687616984034121)
          ·
            refine ⟨982444573265712738025591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309926097687616984034121 982444573265712738025591)
            ·
              refine ⟨1473666859898569107038387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982444573265712738025591 1473666859898569107038387)
              ·
                refine ⟨2210500289847853660557581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473666859898569107038387 2210500289847853660557581)
                ·
                  refine ⟨828937608692945122709093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2210500289847853660557581 828937608692945122709093)
                  ·
                    refine ⟨155425801629927210507955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 828937608692945122709093 155425801629927210507955)
                    ·
                      rfl

theorem cell22_454036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_454036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454036 prefixEnd_454036 := by exact prefixLift 454036
  have htrace : WordTrace (prefixWord ++ tailWord_454036) baseStart_454036 baseEnd_454036 := by
    simpa [prefixWord, tailWord_454036, baseEnd_454036] using wordTrace_append hprefix tailTrace_454036
  have hstable : (prefixWord ++ tailWord_454036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454036).length < 2 ^ (prefixWord ++ tailWord_454036).sum := by decide
  have hdescent : baseEnd_454036 < baseStart_454036 := by decide
  rcases family_descends (prefixWord ++ tailWord_454036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454062 : List Nat := [4, 1, 17]
def baseStart_454062 : Nat := 118140960795 + 454062 * 2 ^ 59
def prefixEnd_454062 : Nat := 4983230072969 + 3 ^ 40 * 454062 * 2
def baseEnd_454062 : Nat := 71072108807165893625

theorem tailTrace_454062 : CollatzResearch.WordTrace tailWord_454062 prefixEnd_454062 71072108807165893625 := by
  unfold tailWord_454062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070125210127299557603555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11040667787345597640552293 2070125210127299557603555)
  ·
    refine ⟨3105187815190949336405333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2070125210127299557603555 3105187815190949336405333)
    ·
      refine ⟨71072108807165893625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 3105187815190949336405333 71072108807165893625)
      ·
        rfl

theorem cell22_454062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 17].length) (baseStart_454062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454062 prefixEnd_454062 := by exact prefixLift 454062
  have htrace : WordTrace (prefixWord ++ tailWord_454062) baseStart_454062 baseEnd_454062 := by
    simpa [prefixWord, tailWord_454062, baseEnd_454062] using wordTrace_append hprefix tailTrace_454062
  have hstable : (prefixWord ++ tailWord_454062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454062).length < 2 ^ (prefixWord ++ tailWord_454062).sum := by decide
  have hdescent : baseEnd_454062 < baseStart_454062 := by decide
  rcases family_descends (prefixWord ++ tailWord_454062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454107 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 13]
def baseStart_454107 : Nat := 118140960795 + 454107 * 2 ^ 59
def prefixEnd_454107 : Nat := 4983230072969 + 3 ^ 40 * 454107 * 2
def baseEnd_454107 : Nat := 51816702126968897327579

theorem tailTrace_454107 : CollatzResearch.WordTrace tailWord_454107 prefixEnd_454107 51816702126968897327579 := by
  unfold tailWord_454107
  simp only [CollatzResearch.WordTrace]
  refine ⟨16562642965855369146216575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11041761977236912764144383 16562642965855369146216575)
  ·
    refine ⟨24843964448783053719324863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16562642965855369146216575 24843964448783053719324863)
    ·
      refine ⟨37265946673174580578987295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24843964448783053719324863 37265946673174580578987295)
      ·
        refine ⟨55898920009761870868480943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37265946673174580578987295 55898920009761870868480943)
        ·
          refine ⟨83848380014642806302721415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55898920009761870868480943 83848380014642806302721415)
          ·
            refine ⟨125772570021964209454082123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83848380014642806302721415 125772570021964209454082123)
            ·
              refine ⟨188658855032946314181123185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125772570021964209454082123 188658855032946314181123185)
              ·
                refine ⟨141494141274709735635842389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188658855032946314181123185 141494141274709735635842389)
                ·
                  refine ⟨51816702126968897327579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 141494141274709735635842389 51816702126968897327579)
                  ·
                    rfl

theorem cell22_454107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_454107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454107 prefixEnd_454107 := by exact prefixLift 454107
  have htrace : WordTrace (prefixWord ++ tailWord_454107) baseStart_454107 baseEnd_454107 := by
    simpa [prefixWord, tailWord_454107, baseEnd_454107] using wordTrace_append hprefix tailTrace_454107
  have hstable : (prefixWord ++ tailWord_454107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454107).length < 2 ^ (prefixWord ++ tailWord_454107).sum := by decide
  have hdescent : baseEnd_454107 < baseStart_454107 := by decide
  rcases family_descends (prefixWord ++ tailWord_454107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454124 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 5]
def baseStart_454124 : Nat := 118140960795 + 454124 * 2 ^ 59
def prefixEnd_454124 : Nat := 4983230072969 + 3 ^ 40 * 454124 * 2
def baseEnd_454124 : Nat := 51818641942774771435895

theorem tailTrace_454124 : CollatzResearch.WordTrace tailWord_454124 prefixEnd_454124 51818641942774771435895 := by
  unfold tailWord_454124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281631503396890524792713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11042175337862520699723617 8281631503396890524792713)
  ·
    refine ⟨6211223627547667893594535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8281631503396890524792713 6211223627547667893594535)
    ·
      refine ⟨9316835441321501840391803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6211223627547667893594535 9316835441321501840391803)
      ·
        refine ⟨13975253161982252760587705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9316835441321501840391803 13975253161982252760587705)
        ·
          refine ⟨10481439871486689570440779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13975253161982252760587705 10481439871486689570440779)
          ·
            refine ⟨15722159807230034355661169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481439871486689570440779 15722159807230034355661169)
            ·
              refine ⟨11791619855422525766745877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15722159807230034355661169 11791619855422525766745877)
              ·
                refine ⟨552732180722930895316213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11791619855422525766745877 552732180722930895316213)
                ·
                  refine ⟨51818641942774771435895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 552732180722930895316213 51818641942774771435895)
                  ·
                    rfl

theorem cell22_454124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_454124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454124 prefixEnd_454124 := by exact prefixLift 454124
  have htrace : WordTrace (prefixWord ++ tailWord_454124) baseStart_454124 baseEnd_454124 := by
    simpa [prefixWord, tailWord_454124, baseEnd_454124] using wordTrace_append hprefix tailTrace_454124
  have hstable : (prefixWord ++ tailWord_454124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454124).length < 2 ^ (prefixWord ++ tailWord_454124).sum := by decide
  have hdescent : baseEnd_454124 < baseStart_454124 := by decide
  rcases family_descends (prefixWord ++ tailWord_454124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454128 : List Nat := [2, 1, 1, 1, 3, 4, 2, 4, 1, 3]
def baseStart_454128 : Nat := 118140960795 + 454128 * 2 ^ 59
def prefixEnd_454128 : Nat := 4983230072969 + 3 ^ 40 * 454128 * 2
def baseEnd_454128 : Nat := 155457295110069637207673

theorem tailTrace_454128 : CollatzResearch.WordTrace tailWord_454128 prefixEnd_454128 155457295110069637207673 := by
  unfold tailWord_454128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281704449389644866365519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11042272599186193155154025 8281704449389644866365519)
  ·
    refine ⟨12422556674084467299548279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8281704449389644866365519 12422556674084467299548279)
    ·
      refine ⟨18633835011126700949322419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12422556674084467299548279 18633835011126700949322419)
      ·
        refine ⟨27950752516690051423983629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18633835011126700949322419 27950752516690051423983629)
        ·
          refine ⟨10481532193758769283993861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27950752516690051423983629 10481532193758769283993861)
          ·
            refine ⟨1965287286329769240748849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10481532193758769283993861 1965287286329769240748849)
            ·
              refine ⟨1473965464747326930561637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965287286329769240748849 1473965464747326930561637)
              ·
                refine ⟨276368524640123799480307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1473965464747326930561637 276368524640123799480307)
                ·
                  refine ⟨414552786960185699220461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276368524640123799480307 414552786960185699220461)
                  ·
                    refine ⟨155457295110069637207673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 414552786960185699220461 155457295110069637207673)
                    ·
                      rfl

theorem cell22_454128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 3].length) (baseStart_454128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454128 prefixEnd_454128 := by exact prefixLift 454128
  have htrace : WordTrace (prefixWord ++ tailWord_454128) baseStart_454128 baseEnd_454128 := by
    simpa [prefixWord, tailWord_454128, baseEnd_454128] using wordTrace_append hprefix tailTrace_454128
  have hstable : (prefixWord ++ tailWord_454128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454128).length < 2 ^ (prefixWord ++ tailWord_454128).sum := by decide
  have hdescent : baseEnd_454128 < baseStart_454128 := by decide
  rcases family_descends (prefixWord ++ tailWord_454128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454205 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_454205 : Nat := 118140960795 + 454205 * 2 ^ 59
def prefixEnd_454205 : Nat := 4983230072969 + 3 ^ 40 * 454205 * 2
def baseEnd_454205 : Nat := 155483653783667103032437

theorem tailTrace_454205 : CollatzResearch.WordTrace tailWord_454205 prefixEnd_454205 155483653783667103032437 := by
  unfold tailWord_454205
  simp only [CollatzResearch.WordTrace]
  refine ⟨16566217319500331883284069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11044144879666887922189379 16566217319500331883284069)
  ·
    refine ⟨3106165747406312228115763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16566217319500331883284069 3106165747406312228115763)
    ·
      refine ⟨4659248621109468342173645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106165747406312228115763 4659248621109468342173645)
      ·
        refine ⟨1747218232916050628315117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4659248621109468342173645 1747218232916050628315117)
        ·
          refine ⟨655206837343518985618169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1747218232916050628315117 655206837343518985618169)
          ·
            refine ⟨491405128007639239213627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655206837343518985618169 491405128007639239213627)
            ·
              refine ⟨737107692011458858820441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491405128007639239213627 737107692011458858820441)
              ·
                refine ⟨552830769008594144115331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737107692011458858820441 552830769008594144115331)
                ·
                  refine ⟨829246153512891216172997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552830769008594144115331 829246153512891216172997)
                  ·
                    refine ⟨155483653783667103032437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 829246153512891216172997 155483653783667103032437)
                    ·
                      rfl

theorem cell22_454205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_454205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454205 prefixEnd_454205 := by exact prefixLift 454205
  have htrace : WordTrace (prefixWord ++ tailWord_454205) baseStart_454205 baseEnd_454205 := by
    simpa [prefixWord, tailWord_454205, baseEnd_454205] using wordTrace_append hprefix tailTrace_454205
  have hstable : (prefixWord ++ tailWord_454205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454205).length < 2 ^ (prefixWord ++ tailWord_454205).sum := by decide
  have hdescent : baseEnd_454205 < baseStart_454205 := by decide
  rcases family_descends (prefixWord ++ tailWord_454205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454237 : List Nat := [1, 4, 4, 2, 1, 1, 1, 4, 4]
def baseStart_454237 : Nat := 118140960795 + 454237 * 2 ^ 59
def prefixEnd_454237 : Nat := 4983230072969 + 3 ^ 40 * 454237 * 2
def baseEnd_454237 : Nat := 51831536012543228744113

theorem tailTrace_454237 : CollatzResearch.WordTrace tailWord_454237 prefixEnd_454237 51831536012543228744113 := by
  unfold tailWord_454237
  simp only [CollatzResearch.WordTrace]
  refine ⟨16567384455384401348448965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11044922970256267565632643 16567384455384401348448965)
  ·
    refine ⟨3106384585384575252834181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16567384455384401348448965 3106384585384575252834181)
    ·
      refine ⟨582447109759607859906409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3106384585384575252834181 582447109759607859906409)
      ·
        refine ⟨436835332319705894929807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582447109759607859906409 436835332319705894929807)
        ·
          refine ⟨655252998479558842394711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436835332319705894929807 655252998479558842394711)
          ·
            refine ⟨982879497719338263592067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655252998479558842394711 982879497719338263592067)
            ·
              refine ⟨1474319246579007395388101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982879497719338263592067 1474319246579007395388101)
              ·
                refine ⟨276434858733563886635269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1474319246579007395388101 276434858733563886635269)
                ·
                  refine ⟨51831536012543228744113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276434858733563886635269 51831536012543228744113)
                  ·
                    rfl

theorem cell22_454237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_454237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454237 prefixEnd_454237 := by exact prefixLift 454237
  have htrace : WordTrace (prefixWord ++ tailWord_454237) baseStart_454237 baseEnd_454237 := by
    simpa [prefixWord, tailWord_454237, baseEnd_454237] using wordTrace_append hprefix tailTrace_454237
  have hstable : (prefixWord ++ tailWord_454237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454237).length < 2 ^ (prefixWord ++ tailWord_454237).sum := by decide
  have hdescent : baseEnd_454237 < baseStart_454237 := by decide
  rcases family_descends (prefixWord ++ tailWord_454237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454248 : List Nat := [2, 1, 4, 3, 1, 3, 1, 7]
def baseStart_454248 : Nat := 118140960795 + 454248 * 2 ^ 59
def prefixEnd_454248 : Nat := 4983230072969 + 3 ^ 40 * 454248 * 2
def baseEnd_454248 : Nat := 17277597062492147134145

theorem tailTrace_454248 : CollatzResearch.WordTrace tailWord_454248 prefixEnd_454248 17277597062492147134145 := by
  unfold tailWord_454248
  simp only [CollatzResearch.WordTrace]
  refine ⟨8283892829172275113549699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11045190438896366818066265 8283892829172275113549699)
  ·
    refine ⟨12425839243758412670324549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8283892829172275113549699 12425839243758412670324549)
    ·
      refine ⟨2329844858204702375685853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12425839243758412670324549 2329844858204702375685853)
      ·
        refine ⟨873691821826763390882195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2329844858204702375685853 873691821826763390882195)
        ·
          refine ⟨1310537732740145086323293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873691821826763390882195 1310537732740145086323293)
          ·
            refine ⟨491451649777554407371235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1310537732740145086323293 491451649777554407371235)
            ·
              refine ⟨737177474666331611056853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491451649777554407371235 737177474666331611056853)
              ·
                refine ⟨17277597062492147134145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 737177474666331611056853 17277597062492147134145)
                ·
                  rfl

theorem cell22_454248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 7].length) (baseStart_454248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454248 prefixEnd_454248 := by exact prefixLift 454248
  have htrace : WordTrace (prefixWord ++ tailWord_454248) baseStart_454248 baseEnd_454248 := by
    simpa [prefixWord, tailWord_454248, baseEnd_454248] using wordTrace_append hprefix tailTrace_454248
  have hstable : (prefixWord ++ tailWord_454248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454248).length < 2 ^ (prefixWord ++ tailWord_454248).sum := by decide
  have hdescent : baseEnd_454248 < baseStart_454248 := by decide
  rcases family_descends (prefixWord ++ tailWord_454248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454323 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 1, 4]
def baseStart_454323 : Nat := 118140960795 + 454323 * 2 ^ 59
def prefixEnd_454323 : Nat := 4983230072969 + 3 ^ 40 * 454323 * 2
def baseEnd_454323 : Nat := 155524047595154128582075

theorem tailTrace_454323 : CollatzResearch.WordTrace tailWord_454323 prefixEnd_454323 155524047595154128582075 := by
  unfold tailWord_454323
  simp only [CollatzResearch.WordTrace]
  refine ⟨16570521133072838036079623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11047014088715225357386415 16570521133072838036079623)
  ·
    refine ⟨24855781699609257054119435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16570521133072838036079623 24855781699609257054119435)
    ·
      refine ⟨37283672549413885581179153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24855781699609257054119435 37283672549413885581179153)
      ·
        refine ⟨27962754412060414185884365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37283672549413885581179153 27962754412060414185884365)
        ·
          refine ⟨10486032904522655319706637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27962754412060414185884365 10486032904522655319706637)
          ·
            refine ⟨3932262339195995744889989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10486032904522655319706637 3932262339195995744889989)
            ·
              refine ⟨737299188599249202166873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3932262339195995744889989 737299188599249202166873)
              ·
                refine ⟨552974391449436901625155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737299188599249202166873 552974391449436901625155)
                ·
                  refine ⟨829461587174155352437733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552974391449436901625155 829461587174155352437733)
                  ·
                    refine ⟨155524047595154128582075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 829461587174155352437733 155524047595154128582075)
                    ·
                      rfl

theorem cell22_454323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 4].length) (baseStart_454323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454323 prefixEnd_454323 := by exact prefixLift 454323
  have htrace : WordTrace (prefixWord ++ tailWord_454323) baseStart_454323 baseEnd_454323 := by
    simpa [prefixWord, tailWord_454323, baseEnd_454323] using wordTrace_append hprefix tailTrace_454323
  have hstable : (prefixWord ++ tailWord_454323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454323).length < 2 ^ (prefixWord ++ tailWord_454323).sum := by decide
  have hdescent : baseEnd_454323 < baseStart_454323 := by decide
  rcases family_descends (prefixWord ++ tailWord_454323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454336 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_454336 : Nat := 118140960795 + 454336 * 2 ^ 59
def prefixEnd_454336 : Nat := 4983230072969 + 3 ^ 40 * 454336 * 2
def baseEnd_454336 : Nat := 155528497760826428007035

theorem tailTrace_454336 : CollatzResearch.WordTrace tailWord_454336 prefixEnd_454336 155528497760826428007035 := by
  unfold tailWord_454336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8285497641012870628151431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11047330188017160837535241 8285497641012870628151431)
  ·
    refine ⟨12428246461519305942227147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8285497641012870628151431 12428246461519305942227147)
    ·
      refine ⟨18642369692278958913340721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12428246461519305942227147 18642369692278958913340721)
      ·
        refine ⟨13981777269209219185005541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18642369692278958913340721 13981777269209219185005541)
        ·
          refine ⟨2621583237976728597188539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13981777269209219185005541 2621583237976728597188539)
          ·
            refine ⟨3932374856965092895782809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621583237976728597188539 3932374856965092895782809)
            ·
              refine ⟨2949281142723819671837107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3932374856965092895782809 2949281142723819671837107)
              ·
                refine ⟨4423921714085729507755661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949281142723819671837107 4423921714085729507755661)
                ·
                  refine ⟨1658970642782148565408373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4423921714085729507755661 1658970642782148565408373)
                  ·
                    refine ⟨155528497760826428007035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1658970642782148565408373 155528497760826428007035)
                    ·
                      rfl

theorem cell22_454336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_454336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454336 prefixEnd_454336 := by exact prefixLift 454336
  have htrace : WordTrace (prefixWord ++ tailWord_454336) baseStart_454336 baseEnd_454336 := by
    simpa [prefixWord, tailWord_454336, baseEnd_454336] using wordTrace_append hprefix tailTrace_454336
  have hstable : (prefixWord ++ tailWord_454336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454336).length < 2 ^ (prefixWord ++ tailWord_454336).sum := by decide
  have hdescent : baseEnd_454336 < baseStart_454336 := by decide
  rcases family_descends (prefixWord ++ tailWord_454336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454353 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 4, 3]
def baseStart_454353 : Nat := 118140960795 + 454353 * 2 ^ 59
def prefixEnd_454353 : Nat := 4983230072969 + 3 ^ 40 * 454353 * 2
def baseEnd_454353 : Nat := 155534317208244050331983

theorem tailTrace_454353 : CollatzResearch.WordTrace tailWord_454353 prefixEnd_454353 155534317208244050331983 := by
  unfold tailWord_454353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16571615322964153159671713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11047743548642768773114475 16571615322964153159671713)
  ·
    refine ⟨12428711492223114869753785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16571615322964153159671713 12428711492223114869753785)
    ·
      refine ⟨9321533619167336152315339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12428711492223114869753785 9321533619167336152315339)
      ·
        refine ⟨13982300428751004228473009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321533619167336152315339 13982300428751004228473009)
        ·
          refine ⟨10486725321563253171354757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13982300428751004228473009 10486725321563253171354757)
          ·
            refine ⟨1966260997793109969629017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10486725321563253171354757 1966260997793109969629017)
            ·
              refine ⟨1474695748344832477221763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966260997793109969629017 1474695748344832477221763)
              ·
                refine ⟨2212043622517248715832645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474695748344832477221763 2212043622517248715832645)
                ·
                  refine ⟨414758179221984134218621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212043622517248715832645 414758179221984134218621)
                  ·
                    refine ⟨155534317208244050331983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 414758179221984134218621 155534317208244050331983)
                    ·
                      rfl

theorem cell22_454353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_454353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454353 prefixEnd_454353 := by exact prefixLift 454353
  have htrace : WordTrace (prefixWord ++ tailWord_454353) baseStart_454353 baseEnd_454353 := by
    simpa [prefixWord, tailWord_454353, baseEnd_454353] using wordTrace_append hprefix tailTrace_454353
  have hstable : (prefixWord ++ tailWord_454353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454353).length < 2 ^ (prefixWord ++ tailWord_454353).sum := by decide
  have hdescent : baseEnd_454353 < baseStart_454353 := by decide
  rcases family_descends (prefixWord ++ tailWord_454353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454411 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 7]
def baseStart_454411 : Nat := 118140960795 + 454411 * 2 ^ 59
def prefixEnd_454411 : Nat := 4983230072969 + 3 ^ 40 * 454411 * 2
def baseEnd_454411 : Nat := 51851390597850410793935

theorem tailTrace_454411 : CollatzResearch.WordTrace tailWord_454411 prefixEnd_454411 51851390597850410793935 := by
  unfold tailWord_454411
  simp only [CollatzResearch.WordTrace]
  refine ⟨16573730756754029065283087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11049153837836019376855391 16573730756754029065283087)
  ·
    refine ⟨24860596135131043597924631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16573730756754029065283087 24860596135131043597924631)
    ·
      refine ⟨37290894202696565396886947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24860596135131043597924631 37290894202696565396886947)
      ·
        refine ⟨55936341304044848095330421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37290894202696565396886947 55936341304044848095330421)
        ·
          refine ⟨5244031997254204508937227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55936341304044848095330421 5244031997254204508937227)
          ·
            refine ⟨7866047995881306763405841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244031997254204508937227 7866047995881306763405841)
            ·
              refine ⟨5899535996910980072554381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7866047995881306763405841 5899535996910980072554381)
              ·
                refine ⟨2212325998841617527207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5899535996910980072554381 2212325998841617527207893)
                ·
                  refine ⟨51851390597850410793935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2212325998841617527207893 51851390597850410793935)
                  ·
                    rfl

theorem cell22_454411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_454411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454411 prefixEnd_454411 := by exact prefixLift 454411
  have htrace : WordTrace (prefixWord ++ tailWord_454411) baseStart_454411 baseEnd_454411 := by
    simpa [prefixWord, tailWord_454411, baseEnd_454411] using wordTrace_append hprefix tailTrace_454411
  have hstable : (prefixWord ++ tailWord_454411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454411).length < 2 ^ (prefixWord ++ tailWord_454411).sum := by decide
  have hdescent : baseEnd_454411 < baseStart_454411 := by decide
  rcases family_descends (prefixWord ++ tailWord_454411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454428 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 5]
def baseStart_454428 : Nat := 118140960795 + 454428 * 2 ^ 59
def prefixEnd_454428 : Nat := 4983230072969 + 3 ^ 40 * 454428 * 2
def baseEnd_454428 : Nat := 51853330413656284902251

theorem tailTrace_454428 : CollatzResearch.WordTrace tailWord_454428 prefixEnd_454428 51853330413656284902251 := by
  unfold tailWord_454428
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287175398846220484325969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11049567198461627312434625 8287175398846220484325969)
  ·
    refine ⟨6215381549134665363244477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8287175398846220484325969 6215381549134665363244477)
    ·
      refine ⟨2330768080925499511216679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6215381549134665363244477 2330768080925499511216679)
      ·
        refine ⟨3496152121388249266825019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330768080925499511216679 3496152121388249266825019)
        ·
          refine ⟨5244228182082373900237529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496152121388249266825019 5244228182082373900237529)
          ·
            refine ⟨3933171136561780425178147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5244228182082373900237529 3933171136561780425178147)
            ·
              refine ⟨5899756704842670637767221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933171136561780425178147 5899756704842670637767221)
              ·
                refine ⟨553102191079000372290677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5899756704842670637767221 553102191079000372290677)
                ·
                  refine ⟨51853330413656284902251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 553102191079000372290677 51853330413656284902251)
                  ·
                    rfl

theorem cell22_454428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_454428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454428 prefixEnd_454428 := by exact prefixLift 454428
  have htrace : WordTrace (prefixWord ++ tailWord_454428) baseStart_454428 baseEnd_454428 := by
    simpa [prefixWord, tailWord_454428, baseEnd_454428] using wordTrace_append hprefix tailTrace_454428
  have hstable : (prefixWord ++ tailWord_454428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454428).length < 2 ^ (prefixWord ++ tailWord_454428).sum := by decide
  have hdescent : baseEnd_454428 < baseStart_454428 := by decide
  rcases family_descends (prefixWord ++ tailWord_454428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454462 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_454462 : Nat := 118140960795 + 454462 * 2 ^ 59
def prefixEnd_454462 : Nat := 4983230072969 + 3 ^ 40 * 454462 * 2
def baseEnd_454462 : Nat := 51857210045268033118883

theorem tailTrace_454462 : CollatzResearch.WordTrace tailWord_454462 prefixEnd_454462 51857210045268033118883 := by
  unfold tailWord_454462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071948859946158096923705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11050393919712843183593093 2071948859946158096923705)
  ·
    refine ⟨1553961644959618572692779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2071948859946158096923705 1553961644959618572692779)
    ·
      refine ⟨2330942467439427859039169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553961644959618572692779 2330942467439427859039169)
      ·
        refine ⟨1748206850579570894279377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330942467439427859039169 1748206850579570894279377)
        ·
          refine ⟨1311155137934678170709533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748206850579570894279377 1311155137934678170709533)
          ·
            refine ⟨491683176725504314016075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1311155137934678170709533 491683176725504314016075)
            ·
              refine ⟨737524765088256471024113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491683176725504314016075 737524765088256471024113)
              ·
                refine ⟨553143573816192353268085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737524765088256471024113 553143573816192353268085)
                ·
                  refine ⟨51857210045268033118883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 553143573816192353268085 51857210045268033118883)
                  ·
                    rfl

theorem cell22_454462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_454462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454462 prefixEnd_454462 := by exact prefixLift 454462
  have htrace : WordTrace (prefixWord ++ tailWord_454462) baseStart_454462 baseEnd_454462 := by
    simpa [prefixWord, tailWord_454462, baseEnd_454462] using wordTrace_append hprefix tailTrace_454462
  have hstable : (prefixWord ++ tailWord_454462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454462).length < 2 ^ (prefixWord ++ tailWord_454462).sum := by decide
  have hdescent : baseEnd_454462 < baseStart_454462 := by decide
  rcases family_descends (prefixWord ++ tailWord_454462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454473 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 6]
def baseStart_454473 : Nat := 118140960795 + 454473 * 2 ^ 59
def prefixEnd_454473 : Nat := 4983230072969 + 3 ^ 40 * 454473 * 2
def baseEnd_454473 : Nat := 51858465220201245777205

theorem tailTrace_454473 : CollatzResearch.WordTrace tailWord_454473 prefixEnd_454473 51858465220201245777205 := by
  unfold tailWord_454473
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575992082529413654040073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11050661388352942436026715 16575992082529413654040073)
  ·
    refine ⟨12431994061897060240530055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16575992082529413654040073 12431994061897060240530055)
    ·
      refine ⟨18647991092845590360795083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12431994061897060240530055 18647991092845590360795083)
      ·
        refine ⟨27971986639268385541192625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18647991092845590360795083 27971986639268385541192625)
        ·
          refine ⟨20978989979451289155894469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27971986639268385541192625 20978989979451289155894469)
          ·
            refine ⟨3933560621147116716730213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20978989979451289155894469 3933560621147116716730213)
            ·
              refine ⟨737542616465084384386915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3933560621147116716730213 737542616465084384386915)
              ·
                refine ⟨1106313924697626576580373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737542616465084384386915 1106313924697626576580373)
                ·
                  refine ⟨51858465220201245777205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1106313924697626576580373 51858465220201245777205)
                  ·
                    rfl

theorem cell22_454473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_454473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454473 prefixEnd_454473 := by exact prefixLift 454473
  have htrace : WordTrace (prefixWord ++ tailWord_454473) baseStart_454473 baseEnd_454473 := by
    simpa [prefixWord, tailWord_454473, baseEnd_454473] using wordTrace_append hprefix tailTrace_454473
  have hstable : (prefixWord ++ tailWord_454473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454473).length < 2 ^ (prefixWord ++ tailWord_454473).sum := by decide
  have hdescent : baseEnd_454473 < baseStart_454473 := by decide
  rcases family_descends (prefixWord ++ tailWord_454473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454503 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 1, 6]
def baseStart_454503 : Nat := 118140960795 + 454503 * 2 ^ 59
def prefixEnd_454503 : Nat := 4983230072969 + 3 ^ 40 * 454503 * 2
def baseEnd_454503 : Nat := 155585665273693659081523

theorem tailTrace_454503 : CollatzResearch.WordTrace tailWord_454503 prefixEnd_454503 155585665273693659081523 := by
  unfold tailWord_454503
  simp only [CollatzResearch.WordTrace]
  refine ⟨16577086272420728777632163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11051390848280485851754775 16577086272420728777632163)
  ·
    refine ⟨24865629408631093166448245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16577086272420728777632163 24865629408631093166448245)
    ·
      refine ⟨2331152757059164984354523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24865629408631093166448245 2331152757059164984354523)
      ·
        refine ⟨3496729135588747476531785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2331152757059164984354523 3496729135588747476531785)
        ·
          refine ⟨2622546851691560607398839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3496729135588747476531785 2622546851691560607398839)
          ·
            refine ⟨3933820277537340911098259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622546851691560607398839 3933820277537340911098259)
            ·
              refine ⟨5900730416306011366647389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933820277537340911098259 5900730416306011366647389)
              ·
                refine ⟨2212773906114754262492771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5900730416306011366647389 2212773906114754262492771)
                ·
                  refine ⟨3319160859172131393739157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212773906114754262492771 3319160859172131393739157)
                  ·
                    refine ⟨155585665273693659081523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3319160859172131393739157 155585665273693659081523)
                    ·
                      rfl

theorem cell22_454503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_454503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454503 prefixEnd_454503 := by exact prefixLift 454503
  have htrace : WordTrace (prefixWord ++ tailWord_454503) baseStart_454503 baseEnd_454503 := by
    simpa [prefixWord, tailWord_454503, baseEnd_454503] using wordTrace_append hprefix tailTrace_454503
  have hstable : (prefixWord ++ tailWord_454503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454503).length < 2 ^ (prefixWord ++ tailWord_454503).sum := by decide
  have hdescent : baseEnd_454503 < baseStart_454503 := by decide
  rcases family_descends (prefixWord ++ tailWord_454503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454535 : List Nat := [1, 1, 4, 2, 4, 1, 2, 7]
def baseStart_454535 : Nat := 118140960795 + 454535 * 2 ^ 59
def prefixEnd_454535 : Nat := 4983230072969 + 3 ^ 40 * 454535 * 2
def baseEnd_454535 : Nat := 17288513280850693586825

theorem tailTrace_454535 : CollatzResearch.WordTrace tailWord_454535 prefixEnd_454535 17288513280850693586825 := by
  unfold tailWord_454535
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578253408304798242797059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11052168938869865495198039 16578253408304798242797059)
  ·
    refine ⟨24867380112457197364195589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16578253408304798242797059 24867380112457197364195589)
    ·
      refine ⟨4662633771085724505786673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24867380112457197364195589 4662633771085724505786673)
      ·
        refine ⟨3496975328314293379340005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4662633771085724505786673 3496975328314293379340005)
        ·
          refine ⟨655682874058930008626251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3496975328314293379340005 655682874058930008626251)
          ·
            refine ⟨983524311088395012939377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655682874058930008626251 983524311088395012939377)
            ·
              refine ⟨737643233316296259704533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983524311088395012939377 737643233316296259704533)
              ·
                refine ⟨17288513280850693586825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 737643233316296259704533 17288513280850693586825)
                ·
                  rfl

theorem cell22_454535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 7].length) (baseStart_454535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454535 prefixEnd_454535 := by exact prefixLift 454535
  have htrace : WordTrace (prefixWord ++ tailWord_454535) baseStart_454535 baseEnd_454535 := by
    simpa [prefixWord, tailWord_454535, baseEnd_454535] using wordTrace_append hprefix tailTrace_454535
  have hstable : (prefixWord ++ tailWord_454535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454535).length < 2 ^ (prefixWord ++ tailWord_454535).sum := by decide
  have hdescent : baseEnd_454535 < baseStart_454535 := by decide
  rcases family_descends (prefixWord ++ tailWord_454535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454578 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_454578 : Nat := 118140960795 + 454578 * 2 ^ 59
def prefixEnd_454578 : Nat := 4983230072969 + 3 ^ 40 * 454578 * 2
def baseEnd_454578 : Nat := 155611339306418463456293

theorem tailTrace_454578 : CollatzResearch.WordTrace tailWord_454578 prefixEnd_454578 155611339306418463456293 := by
  unfold tailWord_454578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4144955436787254146653097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11053214498099344391074925 4144955436787254146653097)
  ·
    refine ⟨3108716577590440609989823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4144955436787254146653097 3108716577590440609989823)
    ·
      refine ⟨4663074866385660914984735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108716577590440609989823 4663074866385660914984735)
      ·
        refine ⟨6994612299578491372477103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663074866385660914984735 6994612299578491372477103)
        ·
          refine ⟨10491918449367737058715655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994612299578491372477103 10491918449367737058715655)
          ·
            refine ⟨15737877674051605588073483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491918449367737058715655 15737877674051605588073483)
            ·
              refine ⟨23606816511077408382110225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15737877674051605588073483 23606816511077408382110225)
              ·
                refine ⟨17705112383308056286582669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23606816511077408382110225 17705112383308056286582669)
                ·
                  refine ⟨6639417143740521107468501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17705112383308056286582669 6639417143740521107468501)
                  ·
                    refine ⟨155611339306418463456293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6639417143740521107468501 155611339306418463456293)
                    ·
                      rfl

theorem cell22_454578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_454578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454578 prefixEnd_454578 := by exact prefixLift 454578
  have htrace : WordTrace (prefixWord ++ tailWord_454578) baseStart_454578 baseEnd_454578 := by
    simpa [prefixWord, tailWord_454578, baseEnd_454578] using wordTrace_append hprefix tailTrace_454578
  have hstable : (prefixWord ++ tailWord_454578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454578).length < 2 ^ (prefixWord ++ tailWord_454578).sum := by decide
  have hdescent : baseEnd_454578 < baseStart_454578 := by decide
  rcases family_descends (prefixWord ++ tailWord_454578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454608 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 8]
def baseStart_454608 : Nat := 118140960795 + 454608 * 2 ^ 59
def prefixEnd_454608 : Nat := 4983230072969 + 3 ^ 40 * 454608 * 2
def baseEnd_454608 : Nat := 51873869639836128402067

theorem tailTrace_454608 : CollatzResearch.WordTrace tailWord_454608 prefixEnd_454608 51873869639836128402067 := by
  unfold tailWord_454608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290457968520165855102239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11053943958026887806802985 8290457968520165855102239)
  ·
    refine ⟨12435686952780248782653359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8290457968520165855102239 12435686952780248782653359)
    ·
      refine ⟨18653530429170373173980039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12435686952780248782653359 18653530429170373173980039)
      ·
        refine ⟨27980295643755559760970059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18653530429170373173980039 27980295643755559760970059)
        ·
          refine ⟨41970443465633339641455089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27980295643755559760970059 41970443465633339641455089)
          ·
            refine ⟨31477832599225004731091317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41970443465633339641455089 31477832599225004731091317)
            ·
              refine ⟨2951046806177344193539811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31477832599225004731091317 2951046806177344193539811)
              ·
                refine ⟨4426570209266016290309717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951046806177344193539811 4426570209266016290309717)
                ·
                  refine ⟨51873869639836128402067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4426570209266016290309717 51873869639836128402067)
                  ·
                    rfl

theorem cell22_454608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_454608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454608 prefixEnd_454608 := by exact prefixLift 454608
  have htrace : WordTrace (prefixWord ++ tailWord_454608) baseStart_454608 baseEnd_454608 := by
    simpa [prefixWord, tailWord_454608, baseEnd_454608] using wordTrace_append hprefix tailTrace_454608
  have hstable : (prefixWord ++ tailWord_454608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454608).length < 2 ^ (prefixWord ++ tailWord_454608).sum := by decide
  have hdescent : baseEnd_454608 < baseStart_454608 := by decide
  rcases family_descends (prefixWord ++ tailWord_454608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454627 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 1, 4]
def baseStart_454627 : Nat := 118140960795 + 454627 * 2 ^ 59
def prefixEnd_454627 : Nat := 4983230072969 + 3 ^ 40 * 454627 * 2
def baseEnd_454627 : Nat := 155628113007798668981143

theorem tailTrace_454627 : CollatzResearch.WordTrace tailWord_454627 prefixEnd_454627 155628113007798668981143 := by
  unfold tailWord_454627
  simp only [CollatzResearch.WordTrace]
  refine ⟨16581608923971497955146135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11054405949314331970097423 16581608923971497955146135)
  ·
    refine ⟨24872413385957246932719203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16581608923971497955146135 24872413385957246932719203)
    ·
      refine ⟨37308620078935870399078805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24872413385957246932719203 37308620078935870399078805)
      ·
        refine ⟨1748841566200118924956819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37308620078935870399078805 1748841566200118924956819)
        ·
          refine ⟨2623262349300178387435229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748841566200118924956819 2623262349300178387435229)
          ·
            refine ⟨983723380987566895288211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2623262349300178387435229 983723380987566895288211)
            ·
              refine ⟨1475585071481350342932317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983723380987566895288211 1475585071481350342932317)
              ·
                refine ⟨553344401805506378599619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1475585071481350342932317 553344401805506378599619)
                ·
                  refine ⟨830016602708259567899429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553344401805506378599619 830016602708259567899429)
                  ·
                    refine ⟨155628113007798668981143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830016602708259567899429 155628113007798668981143)
                    ·
                      rfl

theorem cell22_454627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 4].length) (baseStart_454627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454627 prefixEnd_454627 := by exact prefixLift 454627
  have htrace : WordTrace (prefixWord ++ tailWord_454627) baseStart_454627 baseEnd_454627 := by
    simpa [prefixWord, tailWord_454627, baseEnd_454627] using wordTrace_append hprefix tailTrace_454627
  have hstable : (prefixWord ++ tailWord_454627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454627).length < 2 ^ (prefixWord ++ tailWord_454627).sum := by decide
  have hdescent : baseEnd_454627 < baseStart_454627 := by decide
  rcases family_descends (prefixWord ++ tailWord_454627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454670 : List Nat := [4, 1, 1, 2, 2, 1, 3, 8]
def baseStart_454670 : Nat := 118140960795 + 454670 * 2 ^ 59
def prefixEnd_454670 : Nat := 4983230072969 + 3 ^ 40 * 454670 * 2
def baseEnd_454670 : Nat := 17293648087395654461779

theorem tailTrace_454670 : CollatzResearch.WordTrace tailWord_454670 prefixEnd_454670 17293648087395654461779 := by
  unfold tailWord_454670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072897157851964537370183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11055451508543810865974309 2072897157851964537370183)
  ·
    refine ⟨3109345736777946806055275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2072897157851964537370183 3109345736777946806055275)
    ·
      refine ⟨4664018605166920209082913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3109345736777946806055275 4664018605166920209082913)
      ·
        refine ⟨3498013953875190156812185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4664018605166920209082913 3498013953875190156812185)
        ·
          refine ⟨2623510465406392617609139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3498013953875190156812185 2623510465406392617609139)
          ·
            refine ⟨3935265698109588926413709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623510465406392617609139 3935265698109588926413709)
            ·
              refine ⟨1475724636791095847405141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3935265698109588926413709 1475724636791095847405141)
              ·
                refine ⟨17293648087395654461779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1475724636791095847405141 17293648087395654461779)
                ·
                  rfl

theorem cell22_454670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_454670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454670 prefixEnd_454670 := by exact prefixLift 454670
  have htrace : WordTrace (prefixWord ++ tailWord_454670) baseStart_454670 baseEnd_454670 := by
    simpa [prefixWord, tailWord_454670, baseEnd_454670] using wordTrace_append hprefix tailTrace_454670
  have hstable : (prefixWord ++ tailWord_454670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454670).length < 2 ^ (prefixWord ++ tailWord_454670).sum := by decide
  have hdescent : baseEnd_454670 < baseStart_454670 := by decide
  rcases family_descends (prefixWord ++ tailWord_454670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454715 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 5]
def baseStart_454715 : Nat := 118140960795 + 454715 * 2 ^ 59
def prefixEnd_454715 : Nat := 4983230072969 + 3 ^ 40 * 454715 * 2
def baseEnd_454715 : Nat := 51886079068731924260291

theorem tailTrace_454715 : CollatzResearch.WordTrace tailWord_454715 prefixEnd_454715 51886079068731924260291 := by
  unfold tailWord_454715
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584818547652688984349599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11056545698435125989566399 16584818547652688984349599)
  ·
    refine ⟨24877227821479033476524399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16584818547652688984349599 24877227821479033476524399)
    ·
      refine ⟨37315841732218550214786599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24877227821479033476524399 37315841732218550214786599)
      ·
        refine ⟨55973762598327825322179899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37315841732218550214786599 55973762598327825322179899)
        ·
          refine ⟨83960643897491737983269849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55973762598327825322179899 83960643897491737983269849)
          ·
            refine ⟨62970482923118803487452387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83960643897491737983269849 62970482923118803487452387)
            ·
              refine ⟨94455724384678205231178581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62970482923118803487452387 94455724384678205231178581)
              ·
                refine ⟨553451510066473858776437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 94455724384678205231178581 553451510066473858776437)
                ·
                  refine ⟨51886079068731924260291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 553451510066473858776437 51886079068731924260291)
                  ·
                    rfl

theorem cell22_454715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 5].length) (baseStart_454715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454715 prefixEnd_454715 := by exact prefixLift 454715
  have htrace : WordTrace (prefixWord ++ tailWord_454715) baseStart_454715 baseEnd_454715 := by
    simpa [prefixWord, tailWord_454715, baseEnd_454715] using wordTrace_append hprefix tailTrace_454715
  have hstable : (prefixWord ++ tailWord_454715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454715).length < 2 ^ (prefixWord ++ tailWord_454715).sum := by decide
  have hdescent : baseEnd_454715 < baseStart_454715 := by decide
  rcases family_descends (prefixWord ++ tailWord_454715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454730 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_454730 : Nat := 118140960795 + 454730 * 2 ^ 59
def prefixEnd_454730 : Nat := 4983230072969 + 3 ^ 40 * 454730 * 2
def baseEnd_454730 : Nat := 155663372012740733655827

theorem tailTrace_454730 : CollatzResearch.WordTrace tailWord_454730 prefixEnd_454730 155663372012740733655827 := by
  unfold tailWord_454730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146341410649586636536411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11056910428398897697430429 4146341410649586636536411)
  ·
    refine ⟨6219512115974379954804617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4146341410649586636536411 6219512115974379954804617)
    ·
      refine ⟨4664634086980784966103463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6219512115974379954804617 4664634086980784966103463)
      ·
        refine ⟨6996951130471177449155195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4664634086980784966103463 6996951130471177449155195)
        ·
          refine ⟨10495426695706766173732793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6996951130471177449155195 10495426695706766173732793)
          ·
            refine ⟨7871570021780074630299595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10495426695706766173732793 7871570021780074630299595)
            ·
              refine ⟨11807355032670111945449393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871570021780074630299595 11807355032670111945449393)
              ·
                refine ⟨8855516274502583959087045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11807355032670111945449393 8855516274502583959087045)
                ·
                  refine ⟨1660409301469234492328821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8855516274502583959087045 1660409301469234492328821)
                  ·
                    refine ⟨155663372012740733655827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1660409301469234492328821 155663372012740733655827)
                    ·
                      rfl

theorem cell22_454730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_454730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454730 prefixEnd_454730 := by exact prefixLift 454730
  have htrace : WordTrace (prefixWord ++ tailWord_454730) baseStart_454730 baseEnd_454730 := by
    simpa [prefixWord, tailWord_454730, baseEnd_454730] using wordTrace_append hprefix tailTrace_454730
  have hstable : (prefixWord ++ tailWord_454730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454730).length < 2 ^ (prefixWord ++ tailWord_454730).sum := by decide
  have hdescent : baseEnd_454730 < baseStart_454730 := by decide
  rcases family_descends (prefixWord ++ tailWord_454730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454749 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 5]
def baseStart_454749 : Nat := 118140960795 + 454749 * 2 ^ 59
def prefixEnd_454749 : Nat := 4983230072969 + 3 ^ 40 * 454749 * 2
def baseEnd_454749 : Nat := 51889958700343672476923

theorem tailTrace_454749 : CollatzResearch.WordTrace tailWord_454749 prefixEnd_454749 51889958700343672476923 := by
  unfold tailWord_454749
  simp only [CollatzResearch.WordTrace]
  refine ⟨16586058629529512791087301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11057372419686341860724867 16586058629529512791087301)
  ·
    refine ⟨3109885993036783648328869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16586058629529512791087301 3109885993036783648328869)
    ·
      refine ⟨583103623694396934061663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3109885993036783648328869 583103623694396934061663)
      ·
        refine ⟨874655435541595401092495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583103623694396934061663 874655435541595401092495)
        ·
          refine ⟨1311983153312393101638743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874655435541595401092495 1311983153312393101638743)
          ·
            refine ⟨1967974729968589652458115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311983153312393101638743 1967974729968589652458115)
            ·
              refine ⟨2951962094952884478687173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967974729968589652458115 2951962094952884478687173)
              ·
                refine ⟨553492892803665839753845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2951962094952884478687173 553492892803665839753845)
                ·
                  refine ⟨51889958700343672476923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 553492892803665839753845 51889958700343672476923)
                  ·
                    rfl

theorem cell22_454749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_454749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454749 prefixEnd_454749 := by exact prefixLift 454749
  have htrace : WordTrace (prefixWord ++ tailWord_454749) baseStart_454749 baseEnd_454749 := by
    simpa [prefixWord, tailWord_454749, baseEnd_454749] using wordTrace_append hprefix tailTrace_454749
  have hstable : (prefixWord ++ tailWord_454749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454749).length < 2 ^ (prefixWord ++ tailWord_454749).sum := by decide
  have hdescent : baseEnd_454749 < baseStart_454749 := by decide
  rcases family_descends (prefixWord ++ tailWord_454749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454777 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 6]
def baseStart_454777 : Nat := 118140960795 + 454777 * 2 ^ 59
def prefixEnd_454777 : Nat := 4983230072969 + 3 ^ 40 * 454777 * 2
def baseEnd_454777 : Nat := 51893153691082759243561

theorem tailTrace_454777 : CollatzResearch.WordTrace tailWord_454777 prefixEnd_454777 51893153691082759243561 := by
  unfold tailWord_454777
  simp only [CollatzResearch.WordTrace]
  refine ⟨16587079873428073573106585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11058053248952049048737723 16587079873428073573106585)
  ·
    refine ⟨12440309905071055179829939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16587079873428073573106585 12440309905071055179829939)
    ·
      refine ⟨18660464857606582769744909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12440309905071055179829939 18660464857606582769744909)
      ·
        refine ⟨6997674321602468538654341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18660464857606582769744909 6997674321602468538654341)
        ·
          refine ⟨1312063935300462850997689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6997674321602468538654341 1312063935300462850997689)
          ·
            refine ⟨984047951475347138248267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312063935300462850997689 984047951475347138248267)
            ·
              refine ⟨1476071927213020707372401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984047951475347138248267 1476071927213020707372401)
              ·
                refine ⟨1107053945409765530529301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476071927213020707372401 1107053945409765530529301)
                ·
                  refine ⟨51893153691082759243561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1107053945409765530529301 51893153691082759243561)
                  ·
                    rfl

theorem cell22_454777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_454777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454777 prefixEnd_454777 := by exact prefixLift 454777
  have htrace : WordTrace (prefixWord ++ tailWord_454777) baseStart_454777 baseEnd_454777 := by
    simpa [prefixWord, tailWord_454777, baseEnd_454777] using wordTrace_append hprefix tailTrace_454777
  have hstable : (prefixWord ++ tailWord_454777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454777).length < 2 ^ (prefixWord ++ tailWord_454777).sum := by decide
  have hdescent : baseEnd_454777 < baseStart_454777 := by decide
  rcases family_descends (prefixWord ++ tailWord_454777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454794 : List Nat := [3, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_454794 : Nat := 118140960795 + 454794 * 2 ^ 59
def prefixEnd_454794 : Nat := 4983230072969 + 3 ^ 40 * 454794 * 2
def baseEnd_454794 : Nat := 51895093506888633351877

theorem tailTrace_454794 : CollatzResearch.WordTrace tailWord_454794 prefixEnd_454794 51895093506888633351877 := by
  unfold tailWord_454794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146924978591621369118859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11058466609577656984316957 4146924978591621369118859)
  ·
    refine ⟨6220387467887432053678289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4146924978591621369118859 6220387467887432053678289)
    ·
      refine ⟨4665290600915574040258717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6220387467887432053678289 4665290600915574040258717)
      ·
        refine ⟨1749483975343340265097019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4665290600915574040258717 1749483975343340265097019)
        ·
          refine ⟨2624225963015010397645529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749483975343340265097019 2624225963015010397645529)
          ·
            refine ⟨1968169472261257798234147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2624225963015010397645529 1968169472261257798234147)
            ·
              refine ⟨2952254208391886697351221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968169472261257798234147 2952254208391886697351221)
              ·
                refine ⟨276773832036739377876677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2952254208391886697351221 276773832036739377876677)
                ·
                  refine ⟨51895093506888633351877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276773832036739377876677 51895093506888633351877)
                  ·
                    rfl

theorem cell22_454794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_454794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454794 prefixEnd_454794 := by exact prefixLift 454794
  have htrace : WordTrace (prefixWord ++ tailWord_454794) baseStart_454794 baseEnd_454794 := by
    simpa [prefixWord, tailWord_454794, baseEnd_454794] using wordTrace_append hprefix tailTrace_454794
  have hstable : (prefixWord ++ tailWord_454794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454794).length < 2 ^ (prefixWord ++ tailWord_454794).sum := by decide
  have hdescent : baseEnd_454794 < baseStart_454794 := by decide
  rcases family_descends (prefixWord ++ tailWord_454794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454805 : List Nat := [1, 3, 2, 1, 1, 1, 13]
def baseStart_454805 : Nat := 118140960795 + 454805 * 2 ^ 59
def prefixEnd_454805 : Nat := 4983230072969 + 3 ^ 40 * 454805 * 2
def baseEnd_454805 : Nat := 5766260964646871778911

theorem tailTrace_454805 : CollatzResearch.WordTrace tailWord_454805 prefixEnd_454805 5766260964646871778911 := by
  unfold tailWord_454805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16588101117326634355125869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11058734078217756236750579 16588101117326634355125869)
  ·
    refine ⟨6220537918997487883172201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16588101117326634355125869 6220537918997487883172201)
    ·
      refine ⟨4665403439248115912379151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6220537918997487883172201 4665403439248115912379151)
      ·
        refine ⟨6998105158872173868568727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665403439248115912379151 6998105158872173868568727)
        ·
          refine ⟨10497157738308260802853091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998105158872173868568727 10497157738308260802853091)
          ·
            refine ⟨15745736607462391204279637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497157738308260802853091 15745736607462391204279637)
            ·
              refine ⟨5766260964646871778911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 15745736607462391204279637 5766260964646871778911)
              ·
                rfl

theorem cell22_454805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 13].length) (baseStart_454805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454805 prefixEnd_454805 := by exact prefixLift 454805
  have htrace : WordTrace (prefixWord ++ tailWord_454805) baseStart_454805 baseEnd_454805 := by
    simpa [prefixWord, tailWord_454805, baseEnd_454805] using wordTrace_append hprefix tailTrace_454805
  have hstable : (prefixWord ++ tailWord_454805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454805).length < 2 ^ (prefixWord ++ tailWord_454805).sum := by decide
  have hdescent : baseEnd_454805 < baseStart_454805 := by decide
  rcases family_descends (prefixWord ++ tailWord_454805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454839 : List Nat := [1, 1, 3, 1, 4, 4, 2, 6]
def baseStart_454839 : Nat := 118140960795 + 454839 * 2 ^ 59
def prefixEnd_454839 : Nat := 4983230072969 + 3 ^ 40 * 454839 * 2
def baseEnd_454839 : Nat := 17300076104477864742277

theorem tailTrace_454839 : CollatzResearch.WordTrace tailWord_454839 prefixEnd_454839 17300076104477864742277 := by
  unfold tailWord_454839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16589341199203458161863571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11059560799468972107909047 16589341199203458161863571)
  ·
    refine ⟨24884011798805187242795357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16589341199203458161863571 24884011798805187242795357)
    ·
      refine ⟨9331504424551945216048259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24884011798805187242795357 9331504424551945216048259)
      ·
        refine ⟨13997256636827917824072389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9331504424551945216048259 13997256636827917824072389)
        ·
          refine ⟨2624485619405234592013573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13997256636827917824072389 2624485619405234592013573)
          ·
            refine ⟨492091053638481486002545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2624485619405234592013573 492091053638481486002545)
            ·
              refine ⟨369068290228861114501909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492091053638481486002545 369068290228861114501909)
              ·
                refine ⟨17300076104477864742277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 369068290228861114501909 17300076104477864742277)
                ·
                  rfl

theorem cell22_454839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 6].length) (baseStart_454839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454839 prefixEnd_454839 := by exact prefixLift 454839
  have htrace : WordTrace (prefixWord ++ tailWord_454839) baseStart_454839 baseEnd_454839 := by
    simpa [prefixWord, tailWord_454839, baseEnd_454839] using wordTrace_append hprefix tailTrace_454839
  have hstable : (prefixWord ++ tailWord_454839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454839).length < 2 ^ (prefixWord ++ tailWord_454839).sum := by decide
  have hdescent : baseEnd_454839 < baseStart_454839 := by decide
  rcases family_descends (prefixWord ++ tailWord_454839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454944 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_454944 : Nat := 118140960795 + 454944 * 2 ^ 59
def prefixEnd_454944 : Nat := 4983230072969 + 3 ^ 40 * 454944 * 2
def baseEnd_454944 : Nat := 155736628586115508805171

theorem tailTrace_454944 : CollatzResearch.WordTrace tailWord_454944 prefixEnd_454944 155736628586115508805171 := by
  unfold tailWord_454944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296585431911530547217943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11062113909215374062957257 8296585431911530547217943)
  ·
    refine ⟨12444878147867295820826915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8296585431911530547217943 12444878147867295820826915)
    ·
      refine ⟨18667317221800943731240373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12444878147867295820826915 18667317221800943731240373)
      ·
        refine ⟨1750060989543838474803785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18667317221800943731240373 1750060989543838474803785)
        ·
          refine ⟨1312545742157878856102839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1750060989543838474803785 1312545742157878856102839)
          ·
            refine ⟨1968818613236818284154259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312545742157878856102839 1968818613236818284154259)
            ·
              refine ⟨2953227919855227426231389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968818613236818284154259 2953227919855227426231389)
              ·
                refine ⟨1107460469945710284836771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2953227919855227426231389 1107460469945710284836771)
                ·
                  refine ⟨1661190704918565427255157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107460469945710284836771 1661190704918565427255157)
                  ·
                    refine ⟨155736628586115508805171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1661190704918565427255157 155736628586115508805171)
                    ·
                      rfl

theorem cell22_454944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_454944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454944 prefixEnd_454944 := by exact prefixLift 454944
  have htrace : WordTrace (prefixWord ++ tailWord_454944) baseStart_454944 baseEnd_454944 := by
    simpa [prefixWord, tailWord_454944, baseEnd_454944] using wordTrace_append hprefix tailTrace_454944
  have hstable : (prefixWord ++ tailWord_454944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454944).length < 2 ^ (prefixWord ++ tailWord_454944).sum := by decide
  have hdescent : baseEnd_454944 < baseStart_454944 := by decide
  rcases family_descends (prefixWord ++ tailWord_454944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454959 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 2, 4]
def baseStart_454959 : Nat := 118140960795 + 454959 * 2 ^ 59
def prefixEnd_454959 : Nat := 4983230072969 + 3 ^ 40 * 454959 * 2
def baseEnd_454959 : Nat := 155741763392660469680125

theorem tailTrace_454959 : CollatzResearch.WordTrace tailWord_454959 prefixEnd_454959 155741763392660469680125 := by
  unfold tailWord_454959
  simp only [CollatzResearch.WordTrace]
  refine ⟨16593717958768718656231931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11062478639179145770821287 16593717958768718656231931)
  ·
    refine ⟨24890576938153077984347897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16593717958768718656231931 24890576938153077984347897)
    ·
      refine ⟨18667932703614808488260923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24890576938153077984347897 18667932703614808488260923)
      ·
        refine ⟨28001899055422212732391385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18667932703614808488260923 28001899055422212732391385)
        ·
          refine ⟨21001424291566659549293539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28001899055422212732391385 21001424291566659549293539)
          ·
            refine ⟨31502136437349989323940309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21001424291566659549293539 31502136437349989323940309)
            ·
              refine ⟨738331322750390374779851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31502136437349989323940309 738331322750390374779851)
              ·
                refine ⟨1107496984125585562169777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738331322750390374779851 1107496984125585562169777)
                ·
                  refine ⟨830622738094189171627333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107496984125585562169777 830622738094189171627333)
                  ·
                    refine ⟨155741763392660469680125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830622738094189171627333 155741763392660469680125)
                    ·
                      rfl

theorem cell22_454959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_454959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454959 prefixEnd_454959 := by exact prefixLift 454959
  have htrace : WordTrace (prefixWord ++ tailWord_454959) baseStart_454959 baseEnd_454959 := by
    simpa [prefixWord, tailWord_454959, baseEnd_454959] using wordTrace_append hprefix tailTrace_454959
  have hstable : (prefixWord ++ tailWord_454959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454959).length < 2 ^ (prefixWord ++ tailWord_454959).sum := by decide
  have hdescent : baseEnd_454959 < baseStart_454959 := by decide
  rcases family_descends (prefixWord ++ tailWord_454959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454974 : List Nat := [4, 2, 1, 2, 1, 3, 9]
def baseStart_454974 : Nat := 118140960795 + 454974 * 2 ^ 59
def prefixEnd_454974 : Nat := 4983230072969 + 3 ^ 40 * 454974 * 2
def baseEnd_454974 : Nat := 5768403637007608539077

theorem tailTrace_454974 : CollatzResearch.WordTrace tailWord_454974 prefixEnd_454974 5768403637007608539077 := by
  unfold tailWord_454974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074283131714297027253497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11062843369142917478685317 2074283131714297027253497)
  ·
    refine ⟨1555712348785722770440123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2074283131714297027253497 1555712348785722770440123)
    ·
      refine ⟨2333568523178584155660185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555712348785722770440123 2333568523178584155660185)
      ·
        refine ⟨1750176392383938116745139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2333568523178584155660185 1750176392383938116745139)
        ·
          refine ⟨2625264588575907175117709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750176392383938116745139 2625264588575907175117709)
          ·
            refine ⟨984474220715965190669141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2625264588575907175117709 984474220715965190669141)
            ·
              refine ⟨5768403637007608539077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 984474220715965190669141 5768403637007608539077)
              ·
                rfl

theorem cell22_454974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 9].length) (baseStart_454974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454974 prefixEnd_454974 := by exact prefixLift 454974
  have htrace : WordTrace (prefixWord ++ tailWord_454974) baseStart_454974 baseEnd_454974 := by
    simpa [prefixWord, tailWord_454974, baseEnd_454974] using wordTrace_append hprefix tailTrace_454974
  have hstable : (prefixWord ++ tailWord_454974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454974).length < 2 ^ (prefixWord ++ tailWord_454974).sum := by decide
  have hdescent : baseEnd_454974 < baseStart_454974 := by decide
  rcases family_descends (prefixWord ++ tailWord_454974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454987 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 2, 6]
def baseStart_454987 : Nat := 118140960795 + 454987 * 2 ^ 59
def prefixEnd_454987 : Nat := 4983230072969 + 3 ^ 40 * 454987 * 2
def baseEnd_454987 : Nat := 155751348364877729980039

theorem tailTrace_454987 : CollatzResearch.WordTrace tailWord_454987 prefixEnd_454987 155751348364877729980039 := by
  unfold tailWord_454987
  simp only [CollatzResearch.WordTrace]
  refine ⟨16594739202667279438251215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11063159468444852958834143 16594739202667279438251215)
  ·
    refine ⟨24892108804000919157376823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16594739202667279438251215 24892108804000919157376823)
    ·
      refine ⟨37338163206001378736065235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24892108804000919157376823 37338163206001378736065235)
      ·
        refine ⟨56007244809002068104097853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37338163206001378736065235 56007244809002068104097853)
        ·
          refine ⟨21002716803375775539036695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56007244809002068104097853 21002716803375775539036695)
          ·
            refine ⟨31504075205063663308555043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21002716803375775539036695 31504075205063663308555043)
            ·
              refine ⟨47256112807595494962832565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31504075205063663308555043 47256112807595494962832565)
              ·
                refine ⟨4430260575712077652765553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47256112807595494962832565 4430260575712077652765553)
                ·
                  refine ⟨3322695431784058239574165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430260575712077652765553 3322695431784058239574165)
                  ·
                    refine ⟨155751348364877729980039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3322695431784058239574165 155751348364877729980039)
                    ·
                      rfl

theorem cell22_454987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_454987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_454987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_454987 prefixEnd_454987 := by exact prefixLift 454987
  have htrace : WordTrace (prefixWord ++ tailWord_454987) baseStart_454987 baseEnd_454987 := by
    simpa [prefixWord, tailWord_454987, baseEnd_454987] using wordTrace_append hprefix tailTrace_454987
  have hstable : (prefixWord ++ tailWord_454987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454987).length < 2 ^ (prefixWord ++ tailWord_454987).sum := by decide
  have hdescent : baseEnd_454987 < baseStart_454987 := by decide
  rcases family_descends (prefixWord ++ tailWord_454987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455008 : List Nat := [2, 1, 1, 3, 6, 1, 2, 6]
def baseStart_455008 : Nat := 118140960795 + 455008 * 2 ^ 59
def prefixEnd_455008 : Nat := 4983230072969 + 3 ^ 40 * 455008 * 2
def baseEnd_455008 : Nat := 17306504121560075022775

theorem tailTrace_455008 : CollatzResearch.WordTrace tailWord_455008 prefixEnd_455008 17306504121560075022775 := by
  unfold tailWord_455008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297752567795600012382839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11063670090394133349843785 8297752567795600012382839)
  ·
    refine ⟨12446628851693400018574259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8297752567795600012382839 12446628851693400018574259)
    ·
      refine ⟨18669943277540100027861389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12446628851693400018574259 18669943277540100027861389)
      ·
        refine ⟨7001228729077537510448021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18669943277540100027861389 7001228729077537510448021)
        ·
          refine ⟨328182596675509570802251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7001228729077537510448021 328182596675509570802251)
          ·
            refine ⟨492273895013264356203377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328182596675509570802251 492273895013264356203377)
            ·
              refine ⟨369205421259948267152533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492273895013264356203377 369205421259948267152533)
              ·
                refine ⟨17306504121560075022775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 369205421259948267152533 17306504121560075022775)
                ·
                  rfl

theorem cell22_455008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 6].length) (baseStart_455008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455008 prefixEnd_455008 := by exact prefixLift 455008
  have htrace : WordTrace (prefixWord ++ tailWord_455008) baseStart_455008 baseEnd_455008 := by
    simpa [prefixWord, tailWord_455008, baseEnd_455008] using wordTrace_append hprefix tailTrace_455008
  have hstable : (prefixWord ++ tailWord_455008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455008).length < 2 ^ (prefixWord ++ tailWord_455008).sum := by decide
  have hdescent : baseEnd_455008 < baseStart_455008 := by decide
  rcases family_descends (prefixWord ++ tailWord_455008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455066 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_455066 : Nat := 118140960795 + 455066 * 2 ^ 59
def prefixEnd_455066 : Nat := 4983230072969 + 3 ^ 40 * 455066 * 2
def baseEnd_455066 : Nat := 155778391679347857254797

theorem tailTrace_455066 : CollatzResearch.WordTrace tailWord_455066 prefixEnd_455066 155778391679347857254797 := by
  unfold tailWord_455066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149405142345268982594263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11065080379587383953584701 4149405142345268982594263)
  ·
    refine ⟨6224107713517903473891395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149405142345268982594263 6224107713517903473891395)
    ·
      refine ⟨9336161570276855210837093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6224107713517903473891395 9336161570276855210837093)
      ·
        refine ⟨1750530294426910352031955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9336161570276855210837093 1750530294426910352031955)
        ·
          refine ⟨2625795441640365528047933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750530294426910352031955 2625795441640365528047933)
          ·
            refine ⟨984673290615137073017975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2625795441640365528047933 984673290615137073017975)
            ·
              refine ⟨1477009935922705609526963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984673290615137073017975 1477009935922705609526963)
              ·
                refine ⟨2215514903884058414290445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477009935922705609526963 2215514903884058414290445)
                ·
                  refine ⟨830818088956521905358917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2215514903884058414290445 830818088956521905358917)
                  ·
                    refine ⟨155778391679347857254797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830818088956521905358917 155778391679347857254797)
                    ·
                      rfl

theorem cell22_455066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_455066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455066 prefixEnd_455066 := by exact prefixLift 455066
  have htrace : WordTrace (prefixWord ++ tailWord_455066) baseStart_455066 baseEnd_455066 := by
    simpa [prefixWord, tailWord_455066, baseEnd_455066] using wordTrace_append hprefix tailTrace_455066
  have hstable : (prefixWord ++ tailWord_455066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455066).length < 2 ^ (prefixWord ++ tailWord_455066).sum := by decide
  have hdescent : baseEnd_455066 < baseStart_455066 := by decide
  rcases family_descends (prefixWord ++ tailWord_455066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455188 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 7]
def baseStart_455188 : Nat := 118140960795 + 455188 * 2 ^ 59
def prefixEnd_455188 : Nat := 4983230072969 + 3 ^ 40 * 455188 * 2
def baseEnd_455188 : Nat := 51940051590860068568141

theorem tailTrace_455188 : CollatzResearch.WordTrace tailWord_455188 prefixEnd_455188 51940051590860068568141 := by
  unfold tailWord_455188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301035137469545383159109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11068046849959393844212145 8301035137469545383159109)
  ·
    refine ⟨1556444088275539759342333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8301035137469545383159109 1556444088275539759342333)
    ·
      refine ⟨583666533103327409753375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1556444088275539759342333 583666533103327409753375)
      ·
        refine ⟨875499799654991114630063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583666533103327409753375 875499799654991114630063)
        ·
          refine ⟨1313249699482486671945095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875499799654991114630063 1313249699482486671945095)
          ·
            refine ⟨1969874549223730007917643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313249699482486671945095 1969874549223730007917643)
            ·
              refine ⟨2954811823835595011876465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969874549223730007917643 2954811823835595011876465)
              ·
                refine ⟨2216108867876696258907349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954811823835595011876465 2216108867876696258907349)
                ·
                  refine ⟨51940051590860068568141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2216108867876696258907349 51940051590860068568141)
                  ·
                    rfl

theorem cell22_455188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_455188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455188 prefixEnd_455188 := by exact prefixLift 455188
  have htrace : WordTrace (prefixWord ++ tailWord_455188) baseStart_455188 baseEnd_455188 := by
    simpa [prefixWord, tailWord_455188, baseEnd_455188] using wordTrace_append hprefix tailTrace_455188
  have hstable : (prefixWord ++ tailWord_455188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455188).length < 2 ^ (prefixWord ++ tailWord_455188).sum := by decide
  have hdescent : baseEnd_455188 < baseStart_455188 := by decide
  rcases family_descends (prefixWord ++ tailWord_455188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455192 : List Nat := [2, 1, 2, 3, 3, 3, 1, 3, 1, 3]
def baseStart_455192 : Nat := 118140960795 + 455192 * 2 ^ 59
def prefixEnd_455192 : Nat := 4983230072969 + 3 ^ 40 * 455192 * 2
def baseEnd_455192 : Nat := 155821524054325528604411

theorem tailTrace_455192 : CollatzResearch.WordTrace tailWord_455192 prefixEnd_455192 155821524054325528604411 := by
  unfold tailWord_455192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301108083462299724731915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11068144111283066299642553 8301108083462299724731915)
  ·
    refine ⟨12451662125193449587097873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8301108083462299724731915 12451662125193449587097873)
    ·
      refine ⟨9338746593895087190323405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12451662125193449587097873 9338746593895087190323405)
      ·
        refine ⟨3502029972710657696371277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9338746593895087190323405 3502029972710657696371277)
        ·
          refine ⟨1313261239766496636139229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3502029972710657696371277 1313261239766496636139229)
          ·
            refine ⟨492472964912436238552211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1313261239766496636139229 492472964912436238552211)
            ·
              refine ⟨738709447368654357828317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492472964912436238552211 738709447368654357828317)
              ·
                refine ⟨277016042763245384185619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738709447368654357828317 277016042763245384185619)
                ·
                  refine ⟨415524064144868076278429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277016042763245384185619 415524064144868076278429)
                  ·
                    refine ⟨155821524054325528604411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 415524064144868076278429 155821524054325528604411)
                    ·
                      rfl

theorem cell22_455192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_455192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455192 prefixEnd_455192 := by exact prefixLift 455192
  have htrace : WordTrace (prefixWord ++ tailWord_455192) baseStart_455192 baseEnd_455192 := by
    simpa [prefixWord, tailWord_455192, baseEnd_455192] using wordTrace_append hprefix tailTrace_455192
  have hstable : (prefixWord ++ tailWord_455192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455192).length < 2 ^ (prefixWord ++ tailWord_455192).sum := by decide
  have hdescent : baseEnd_455192 < baseStart_455192 := by decide
  rcases family_descends (prefixWord ++ tailWord_455192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455216 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 6]
def baseStart_455216 : Nat := 118140960795 + 455216 * 2 ^ 59
def prefixEnd_455216 : Nat := 4983230072969 + 3 ^ 40 * 455216 * 2
def baseEnd_455216 : Nat := 51943246581599155334779

theorem tailTrace_455216 : CollatzResearch.WordTrace tailWord_455216 prefixEnd_455216 51943246581599155334779 := by
  unfold tailWord_455216
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301545759418825774168751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11068727679225101032225001 8301545759418825774168751)
  ·
    refine ⟨12452318639128238661253127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8301545759418825774168751 12452318639128238661253127)
    ·
      refine ⟨18678477958692357991879691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12452318639128238661253127 18678477958692357991879691)
      ·
        refine ⟨28017716938038536987819537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18678477958692357991879691 28017716938038536987819537)
        ·
          refine ⟨21013287703528902740864653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28017716938038536987819537 21013287703528902740864653)
          ·
            refine ⟨7879982888823338527824245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21013287703528902740864653 7879982888823338527824245)
            ·
              refine ⟨738748395827187986983523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7879982888823338527824245 738748395827187986983523)
              ·
                refine ⟨1108122593740781980475285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738748395827187986983523 1108122593740781980475285)
                ·
                  refine ⟨51943246581599155334779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1108122593740781980475285 51943246581599155334779)
                  ·
                    rfl

theorem cell22_455216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_455216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455216 prefixEnd_455216 := by exact prefixLift 455216
  have htrace : WordTrace (prefixWord ++ tailWord_455216) baseStart_455216 baseEnd_455216 := by
    simpa [prefixWord, tailWord_455216, baseEnd_455216] using wordTrace_append hprefix tailTrace_455216
  have hstable : (prefixWord ++ tailWord_455216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455216).length < 2 ^ (prefixWord ++ tailWord_455216).sum := by decide
  have hdescent : baseEnd_455216 < baseStart_455216 := by decide
  rcases family_descends (prefixWord ++ tailWord_455216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455222 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_455222 : Nat := 118140960795 + 455222 * 2 ^ 59
def prefixEnd_455222 : Nat := 4983230072969 + 3 ^ 40 * 455222 * 2
def baseEnd_455222 : Nat := 51943931222471816784773

theorem tailTrace_455222 : CollatzResearch.WordTrace tailWord_455222 prefixEnd_455222 51943931222471816784773 := by
  unfold tailWord_455222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037706897300994660815995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11068873571210609715370613 1037706897300994660815995)
  ·
    refine ⟨1556560345951491991223993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1037706897300994660815995 1556560345951491991223993)
    ·
      refine ⟨1167420259463618993417995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1556560345951491991223993 1167420259463618993417995)
      ·
        refine ⟨1751130389195428490126993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167420259463618993417995 1751130389195428490126993)
        ·
          refine ⟨1313347791896571367595245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1751130389195428490126993 1313347791896571367595245)
          ·
            refine ⟨492505421961214262848217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1313347791896571367595245 492505421961214262848217)
            ·
              refine ⟨369379066470910697136163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492505421961214262848217 369379066470910697136163)
              ·
                refine ⟨554068599706366045704245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369379066470910697136163 554068599706366045704245)
                ·
                  refine ⟨51943931222471816784773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554068599706366045704245 51943931222471816784773)
                  ·
                    rfl

theorem cell22_455222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_455222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455222 prefixEnd_455222 := by exact prefixLift 455222
  have htrace : WordTrace (prefixWord ++ tailWord_455222) baseStart_455222 baseEnd_455222 := by
    simpa [prefixWord, tailWord_455222, baseEnd_455222] using wordTrace_append hprefix tailTrace_455222
  have hstable : (prefixWord ++ tailWord_455222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455222).length < 2 ^ (prefixWord ++ tailWord_455222).sum := by decide
  have hdescent : baseEnd_455222 < baseStart_455222 := by decide
  rcases family_descends (prefixWord ++ tailWord_455222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455231 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 1, 5]
def baseStart_455231 : Nat := 118140960795 + 455231 * 2 ^ 59
def prefixEnd_455231 : Nat := 4983230072969 + 3 ^ 40 * 455231 * 2
def baseEnd_455231 : Nat := 155834874551342426879291

theorem tailTrace_455231 : CollatzResearch.WordTrace tailWord_455231 prefixEnd_455231 155834874551342426879291 := by
  unfold tailWord_455231
  simp only [CollatzResearch.WordTrace]
  refine ⟨16603638613783309110133547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11069092409188872740089031 16603638613783309110133547)
  ·
    refine ⟨24905457920674963665200321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16603638613783309110133547 24905457920674963665200321)
    ·
      refine ⟨18679093440506222748900241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24905457920674963665200321 18679093440506222748900241)
      ·
        refine ⟨14009320080379667061675181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18679093440506222748900241 14009320080379667061675181)
        ·
          refine ⟨5253495030142375148128193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14009320080379667061675181 5253495030142375148128193)
          ·
            refine ⟨3940121272606781361096145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5253495030142375148128193 3940121272606781361096145)
            ·
              refine ⟨2955090954455086020822109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940121272606781361096145 2955090954455086020822109)
              ·
                refine ⟨1108159107920657257808291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2955090954455086020822109 1108159107920657257808291)
                ·
                  refine ⟨1662238661880985886712437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108159107920657257808291 1662238661880985886712437)
                  ·
                    refine ⟨155834874551342426879291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1662238661880985886712437 155834874551342426879291)
                    ·
                      rfl

theorem cell22_455231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_455231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455231 prefixEnd_455231 := by exact prefixLift 455231
  have htrace : WordTrace (prefixWord ++ tailWord_455231) baseStart_455231 baseEnd_455231 := by
    simpa [prefixWord, tailWord_455231, baseEnd_455231] using wordTrace_append hprefix tailTrace_455231
  have hstable : (prefixWord ++ tailWord_455231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455231).length < 2 ^ (prefixWord ++ tailWord_455231).sum := by decide
  have hdescent : baseEnd_455231 < baseStart_455231 := by decide
  rcases family_descends (prefixWord ++ tailWord_455231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455246 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_455246 : Nat := 118140960795 + 455246 * 2 ^ 59
def prefixEnd_455246 : Nat := 4983230072969 + 3 ^ 40 * 455246 * 2
def baseEnd_455246 : Nat := 155840009357887387754245

theorem tailTrace_455246 : CollatzResearch.WordTrace tailWord_455246 prefixEnd_455246 155840009357887387754245 := by
  unfold tailWord_455246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075523213591120833991199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11069457139152644447953061 2075523213591120833991199)
  ·
    refine ⟨3113284820386681250986799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2075523213591120833991199 3113284820386681250986799)
    ·
      refine ⟨4669927230580021876480199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3113284820386681250986799 4669927230580021876480199)
      ·
        refine ⟨7004890845870032814720299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669927230580021876480199 7004890845870032814720299)
        ·
          refine ⟨10507336268805049222080449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004890845870032814720299 10507336268805049222080449)
          ·
            refine ⟨7880502201603786916560337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10507336268805049222080449 7880502201603786916560337)
            ·
              refine ⟨5910376651202840187420253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7880502201603786916560337 5910376651202840187420253)
              ·
                refine ⟨2216391244201065070282595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5910376651202840187420253 2216391244201065070282595)
                ·
                  refine ⟨3324586866301597605423893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216391244201065070282595 3324586866301597605423893)
                  ·
                    refine ⟨155840009357887387754245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3324586866301597605423893 155840009357887387754245)
                    ·
                      rfl

theorem cell22_455246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_455246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455246 prefixEnd_455246 := by exact prefixLift 455246
  have htrace : WordTrace (prefixWord ++ tailWord_455246) baseStart_455246 baseEnd_455246 := by
    simpa [prefixWord, tailWord_455246, baseEnd_455246] using wordTrace_append hprefix tailTrace_455246
  have hstable : (prefixWord ++ tailWord_455246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455246).length < 2 ^ (prefixWord ++ tailWord_455246).sum := by decide
  have hdescent : baseEnd_455246 < baseStart_455246 := by decide
  rcases family_descends (prefixWord ++ tailWord_455246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455261 : List Nat := [1, 4, 4, 13]
def baseStart_455261 : Nat := 118140960795 + 455261 * 2 ^ 59
def prefixEnd_455261 : Nat := 4983230072969 + 3 ^ 40 * 455261 * 2
def baseEnd_455261 : Nat := 213779347276313235431

theorem tailTrace_455261 : CollatzResearch.WordTrace tailWord_455261 prefixEnd_455261 213779347276313235431 := by
  unfold tailWord_455261
  simp only [CollatzResearch.WordTrace]
  refine ⟨16604732803674624233725637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11069821869116416155817091 16604732803674624233725637)
  ·
    refine ⟨3113387400688992043823557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16604732803674624233725637 3113387400688992043823557)
    ·
      refine ⟨583760137629186008216917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3113387400688992043823557 583760137629186008216917)
      ·
        refine ⟨213779347276313235431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 583760137629186008216917 213779347276313235431)
        ·
          rfl

theorem cell22_455261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 13].length) (baseStart_455261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455261 prefixEnd_455261 := by exact prefixLift 455261
  have htrace : WordTrace (prefixWord ++ tailWord_455261) baseStart_455261 baseEnd_455261 := by
    simpa [prefixWord, tailWord_455261, baseEnd_455261] using wordTrace_append hprefix tailTrace_455261
  have hstable : (prefixWord ++ tailWord_455261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455261).length < 2 ^ (prefixWord ++ tailWord_455261).sum := by decide
  have hdescent : baseEnd_455261 < baseStart_455261 := by decide
  rcases family_descends (prefixWord ++ tailWord_455261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455265 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 2, 3]
def baseStart_455265 : Nat := 118140960795 + 455265 * 2 ^ 59
def prefixEnd_455265 : Nat := 4983230072969 + 3 ^ 40 * 455265 * 2
def baseEnd_455265 : Nat := 155846513446177671529187

theorem tailTrace_455265 : CollatzResearch.WordTrace tailWord_455265 prefixEnd_455265 155846513446177671529187 := by
  unfold tailWord_455265
  simp only [CollatzResearch.WordTrace]
  refine ⟨16604878695660132916871249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11069919130440088611247499 16604878695660132916871249)
  ·
    refine ⟨12453659021745099687653437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16604878695660132916871249 12453659021745099687653437)
    ·
      refine ⟨4670122133154412382870039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12453659021745099687653437 4670122133154412382870039)
      ·
        refine ⟨7005183199731618574305059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4670122133154412382870039 7005183199731618574305059)
        ·
          refine ⟨10507774799597427861457589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005183199731618574305059 10507774799597427861457589)
          ·
            refine ⟨985103887462258862011649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10507774799597427861457589 985103887462258862011649)
            ·
              refine ⟨738827915596694146508737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985103887462258862011649 738827915596694146508737)
              ·
                refine ⟨554120936697520609881553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738827915596694146508737 554120936697520609881553)
                ·
                  refine ⟨415590702523140457411165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554120936697520609881553 415590702523140457411165)
                  ·
                    refine ⟨155846513446177671529187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 415590702523140457411165 155846513446177671529187)
                    ·
                      rfl

theorem cell22_455265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_455265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455265 prefixEnd_455265 := by exact prefixLift 455265
  have htrace : WordTrace (prefixWord ++ tailWord_455265) baseStart_455265 baseEnd_455265 := by
    simpa [prefixWord, tailWord_455265, baseEnd_455265] using wordTrace_append hprefix tailTrace_455265
  have hstable : (prefixWord ++ tailWord_455265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455265).length < 2 ^ (prefixWord ++ tailWord_455265).sum := by decide
  have hdescent : baseEnd_455265 < baseStart_455265 := by decide
  rcases family_descends (prefixWord ++ tailWord_455265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455278 : List Nat := [4, 1, 2, 2, 2, 1, 3, 7]
def baseStart_455278 : Nat := 118140960795 + 455278 * 2 ^ 59
def prefixEnd_455278 : Nat := 4983230072969 + 3 ^ 40 * 455278 * 2
def baseEnd_455278 : Nat := 17316773734649996772683

theorem tailTrace_455278 : CollatzResearch.WordTrace tailWord_455278 prefixEnd_455278 17316773734649996772683 := by
  unfold tailWord_455278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075669105576629517136811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11070235229742024091396325 2075669105576629517136811)
  ·
    refine ⟨3113503658364944275705217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2075669105576629517136811 3113503658364944275705217)
    ·
      refine ⟨2335127743773708206778913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3113503658364944275705217 2335127743773708206778913)
      ·
        refine ⟨1751345807830281155084185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2335127743773708206778913 1751345807830281155084185)
        ·
          refine ⟨1313509355872710866313139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1751345807830281155084185 1313509355872710866313139)
          ·
            refine ⟨1970264033809066299469709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313509355872710866313139 1970264033809066299469709)
            ·
              refine ⟨738849012678399862301141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1970264033809066299469709 738849012678399862301141)
              ·
                refine ⟨17316773734649996772683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 738849012678399862301141 17316773734649996772683)
                ·
                  rfl

theorem cell22_455278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_455278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455278 prefixEnd_455278 := by exact prefixLift 455278
  have htrace : WordTrace (prefixWord ++ tailWord_455278) baseStart_455278 baseEnd_455278 := by
    simpa [prefixWord, tailWord_455278, baseEnd_455278] using wordTrace_append hprefix tailTrace_455278
  have hstable : (prefixWord ++ tailWord_455278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455278).length < 2 ^ (prefixWord ++ tailWord_455278).sum := by decide
  have hdescent : baseEnd_455278 < baseStart_455278 := by decide
  rcases family_descends (prefixWord ++ tailWord_455278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455321 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_455321 : Nat := 118140960795 + 455321 * 2 ^ 59
def prefixEnd_455321 : Nat := 4983230072969 + 3 ^ 40 * 455321 * 2
def baseEnd_455321 : Nat := 155865683390612192129015

theorem tailTrace_455321 : CollatzResearch.WordTrace tailWord_455321 prefixEnd_455321 155865683390612192129015 := by
  unfold tailWord_455321
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606921183457254480909817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11071280788971502987273211 16606921183457254480909817)
  ·
    refine ⟨12455190887592940860682363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16606921183457254480909817 12455190887592940860682363)
    ·
      refine ⟨18682786331389411291023545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12455190887592940860682363 18682786331389411291023545)
      ·
        refine ⟨14012089748542058468267659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18682786331389411291023545 14012089748542058468267659)
        ·
          refine ⟨21018134622813087702401489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14012089748542058468267659 21018134622813087702401489)
          ·
            refine ⟨15763600967109815776801117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21018134622813087702401489 15763600967109815776801117)
            ·
              refine ⟨5911350362666180916300419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15763600967109815776801117 5911350362666180916300419)
              ·
                refine ⟨8867025543999271374450629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911350362666180916300419 8867025543999271374450629)
                ·
                  refine ⟨1662567289499863382709493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8867025543999271374450629 1662567289499863382709493)
                  ·
                    refine ⟨155865683390612192129015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1662567289499863382709493 155865683390612192129015)
                    ·
                      rfl

theorem cell22_455321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_455321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455321 prefixEnd_455321 := by exact prefixLift 455321
  have htrace : WordTrace (prefixWord ++ tailWord_455321) baseStart_455321 baseEnd_455321 := by
    simpa [prefixWord, tailWord_455321, baseEnd_455321] using wordTrace_append hprefix tailTrace_455321
  have hstable : (prefixWord ++ tailWord_455321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455321).length < 2 ^ (prefixWord ++ tailWord_455321).sum := by decide
  have hdescent : baseEnd_455321 < baseStart_455321 := by decide
  rcases family_descends (prefixWord ++ tailWord_455321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455370 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_455370 : Nat := 118140960795 + 455370 * 2 ^ 59
def prefixEnd_455370 : Nat := 4983230072969 + 3 ^ 40 * 455370 * 2
def baseEnd_455370 : Nat := 155882457091992397653865

theorem tailTrace_455370 : CollatzResearch.WordTrace tailWord_455370 prefixEnd_455370 155882457091992397653865 := by
  unfold tailWord_455370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152177090069933962360891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11072472240186490566295709 4152177090069933962360891)
  ·
    refine ⟨6228265635104900943541337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4152177090069933962360891 6228265635104900943541337)
    ·
      refine ⟨4671199226328675707656003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6228265635104900943541337 4671199226328675707656003)
      ·
        refine ⟨7006798839493013561484005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671199226328675707656003 7006798839493013561484005)
        ·
          refine ⟨1313774782404940042778251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7006798839493013561484005 1313774782404940042778251)
          ·
            refine ⟨1970662173607410064167377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313774782404940042778251 1970662173607410064167377)
            ·
              refine ⟨1477996630205557548125533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970662173607410064167377 1477996630205557548125533)
              ·
                refine ⟨554248736327084080547075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1477996630205557548125533 554248736327084080547075)
                ·
                  refine ⟨831373104490626120820613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554248736327084080547075 831373104490626120820613)
                  ·
                    refine ⟨155882457091992397653865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 831373104490626120820613 155882457091992397653865)
                    ·
                      rfl

theorem cell22_455370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_455370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455370 prefixEnd_455370 := by exact prefixLift 455370
  have htrace : WordTrace (prefixWord ++ tailWord_455370) baseStart_455370 baseEnd_455370 := by
    simpa [prefixWord, tailWord_455370, baseEnd_455370] using wordTrace_append hprefix tailTrace_455370
  have hstable : (prefixWord ++ tailWord_455370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455370).length < 2 ^ (prefixWord ++ tailWord_455370).sum := by decide
  have hdescent : baseEnd_455370 < baseStart_455370 := by decide
  rcases family_descends (prefixWord ++ tailWord_455370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455445 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_455445 : Nat := 118140960795 + 455445 * 2 ^ 59
def prefixEnd_455445 : Nat := 4983230072969 + 3 ^ 40 * 455445 * 2
def baseEnd_455445 : Nat := 155908131124717202028635

theorem tailTrace_455445 : CollatzResearch.WordTrace tailWord_455445 prefixEnd_455445 155908131124717202028635 := by
  unfold tailWord_455445
  simp only [CollatzResearch.WordTrace]
  refine ⟨16611443835008023658423789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11074295890005349105615859 16611443835008023658423789)
  ·
    refine ⟨6229291438128008871908921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16611443835008023658423789 6229291438128008871908921)
    ·
      refine ⟨4671968578596006653931691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6229291438128008871908921 4671968578596006653931691)
      ·
        refine ⟨7007952867894009980897537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671968578596006653931691 7007952867894009980897537)
        ·
          refine ⟨5255964650920507485673153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7007952867894009980897537 5255964650920507485673153)
          ·
            refine ⟨3941973488190380614254865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255964650920507485673153 3941973488190380614254865)
            ·
              refine ⟨2956480116142785460691149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941973488190380614254865 2956480116142785460691149)
              ·
                refine ⟨1108680043553544547759181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2956480116142785460691149 1108680043553544547759181)
                ·
                  refine ⟨415755016332579205409693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108680043553544547759181 415755016332579205409693)
                  ·
                    refine ⟨155908131124717202028635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 415755016332579205409693 155908131124717202028635)
                    ·
                      rfl

theorem cell22_455445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_455445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455445 prefixEnd_455445 := by exact prefixLift 455445
  have htrace : WordTrace (prefixWord ++ tailWord_455445) baseStart_455445 baseEnd_455445 := by
    simpa [prefixWord, tailWord_455445, baseEnd_455445] using wordTrace_append hprefix tailTrace_455445
  have hstable : (prefixWord ++ tailWord_455445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455445).length < 2 ^ (prefixWord ++ tailWord_455445).sum := by decide
  have hdescent : baseEnd_455445 < baseStart_455445 := by decide
  rcases family_descends (prefixWord ++ tailWord_455445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455447 : List Nat := [1, 1, 3, 4, 4, 1, 1, 7]
def baseStart_455447 : Nat := 118140960795 + 455447 * 2 ^ 59
def prefixEnd_455447 : Nat := 4983230072969 + 3 ^ 40 * 455447 * 2
def baseEnd_455447 : Nat := 17323201751732207053181

theorem tailTrace_455447 : CollatzResearch.WordTrace tailWord_455447 prefixEnd_455447 17323201751732207053181 := by
  unfold tailWord_455447
  simp only [CollatzResearch.WordTrace]
  refine ⟨16611516781000777999996595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11074344520667185333331063 16611516781000777999996595)
  ·
    refine ⟨24917275171501166999994893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16611516781000777999996595 24917275171501166999994893)
    ·
      refine ⟨9343978189312937624998085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24917275171501166999994893 9343978189312937624998085)
      ·
        refine ⟨1751995910496175804687141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9343978189312937624998085 1751995910496175804687141)
        ·
          refine ⟨328499233218032963378839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1751995910496175804687141 328499233218032963378839)
          ·
            refine ⟨492748849827049445068259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328499233218032963378839 492748849827049445068259)
            ·
              refine ⟨739123274740574167602389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492748849827049445068259 739123274740574167602389)
              ·
                refine ⟨17323201751732207053181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 739123274740574167602389 17323201751732207053181)
                ·
                  rfl

theorem cell22_455447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 7].length) (baseStart_455447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455447 prefixEnd_455447 := by exact prefixLift 455447
  have htrace : WordTrace (prefixWord ++ tailWord_455447) baseStart_455447 baseEnd_455447 := by
    simpa [prefixWord, tailWord_455447, baseEnd_455447] using wordTrace_append hprefix tailTrace_455447
  have hstable : (prefixWord ++ tailWord_455447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455447).length < 2 ^ (prefixWord ++ tailWord_455447).sum := by decide
  have hdescent : baseEnd_455447 < baseStart_455447 := by decide
  rcases family_descends (prefixWord ++ tailWord_455447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455466 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_455466 : Nat := 118140960795 + 455466 * 2 ^ 59
def prefixEnd_455466 : Nat := 4983230072969 + 3 ^ 40 * 455466 * 2
def baseEnd_455466 : Nat := 155915319853880147253571

theorem tailTrace_455466 : CollatzResearch.WordTrace tailWord_455466 prefixEnd_455466 155915319853880147253571 := by
  unfold tailWord_455466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153052441982986061234563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11074806511954629496625501 4153052441982986061234563)
  ·
    refine ⟨6229578662974479091851845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4153052441982986061234563 6229578662974479091851845)
    ·
      refine ⟨1168045999307714829722221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6229578662974479091851845 1168045999307714829722221)
      ·
        refine ⟨438017249740393061145833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1168045999307714829722221 438017249740393061145833)
        ·
          refine ⟨328512937305294795859375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438017249740393061145833 328512937305294795859375)
          ·
            refine ⟨492769405957942193789063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328512937305294795859375 492769405957942193789063)
            ·
              refine ⟨739154108936913290683595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492769405957942193789063 739154108936913290683595)
              ·
                refine ⟨1108731163405369936025393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739154108936913290683595 1108731163405369936025393)
                ·
                  refine ⟨831548372554027452019045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108731163405369936025393 831548372554027452019045)
                  ·
                    refine ⟨155915319853880147253571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 831548372554027452019045 155915319853880147253571)
                    ·
                      rfl

theorem cell22_455466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_455466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455466 prefixEnd_455466 := by exact prefixLift 455466
  have htrace : WordTrace (prefixWord ++ tailWord_455466) baseStart_455466 baseEnd_455466 := by
    simpa [prefixWord, tailWord_455466, baseEnd_455466] using wordTrace_append hprefix tailTrace_455466
  have hstable : (prefixWord ++ tailWord_455466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455466).length < 2 ^ (prefixWord ++ tailWord_455466).sum := by decide
  have hdescent : baseEnd_455466 < baseStart_455466 := by decide
  rcases family_descends (prefixWord ++ tailWord_455466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455473 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_455473 : Nat := 118140960795 + 455473 * 2 ^ 59
def prefixEnd_455473 : Nat := 4983230072969 + 3 ^ 40 * 455473 * 2
def baseEnd_455473 : Nat := 155917716096934462328549

theorem tailTrace_455473 : CollatzResearch.WordTrace tailWord_455473 prefixEnd_455473 155917716096934462328549 := by
  unfold tailWord_455473
  simp only [CollatzResearch.WordTrace]
  refine ⟨16612465078906584440443073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11074976719271056293628715 16612465078906584440443073)
  ·
    refine ⟨12459348809179938330332305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16612465078906584440443073 12459348809179938330332305)
    ·
      refine ⟨9344511606884953747749229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12459348809179938330332305 9344511606884953747749229)
      ·
        refine ⟨3504191852581857655405961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9344511606884953747749229 3504191852581857655405961)
        ·
          refine ⟨2628143889436393241554471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3504191852581857655405961 2628143889436393241554471)
          ·
            refine ⟨3942215834154589862331707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628143889436393241554471 3942215834154589862331707)
            ·
              refine ⟨5913323751231884793497561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942215834154589862331707 5913323751231884793497561)
              ·
                refine ⟨4434992813423913595123171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5913323751231884793497561 4434992813423913595123171)
                ·
                  refine ⟨6652489220135870392684757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434992813423913595123171 6652489220135870392684757)
                  ·
                    refine ⟨155917716096934462328549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6652489220135870392684757 155917716096934462328549)
                    ·
                      rfl

theorem cell22_455473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_455473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455473 prefixEnd_455473 := by exact prefixLift 455473
  have htrace : WordTrace (prefixWord ++ tailWord_455473) baseStart_455473 baseEnd_455473 := by
    simpa [prefixWord, tailWord_455473, baseEnd_455473] using wordTrace_append hprefix tailTrace_455473
  have hstable : (prefixWord ++ tailWord_455473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455473).length < 2 ^ (prefixWord ++ tailWord_455473).sum := by decide
  have hdescent : baseEnd_455473 < baseStart_455473 := by decide
  rcases family_descends (prefixWord ++ tailWord_455473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455537 : List Nat := [1, 2, 2, 2, 1, 4, 3, 3, 4]
def baseStart_455537 : Nat := 118140960795 + 455537 * 2 ^ 59
def prefixEnd_455537 : Nat := 4983230072969 + 3 ^ 40 * 455537 * 2
def baseEnd_455537 : Nat := 51979874868286542909451

theorem tailTrace_455537 : CollatzResearch.WordTrace tailWord_455537 prefixEnd_455537 51979874868286542909451 := by
  unfold tailWord_455537
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614799350674723370772865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11076532900449815580515243 16614799350674723370772865)
  ·
    refine ⟨12461099513006042528079649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16614799350674723370772865 12461099513006042528079649)
    ·
      refine ⟨9345824634754531896059737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12461099513006042528079649 9345824634754531896059737)
      ·
        refine ⟨7009368476065898922044803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9345824634754531896059737 7009368476065898922044803)
        ·
          refine ⟨10514052714098848383067205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7009368476065898922044803 10514052714098848383067205)
          ·
            refine ⟨1971384883893534071825101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10514052714098848383067205 1971384883893534071825101)
            ·
              refine ⟨739269331460075276934413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1971384883893534071825101 739269331460075276934413)
              ·
                refine ⟨277225999297528228850405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739269331460075276934413 277225999297528228850405)
                ·
                  refine ⟨51979874868286542909451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277225999297528228850405 51979874868286542909451)
                  ·
                    rfl

theorem cell22_455537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_455537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455537 prefixEnd_455537 := by exact prefixLift 455537
  have htrace : WordTrace (prefixWord ++ tailWord_455537) baseStart_455537 baseEnd_455537 := by
    simpa [prefixWord, tailWord_455537, baseEnd_455537] using wordTrace_append hprefix tailTrace_455537
  have hstable : (prefixWord ++ tailWord_455537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455537).length < 2 ^ (prefixWord ++ tailWord_455537).sum := by decide
  have hdescent : baseEnd_455537 < baseStart_455537 := by decide
  rcases family_descends (prefixWord ++ tailWord_455537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455685 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_455685 : Nat := 118140960795 + 455685 * 2 ^ 59
def prefixEnd_455685 : Nat := 4983230072969 + 3 ^ 40 * 455685 * 2
def baseEnd_455685 : Nat := 155990288029436576027899

theorem tailTrace_455685 : CollatzResearch.WordTrace tailWord_455685 prefixEnd_455685 155990288029436576027899 := by
  unfold tailWord_455685
  simp only [CollatzResearch.WordTrace]
  refine ⟨16620197354138544647160509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11080131569425696431440339 16620197354138544647160509)
  ·
    refine ⟨6232574007801954242685191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16620197354138544647160509 6232574007801954242685191)
    ·
      refine ⟨9348861011702931364027787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6232574007801954242685191 9348861011702931364027787)
      ·
        refine ⟨14023291517554397046041681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9348861011702931364027787 14023291517554397046041681)
        ·
          refine ⟨10517468638165797784531261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14023291517554397046041681 10517468638165797784531261)
          ·
            refine ⟨3944050739312174169199223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10517468638165797784531261 3944050739312174169199223)
            ·
              refine ⟨5916076108968261253798835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944050739312174169199223 5916076108968261253798835)
              ·
                refine ⟨8874114163452391880698253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916076108968261253798835 8874114163452391880698253)
                ·
                  refine ⟨3327792811294646955261845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8874114163452391880698253 3327792811294646955261845)
                  ·
                    refine ⟨155990288029436576027899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3327792811294646955261845 155990288029436576027899)
                    ·
                      rfl

theorem cell22_455685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_455685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455685 prefixEnd_455685 := by exact prefixLift 455685
  have htrace : WordTrace (prefixWord ++ tailWord_455685) baseStart_455685 baseEnd_455685 := by
    simpa [prefixWord, tailWord_455685, baseEnd_455685] using wordTrace_append hprefix tailTrace_455685
  have hstable : (prefixWord ++ tailWord_455685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455685).length < 2 ^ (prefixWord ++ tailWord_455685).sum := by decide
  have hdescent : baseEnd_455685 < baseStart_455685 := by decide
  rcases family_descends (prefixWord ++ tailWord_455685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455719 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 4, 4]
def baseStart_455719 : Nat := 118140960795 + 455719 * 2 ^ 59
def prefixEnd_455719 : Nat := 4983230072969 + 3 ^ 40 * 455719 * 2
def baseEnd_455719 : Nat := 156001926924271820677795

theorem tailTrace_455719 : CollatzResearch.WordTrace tailWord_455719 prefixEnd_455719 156001926924271820677795 := by
  unfold tailWord_455719
  simp only [CollatzResearch.WordTrace]
  refine ⟨16621437436015368453898211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11080958290676912302598807 16621437436015368453898211)
  ·
    refine ⟨24932156154023052680847317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16621437436015368453898211 24932156154023052680847317)
    ·
      refine ⟨584347409859915297207359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24932156154023052680847317 584347409859915297207359)
      ·
        refine ⟨876521114789872945811039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584347409859915297207359 876521114789872945811039)
        ·
          refine ⟨1314781672184809418716559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876521114789872945811039 1314781672184809418716559)
          ·
            refine ⟨1972172508277214128074839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314781672184809418716559 1972172508277214128074839)
            ·
              refine ⟨2958258762415821192112259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972172508277214128074839 2958258762415821192112259)
              ·
                refine ⟨4437388143623731788168389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958258762415821192112259 4437388143623731788168389)
                ·
                  refine ⟨832010276929449710281573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4437388143623731788168389 832010276929449710281573)
                  ·
                    refine ⟨156001926924271820677795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832010276929449710281573 156001926924271820677795)
                    ·
                      rfl

theorem cell22_455719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_455719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455719 prefixEnd_455719 := by exact prefixLift 455719
  have htrace : WordTrace (prefixWord ++ tailWord_455719) baseStart_455719 baseEnd_455719 := by
    simpa [prefixWord, tailWord_455719, baseEnd_455719] using wordTrace_append hprefix tailTrace_455719
  have hstable : (prefixWord ++ tailWord_455719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455719).length < 2 ^ (prefixWord ++ tailWord_455719).sum := by decide
  have hdescent : baseEnd_455719 < baseStart_455719 := by decide
  rcases family_descends (prefixWord ++ tailWord_455719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455734 : List Nat := [5, 1, 2, 1, 1, 3, 2, 7]
def baseStart_455734 : Nat := 118140960795 + 455734 * 2 ^ 59
def prefixEnd_455734 : Nat := 4983230072969 + 3 ^ 40 * 455734 * 2
def baseEnd_455734 : Nat := 17334117970090753505861

theorem tailTrace_455734 : CollatzResearch.WordTrace tailWord_455734 prefixEnd_455734 17334117970090753505861 := by
  unfold tailWord_455734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038874033185064125980891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11081323020640684010462837 1038874033185064125980891)
  ·
    refine ⟨1558311049777596188971337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1038874033185064125980891 1558311049777596188971337)
    ·
      refine ⟨1168733287333197141728503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1558311049777596188971337 1168733287333197141728503)
      ·
        refine ⟨1753099930999795712592755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168733287333197141728503 1753099930999795712592755)
        ·
          refine ⟨2629649896499693568889133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753099930999795712592755 2629649896499693568889133)
          ·
            refine ⟨986118711187385088333425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2629649896499693568889133 986118711187385088333425)
            ·
              refine ⟨739589033390538816250069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986118711187385088333425 739589033390538816250069)
              ·
                refine ⟨17334117970090753505861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 739589033390538816250069 17334117970090753505861)
                ·
                  rfl

theorem cell22_455734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_455734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455734 prefixEnd_455734 := by exact prefixLift 455734
  have htrace : WordTrace (prefixWord ++ tailWord_455734) baseStart_455734 baseEnd_455734 := by
    simpa [prefixWord, tailWord_455734, baseEnd_455734] using wordTrace_append hprefix tailTrace_455734
  have hstable : (prefixWord ++ tailWord_455734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455734).length < 2 ^ (prefixWord ++ tailWord_455734).sum := by decide
  have hdescent : baseEnd_455734 < baseStart_455734 := by decide
  rcases family_descends (prefixWord ++ tailWord_455734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455783 : List Nat := [1, 1, 5, 1, 1, 3, 4, 2, 1, 3]
def baseStart_455783 : Nat := 118140960795 + 455783 * 2 ^ 59
def prefixEnd_455783 : Nat := 4983230072969 + 3 ^ 40 * 455783 * 2
def baseEnd_455783 : Nat := 156023835432196987077599

theorem tailTrace_455783 : CollatzResearch.WordTrace tailWord_455783 prefixEnd_455783 156023835432196987077599 := by
  unfold tailWord_455783
  simp only [CollatzResearch.WordTrace]
  refine ⟨16623771707783507384228003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11082514471855671589485335 16623771707783507384228003)
  ·
    refine ⟨24935657561675261076342005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16623771707783507384228003 24935657561675261076342005)
    ·
      refine ⟨2337717896407055725907063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24935657561675261076342005 2337717896407055725907063)
      ·
        refine ⟨3506576844610583588860595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337717896407055725907063 3506576844610583588860595)
        ·
          refine ⟨5259865266915875383290893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506576844610583588860595 5259865266915875383290893)
          ·
            refine ⟨1972449475093453268734085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5259865266915875383290893 1972449475093453268734085)
            ·
              refine ⟨369834276580022487887641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1972449475093453268734085 369834276580022487887641)
              ·
                refine ⟨277375707435016865915731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369834276580022487887641 277375707435016865915731)
                ·
                  refine ⟨416063561152525298873597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277375707435016865915731 416063561152525298873597)
                  ·
                    refine ⟨156023835432196987077599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416063561152525298873597 156023835432196987077599)
                    ·
                      rfl

theorem cell22_455783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_455783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455783 prefixEnd_455783 := by exact prefixLift 455783
  have htrace : WordTrace (prefixWord ++ tailWord_455783) baseStart_455783 baseEnd_455783 := by
    simpa [prefixWord, tailWord_455783, baseEnd_455783] using wordTrace_append hprefix tailTrace_455783
  have hstable : (prefixWord ++ tailWord_455783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455783).length < 2 ^ (prefixWord ++ tailWord_455783).sum := by decide
  have hdescent : baseEnd_455783 < baseStart_455783 := by decide
  rcases family_descends (prefixWord ++ tailWord_455783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455792 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_455792 : Nat := 118140960795 + 455792 * 2 ^ 59
def prefixEnd_455792 : Nat := 4983230072969 + 3 ^ 40 * 455792 * 2
def baseEnd_455792 : Nat := 156026916316123963602571

theorem tailTrace_455792 : CollatzResearch.WordTrace tailWord_455792 prefixEnd_455792 156026916316123963602571 := by
  unfold tailWord_455792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312049982375450960652815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11082733309833934614203753 8312049982375450960652815)
  ·
    refine ⟨12468074973563176440979223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312049982375450960652815 12468074973563176440979223)
    ·
      refine ⟨18702112460344764661468835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12468074973563176440979223 18702112460344764661468835)
      ·
        refine ⟨28053168690517146992203253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18702112460344764661468835 28053168690517146992203253)
        ·
          refine ⟨2629984564735982530519055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28053168690517146992203253 2629984564735982530519055)
          ·
            refine ⟨3944976847103973795778583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629984564735982530519055 3944976847103973795778583)
            ·
              refine ⟨5917465270655960693667875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944976847103973795778583 5917465270655960693667875)
              ·
                refine ⟨8876197905983941040501813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917465270655960693667875 8876197905983941040501813)
                ·
                  refine ⟨832143553685994472547045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8876197905983941040501813 832143553685994472547045)
                  ·
                    refine ⟨156026916316123963602571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832143553685994472547045 156026916316123963602571)
                    ·
                      rfl

theorem cell22_455792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_455792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455792 prefixEnd_455792 := by exact prefixLift 455792
  have htrace : WordTrace (prefixWord ++ tailWord_455792) baseStart_455792 baseEnd_455792 := by
    simpa [prefixWord, tailWord_455792, baseEnd_455792] using wordTrace_append hprefix tailTrace_455792
  have hstable : (prefixWord ++ tailWord_455792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455792).length < 2 ^ (prefixWord ++ tailWord_455792).sum := by decide
  have hdescent : baseEnd_455792 < baseStart_455792 := by decide
  rcases family_descends (prefixWord ++ tailWord_455792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455809 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_455809 : Nat := 118140960795 + 455809 * 2 ^ 59
def prefixEnd_455809 : Nat := 4983230072969 + 3 ^ 40 * 455809 * 2
def baseEnd_455809 : Nat := 156032735763541585927519

theorem tailTrace_455809 : CollatzResearch.WordTrace tailWord_455809 prefixEnd_455809 156032735763541585927519 := by
  unfold tailWord_455809
  simp only [CollatzResearch.WordTrace]
  refine ⟨16624720005689313824674481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11083146670459542549782987 16624720005689313824674481)
  ·
    refine ⟨12468540004266985368505861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16624720005689313824674481 12468540004266985368505861)
    ·
      refine ⟨2337851250800059756594849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12468540004266985368505861 2337851250800059756594849)
      ·
        refine ⟨1753388438100044817446137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337851250800059756594849 1753388438100044817446137)
        ·
          refine ⟨1315041328575033613084603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753388438100044817446137 1315041328575033613084603)
          ·
            refine ⟨1972561992862550419626905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315041328575033613084603 1972561992862550419626905)
            ·
              refine ⟨1479421494646912814720179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972561992862550419626905 1479421494646912814720179)
              ·
                refine ⟨2219132241970369222080269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479421494646912814720179 2219132241970369222080269)
                ·
                  refine ⟨832174590738888458280101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2219132241970369222080269 832174590738888458280101)
                  ·
                    refine ⟨156032735763541585927519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832174590738888458280101 156032735763541585927519)
                    ·
                      rfl

theorem cell22_455809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_455809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455809 prefixEnd_455809 := by exact prefixLift 455809
  have htrace : WordTrace (prefixWord ++ tailWord_455809) baseStart_455809 baseEnd_455809 := by
    simpa [prefixWord, tailWord_455809, baseEnd_455809] using wordTrace_append hprefix tailTrace_455809
  have hstable : (prefixWord ++ tailWord_455809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455809).length < 2 ^ (prefixWord ++ tailWord_455809).sum := by decide
  have hdescent : baseEnd_455809 < baseStart_455809 := by decide
  rcases family_descends (prefixWord ++ tailWord_455809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455826 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_455826 : Nat := 118140960795 + 455826 * 2 ^ 59
def prefixEnd_455826 : Nat := 4983230072969 + 3 ^ 40 * 455826 * 2
def baseEnd_455826 : Nat := 156038555210959208252467

theorem tailTrace_455826 : CollatzResearch.WordTrace tailWord_455826 prefixEnd_455826 156038555210959208252467 := by
  unfold tailWord_455826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156335011656931432010833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11083560031085150485362221 4156335011656931432010833)
  ·
    refine ⟨3117251258742698574008125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4156335011656931432010833 3117251258742698574008125)
    ·
      refine ⟨1168969222028511965253047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3117251258742698574008125 1168969222028511965253047)
      ·
        refine ⟨1753453833042767947879571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168969222028511965253047 1753453833042767947879571)
        ·
          refine ⟨2630180749564151921819357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753453833042767947879571 2630180749564151921819357)
          ·
            refine ⟨986317781086556970682259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2630180749564151921819357 986317781086556970682259)
            ·
              refine ⟨1479476671629835456023389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986317781086556970682259 1479476671629835456023389)
              ·
                refine ⟨554803751861188296008771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479476671629835456023389 554803751861188296008771)
                ·
                  refine ⟨832205627791782444013157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554803751861188296008771 832205627791782444013157)
                  ·
                    refine ⟨156038555210959208252467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832205627791782444013157 156038555210959208252467)
                    ·
                      rfl

theorem cell22_455826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_455826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455826 prefixEnd_455826 := by exact prefixLift 455826
  have htrace : WordTrace (prefixWord ++ tailWord_455826) baseStart_455826 baseEnd_455826 := by
    simpa [prefixWord, tailWord_455826, baseEnd_455826] using wordTrace_append hprefix tailTrace_455826
  have hstable : (prefixWord ++ tailWord_455826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455826).length < 2 ^ (prefixWord ++ tailWord_455826).sum := by decide
  have hdescent : baseEnd_455826 < baseStart_455826 := by decide
  rcases family_descends (prefixWord ++ tailWord_455826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455869 : List Nat := [1, 4, 1, 2, 1, 1, 6, 6]
def baseStart_455869 : Nat := 118140960795 + 455869 * 2 ^ 59
def prefixEnd_455869 : Nat := 4983230072969 + 3 ^ 40 * 455869 * 2
def baseEnd_455869 : Nat := 17339252776635714380815

theorem tailTrace_455869 : CollatzResearch.WordTrace tailWord_455869 prefixEnd_455869 17339252776635714380815 := by
  unfold tailWord_455869
  simp only [CollatzResearch.WordTrace]
  refine ⟨16626908385471944071858661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11084605590314629381239107 16626908385471944071858661)
  ·
    refine ⟨3117545322275989513473499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16626908385471944071858661 3117545322275989513473499)
    ·
      refine ⟨4676317983413984270210249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3117545322275989513473499 4676317983413984270210249)
      ·
        refine ⟨3507238487560488202657687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4676317983413984270210249 3507238487560488202657687)
        ·
          refine ⟨5260857731340732303986531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507238487560488202657687 5260857731340732303986531)
          ·
            refine ⟨7891286597011098455979797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260857731340732303986531 7891286597011098455979797)
            ·
              refine ⟨369904059234895240124053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7891286597011098455979797 369904059234895240124053)
              ·
                refine ⟨17339252776635714380815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 369904059234895240124053 17339252776635714380815)
                ·
                  rfl

theorem cell22_455869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 6].length) (baseStart_455869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455869 prefixEnd_455869 := by exact prefixLift 455869
  have htrace : WordTrace (prefixWord ++ tailWord_455869) baseStart_455869 baseEnd_455869 := by
    simpa [prefixWord, tailWord_455869, baseEnd_455869] using wordTrace_append hprefix tailTrace_455869
  have hstable : (prefixWord ++ tailWord_455869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455869).length < 2 ^ (prefixWord ++ tailWord_455869).sum := by decide
  have hdescent : baseEnd_455869 < baseStart_455869 := by decide
  rcases family_descends (prefixWord ++ tailWord_455869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455886 : List Nat := [4, 1, 1, 1, 6, 1, 8]
def baseStart_455886 : Nat := 118140960795 + 455886 * 2 ^ 59
def prefixEnd_455886 : Nat := 4983230072969 + 3 ^ 40 * 455886 * 2
def baseEnd_455886 : Nat := 5779966460634779694529

theorem tailTrace_455886 : CollatzResearch.WordTrace tailWord_455886 prefixEnd_455886 5779966460634779694529 := by
  unfold tailWord_455886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078441053301294496903439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11085018950940237316818341 2078441053301294496903439)
  ·
    refine ⟨3117661579951941745355159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2078441053301294496903439 3117661579951941745355159)
    ·
      refine ⟨4676492369927912618032739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3117661579951941745355159 4676492369927912618032739)
      ·
        refine ⟨7014738554891868927049109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4676492369927912618032739 7014738554891868927049109)
        ·
          refine ⟨328815869760556355955427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7014738554891868927049109 328815869760556355955427)
          ·
            refine ⟨493223804640834533933141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328815869760556355955427 493223804640834533933141)
            ·
              refine ⟨5779966460634779694529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 493223804640834533933141 5779966460634779694529)
              ·
                rfl

theorem cell22_455886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 8].length) (baseStart_455886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455886 prefixEnd_455886 := by exact prefixLift 455886
  have htrace : WordTrace (prefixWord ++ tailWord_455886) baseStart_455886 baseEnd_455886 := by
    simpa [prefixWord, tailWord_455886, baseEnd_455886] using wordTrace_append hprefix tailTrace_455886
  have hstable : (prefixWord ++ tailWord_455886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455886).length < 2 ^ (prefixWord ++ tailWord_455886).sum := by decide
  have hdescent : baseEnd_455886 < baseStart_455886 := by decide
  rcases family_descends (prefixWord ++ tailWord_455886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455927 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 8]
def baseStart_455927 : Nat := 118140960795 + 455927 * 2 ^ 59
def prefixEnd_455927 : Nat := 4983230072969 + 3 ^ 40 * 455927 * 2
def baseEnd_455927 : Nat := 156073129575028611477157

theorem tailTrace_455927 : CollatzResearch.WordTrace tailWord_455927 prefixEnd_455927 156073129575028611477157 := by
  unfold tailWord_455927
  simp only [CollatzResearch.WordTrace]
  refine ⟨16629023819261819977470035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11086015879507879984980023 16629023819261819977470035)
  ·
    refine ⟨24943535728892729966205053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16629023819261819977470035 24943535728892729966205053)
    ·
      refine ⟨9353825898334773737326895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24943535728892729966205053 9353825898334773737326895)
      ·
        refine ⟨14030738847502160605990343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9353825898334773737326895 14030738847502160605990343)
        ·
          refine ⟨21046108271253240908985515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14030738847502160605990343 21046108271253240908985515)
          ·
            refine ⟨31569162406879861363478273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21046108271253240908985515 31569162406879861363478273)
            ·
              refine ⟨23676871805159896022608705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31569162406879861363478273 23676871805159896022608705)
              ·
                refine ⟨17757653853869922016956529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23676871805159896022608705 17757653853869922016956529)
                ·
                  refine ⟨13318240390402441512717397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17757653853869922016956529 13318240390402441512717397)
                  ·
                    refine ⟨156073129575028611477157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13318240390402441512717397 156073129575028611477157)
                    ·
                      rfl

theorem cell22_455927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_455927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455927 prefixEnd_455927 := by exact prefixLift 455927
  have htrace : WordTrace (prefixWord ++ tailWord_455927) baseStart_455927 baseEnd_455927 := by
    simpa [prefixWord, tailWord_455927, baseEnd_455927] using wordTrace_append hprefix tailTrace_455927
  have hstable : (prefixWord ++ tailWord_455927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455927).length < 2 ^ (prefixWord ++ tailWord_455927).sum := by decide
  have hdescent : baseEnd_455927 < baseStart_455927 := by decide
  rcases family_descends (prefixWord ++ tailWord_455927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455959 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 6]
def baseStart_455959 : Nat := 118140960795 + 455959 * 2 ^ 59
def prefixEnd_455959 : Nat := 4983230072969 + 3 ^ 40 * 455959 * 2
def baseEnd_455959 : Nat := 52028027942997064892353

theorem tailTrace_455959 : CollatzResearch.WordTrace tailWord_455959 prefixEnd_455959 52028027942997064892353 := by
  unfold tailWord_455959
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630190955145889442634931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11086793970097259628423287 16630190955145889442634931)
  ·
    refine ⟨24945286432718834163952397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16630190955145889442634931 24945286432718834163952397)
    ·
      refine ⟨9354482412269562811482149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24945286432718834163952397 9354482412269562811482149)
      ·
        refine ⟨1753965452300543027152903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9354482412269562811482149 1753965452300543027152903)
        ·
          refine ⟨2630948178450814540729355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753965452300543027152903 2630948178450814540729355)
          ·
            refine ⟨3946422267676221811094033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630948178450814540729355 3946422267676221811094033)
            ·
              refine ⟨2959816700757166358320525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946422267676221811094033 2959816700757166358320525)
              ·
                refine ⟨1109931262783937384370197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2959816700757166358320525 1109931262783937384370197)
                ·
                  refine ⟨52028027942997064892353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1109931262783937384370197 52028027942997064892353)
                  ·
                    rfl

theorem cell22_455959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 6].length) (baseStart_455959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455959 prefixEnd_455959 := by exact prefixLift 455959
  have htrace : WordTrace (prefixWord ++ tailWord_455959) baseStart_455959 baseEnd_455959 := by
    simpa [prefixWord, tailWord_455959, baseEnd_455959] using wordTrace_append hprefix tailTrace_455959
  have hstable : (prefixWord ++ tailWord_455959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455959).length < 2 ^ (prefixWord ++ tailWord_455959).sum := by decide
  have hdescent : baseEnd_455959 < baseStart_455959 := by decide
  rcases family_descends (prefixWord ++ tailWord_455959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455976 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 6]
def baseStart_455976 : Nat := 118140960795 + 455976 * 2 ^ 59
def prefixEnd_455976 : Nat := 4983230072969 + 3 ^ 40 * 455976 * 2
def baseEnd_455976 : Nat := 52029967758802939000669

theorem tailTrace_455976 : CollatzResearch.WordTrace tailWord_455976 prefixEnd_455976 52029967758802939000669 := by
  unfold tailWord_455976
  simp only [CollatzResearch.WordTrace]
  refine ⟨8315405498042150673001891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11087207330722867564002521 8315405498042150673001891)
  ·
    refine ⟨12473108247063226009502837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8315405498042150673001891 12473108247063226009502837)
    ·
      refine ⟨1169353898162177438390891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12473108247063226009502837 1169353898162177438390891)
      ·
        refine ⟨1754030847243266157586337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169353898162177438390891 1754030847243266157586337)
        ·
          refine ⟨1315523135432449618189753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1754030847243266157586337 1315523135432449618189753)
          ·
            refine ⟨986642351574337213642315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1315523135432449618189753 986642351574337213642315)
            ·
              refine ⟨1479963527361505820463473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986642351574337213642315 1479963527361505820463473)
              ·
                refine ⟨1109972645521129365347605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479963527361505820463473 1109972645521129365347605)
                ·
                  refine ⟨52029967758802939000669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1109972645521129365347605 52029967758802939000669)
                  ·
                    rfl

theorem cell22_455976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_455976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_455976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_455976 prefixEnd_455976 := by exact prefixLift 455976
  have htrace : WordTrace (prefixWord ++ tailWord_455976) baseStart_455976 baseEnd_455976 := by
    simpa [prefixWord, tailWord_455976, baseEnd_455976] using wordTrace_append hprefix tailTrace_455976
  have hstable : (prefixWord ++ tailWord_455976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455976).length < 2 ^ (prefixWord ++ tailWord_455976).sum := by decide
  have hdescent : baseEnd_455976 < baseStart_455976 := by decide
  rcases family_descends (prefixWord ++ tailWord_455976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456049 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 7]
def baseStart_456049 : Nat := 118140960795 + 456049 * 2 ^ 59
def prefixEnd_456049 : Nat := 4983230072969 + 3 ^ 40 * 456049 * 2
def baseEnd_456049 : Nat := 52038297556086986642261

theorem tailTrace_456049 : CollatzResearch.WordTrace tailWord_456049 prefixEnd_456049 52038297556086986642261 := by
  unfold tailWord_456049
  simp only [CollatzResearch.WordTrace]
  refine ⟨16633473524819834813411201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11088982349879889875607467 16633473524819834813411201)
  ·
    refine ⟨12475105143614876110058401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16633473524819834813411201 12475105143614876110058401)
    ·
      refine ⟨9356328857711157082543801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12475105143614876110058401 9356328857711157082543801)
      ·
        refine ⟨7017246643283367811907851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9356328857711157082543801 7017246643283367811907851)
        ·
          refine ⟨10525869964925051717861777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017246643283367811907851 10525869964925051717861777)
          ·
            refine ⟨7894402473693788788396333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10525869964925051717861777 7894402473693788788396333)
            ·
              refine ⟨2960400927635170795648625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7894402473693788788396333 2960400927635170795648625)
              ·
                refine ⟨2220300695726378096736469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960400927635170795648625 2220300695726378096736469)
                ·
                  refine ⟨52038297556086986642261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2220300695726378096736469 52038297556086986642261)
                  ·
                    rfl

theorem cell22_456049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_456049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456049 prefixEnd_456049 := by exact prefixLift 456049
  have htrace : WordTrace (prefixWord ++ tailWord_456049) baseStart_456049 baseEnd_456049 := by
    simpa [prefixWord, tailWord_456049, baseEnd_456049] using wordTrace_append hprefix tailTrace_456049
  have hstable : (prefixWord ++ tailWord_456049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456049).length < 2 ^ (prefixWord ++ tailWord_456049).sum := by decide
  have hdescent : baseEnd_456049 < baseStart_456049 := by decide
  rcases family_descends (prefixWord ++ tailWord_456049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456064 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_456064 : Nat := 118140960795 + 456064 * 2 ^ 59
def prefixEnd_456064 : Nat := 4983230072969 + 3 ^ 40 * 456064 * 2
def baseEnd_456064 : Nat := 156120027474805920801737

theorem tailTrace_456064 : CollatzResearch.WordTrace tailWord_456064 prefixEnd_456064 156120027474805920801737 := by
  unfold tailWord_456064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317010309882746187603623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11089347079843661583471497 8317010309882746187603623)
  ·
    refine ⟨12475515464824119281405435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8317010309882746187603623 12475515464824119281405435)
    ·
      refine ⟨18713273197236178922108153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12475515464824119281405435 18713273197236178922108153)
      ·
        refine ⟨14034954897927134191581115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18713273197236178922108153 14034954897927134191581115)
        ·
          refine ⟨21052432346890701287371673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14034954897927134191581115 21052432346890701287371673)
          ·
            refine ⟨15789324260168025965528755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21052432346890701287371673 15789324260168025965528755)
            ·
              refine ⟨23683986390252038948293133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15789324260168025965528755 23683986390252038948293133)
              ·
                refine ⟨8881494896344514605609925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23683986390252038948293133 8881494896344514605609925)
                ·
                  refine ⟨1665280293064596488551861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8881494896344514605609925 1665280293064596488551861)
                  ·
                    refine ⟨156120027474805920801737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1665280293064596488551861 156120027474805920801737)
                    ·
                      rfl

theorem cell22_456064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_456064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456064 prefixEnd_456064 := by exact prefixLift 456064
  have htrace : WordTrace (prefixWord ++ tailWord_456064) baseStart_456064 baseEnd_456064 := by
    simpa [prefixWord, tailWord_456064, baseEnd_456064] using wordTrace_append hprefix tailTrace_456064
  have hstable : (prefixWord ++ tailWord_456064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456064).length < 2 ^ (prefixWord ++ tailWord_456064).sum := by decide
  have hdescent : baseEnd_456064 < baseStart_456064 := by decide
  rcases family_descends (prefixWord ++ tailWord_456064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456096 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_456096 : Nat := 118140960795 + 456096 * 2 ^ 59
def prefixEnd_456096 : Nat := 4983230072969 + 3 ^ 40 * 456096 * 2
def baseEnd_456096 : Nat := 156130981728768504001639

theorem tailTrace_456096 : CollatzResearch.WordTrace tailWord_456096 prefixEnd_456096 156130981728768504001639 := by
  unfold tailWord_456096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317593877824780920186071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11090125170433041226914761 8317593877824780920186071)
  ·
    refine ⟨12476390816737171380279107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8317593877824780920186071 12476390816737171380279107)
    ·
      refine ⟨18714586225105757070418661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12476390816737171380279107 18714586225105757070418661)
      ·
        refine ⟨3508984917207329450703499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18714586225105757070418661 3508984917207329450703499)
        ·
          refine ⟨5263477375810994176055249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508984917207329450703499 5263477375810994176055249)
          ·
            refine ⟨3947608031858245632041437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5263477375810994176055249 3947608031858245632041437)
            ·
              refine ⟨1480353011946842112015539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3947608031858245632041437 1480353011946842112015539)
              ·
                refine ⟨2220529517920263168023309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480353011946842112015539 2220529517920263168023309)
                ·
                  refine ⟨832698569220098688008741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2220529517920263168023309 832698569220098688008741)
                  ·
                    refine ⟨156130981728768504001639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 832698569220098688008741 156130981728768504001639)
                    ·
                      rfl

theorem cell22_456096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_456096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456096 prefixEnd_456096 := by exact prefixLift 456096
  have htrace : WordTrace (prefixWord ++ tailWord_456096) baseStart_456096 baseEnd_456096 := by
    simpa [prefixWord, tailWord_456096, baseEnd_456096] using wordTrace_append hprefix tailTrace_456096
  have hstable : (prefixWord ++ tailWord_456096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456096).length < 2 ^ (prefixWord ++ tailWord_456096).sum := by decide
  have hdescent : baseEnd_456096 < baseStart_456096 := by decide
  rcases family_descends (prefixWord ++ tailWord_456096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456126 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_456126 : Nat := 118140960795 + 456126 * 2 ^ 59
def prefixEnd_456126 : Nat := 4983230072969 + 3 ^ 40 * 456126 * 2
def baseEnd_456126 : Nat := 156141251341858425751547

theorem tailTrace_456126 : CollatzResearch.WordTrace tailWord_456126 prefixEnd_456126 156141251341858425751547 := by
  unfold tailWord_456126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079535243192609620495529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11090854630360584642642821 2079535243192609620495529)
  ·
    refine ⟨1559651432394457215371647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2079535243192609620495529 1559651432394457215371647)
    ·
      refine ⟨2339477148591685823057471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559651432394457215371647 2339477148591685823057471)
      ·
        refine ⟨3509215722887528734586207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339477148591685823057471 3509215722887528734586207)
        ·
          refine ⟨5263823584331293101879311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509215722887528734586207 5263823584331293101879311)
          ·
            refine ⟨7895735376496939652818967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263823584331293101879311 7895735376496939652818967)
            ·
              refine ⟨11843603064745409479228451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7895735376496939652818967 11843603064745409479228451)
              ·
                refine ⟨17765404597118114218842677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11843603064745409479228451 17765404597118114218842677)
                ·
                  refine ⟨1665506680979823208016501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17765404597118114218842677 1665506680979823208016501)
                  ·
                    refine ⟨156141251341858425751547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1665506680979823208016501 156141251341858425751547)
                    ·
                      rfl

theorem cell22_456126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_456126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456126 prefixEnd_456126 := by exact prefixLift 456126
  have htrace : WordTrace (prefixWord ++ tailWord_456126) baseStart_456126 baseEnd_456126 := by
    simpa [prefixWord, tailWord_456126, baseEnd_456126] using wordTrace_append hprefix tailTrace_456126
  have hstable : (prefixWord ++ tailWord_456126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456126).length < 2 ^ (prefixWord ++ tailWord_456126).sum := by decide
  have hdescent : baseEnd_456126 < baseStart_456126 := by decide
  rcases family_descends (prefixWord ++ tailWord_456126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456143 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 2, 3]
def baseStart_456143 : Nat := 118140960795 + 456143 * 2 ^ 59
def prefixEnd_456143 : Nat := 4983230072969 + 3 ^ 40 * 456143 * 2
def baseEnd_456143 : Nat := 156147070789276048076495

theorem tailTrace_456143 : CollatzResearch.WordTrace tailWord_456143 prefixEnd_456143 156147070789276048076495 := by
  unfold tailWord_456143
  simp only [CollatzResearch.WordTrace]
  refine ⟨16636901986479288867333083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11091267990986192578222055 16636901986479288867333083)
  ·
    refine ⟨24955352979718933300999625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16636901986479288867333083 24955352979718933300999625)
    ·
      refine ⟨18716514734789199975749719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24955352979718933300999625 18716514734789199975749719)
      ·
        refine ⟨28074772102183799963624579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18716514734789199975749719 28074772102183799963624579)
        ·
          refine ⟨42112158153275699945436869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28074772102183799963624579 42112158153275699945436869)
          ·
            refine ⟨7896029653739193739769413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42112158153275699945436869 7896029653739193739769413)
            ·
              refine ⟨1480505560076098826206765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7896029653739193739769413 1480505560076098826206765)
              ·
                refine ⟨555189585028537059827537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1480505560076098826206765 555189585028537059827537)
                ·
                  refine ⟨416392188771402794870653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555189585028537059827537 416392188771402794870653)
                  ·
                    refine ⟨156147070789276048076495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416392188771402794870653 156147070789276048076495)
                    ·
                      rfl

theorem cell22_456143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_456143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456143 prefixEnd_456143 := by exact prefixLift 456143
  have htrace : WordTrace (prefixWord ++ tailWord_456143) baseStart_456143 baseEnd_456143 := by
    simpa [prefixWord, tailWord_456143, baseEnd_456143] using wordTrace_append hprefix tailTrace_456143
  have hstable : (prefixWord ++ tailWord_456143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456143).length < 2 ^ (prefixWord ++ tailWord_456143).sum := by decide
  have hdescent : baseEnd_456143 < baseStart_456143 := by decide
  rcases family_descends (prefixWord ++ tailWord_456143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456173 : List Nat := [1, 5, 1, 3, 2, 1, 9]
def baseStart_456173 : Nat := 118140960795 + 456173 * 2 ^ 59
def prefixEnd_456173 : Nat := 4983230072969 + 3 ^ 40 * 456173 * 2
def baseEnd_456173 : Nat := 5783605200087628512089

theorem tailTrace_456173 : CollatzResearch.WordTrace tailWord_456173 prefixEnd_456173 5783605200087628512089 := by
  unfold tailWord_456173
  simp only [CollatzResearch.WordTrace]
  refine ⟨16637996176370603990925173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11091997450913735993950115 16637996176370603990925173)
  ·
    refine ⟨1559812141534744124149235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16637996176370603990925173 1559812141534744124149235)
    ·
      refine ⟨2339718212302116186223853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559812141534744124149235 2339718212302116186223853)
      ·
        refine ⟨877394329613293569833945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2339718212302116186223853 877394329613293569833945)
        ·
          refine ⟨658045747209970177375459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877394329613293569833945 658045747209970177375459)
          ·
            refine ⟨987068620814955266063189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658045747209970177375459 987068620814955266063189)
            ·
              refine ⟨5783605200087628512089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 987068620814955266063189 5783605200087628512089)
              ·
                rfl

theorem cell22_456173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 9].length) (baseStart_456173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456173 prefixEnd_456173 := by exact prefixLift 456173
  have htrace : WordTrace (prefixWord ++ tailWord_456173) baseStart_456173 baseEnd_456173 := by
    simpa [prefixWord, tailWord_456173, baseEnd_456173] using wordTrace_append hprefix tailTrace_456173
  have hstable : (prefixWord ++ tailWord_456173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456173).length < 2 ^ (prefixWord ++ tailWord_456173).sum := by decide
  have hdescent : baseEnd_456173 < baseStart_456173 := by decide
  rcases family_descends (prefixWord ++ tailWord_456173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456188 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_456188 : Nat := 118140960795 + 456188 * 2 ^ 59
def prefixEnd_456188 : Nat := 4983230072969 + 3 ^ 40 * 456188 * 2
def baseEnd_456188 : Nat := 156162475208910930701357

theorem tailTrace_456188 : CollatzResearch.WordTrace tailWord_456188 prefixEnd_456188 156162475208910930701357 := by
  unfold tailWord_456188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319271635658130776360609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11092362180877507701814145 8319271635658130776360609)
  ·
    refine ⟨6239453726743598082270457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8319271635658130776360609 6239453726743598082270457)
    ·
      refine ⟨4679590295057698561702843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6239453726743598082270457 4679590295057698561702843)
      ·
        refine ⟨7019385442586547842554265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4679590295057698561702843 7019385442586547842554265)
        ·
          refine ⟨5264539081939910881915699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7019385442586547842554265 5264539081939910881915699)
          ·
            refine ⟨7896808622909866322873549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264539081939910881915699 7896808622909866322873549)
            ·
              refine ⟨2961303233591199871077581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7896808622909866322873549 2961303233591199871077581)
              ·
                refine ⟨1110488712596699951654093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2961303233591199871077581 1110488712596699951654093)
                ·
                  refine ⟨416433267223762481870285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110488712596699951654093 416433267223762481870285)
                  ·
                    refine ⟨156162475208910930701357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416433267223762481870285 156162475208910930701357)
                    ·
                      rfl

theorem cell22_456188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_456188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456188 prefixEnd_456188 := by exact prefixLift 456188
  have htrace : WordTrace (prefixWord ++ tailWord_456188) baseStart_456188 baseEnd_456188 := by
    simpa [prefixWord, tailWord_456188, baseEnd_456188] using wordTrace_append hprefix tailTrace_456188
  have hstable : (prefixWord ++ tailWord_456188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456188).length < 2 ^ (prefixWord ++ tailWord_456188).sum := by decide
  have hdescent : baseEnd_456188 < baseStart_456188 := by decide
  rcases family_descends (prefixWord ++ tailWord_456188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456194 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_456194 : Nat := 118140960795 + 456194 * 2 ^ 59
def prefixEnd_456194 : Nat := 4983230072969 + 3 ^ 40 * 456194 * 2
def baseEnd_456194 : Nat := 156164529131528915051339

theorem tailTrace_456194 : CollatzResearch.WordTrace tailWord_456194 prefixEnd_456194 156164529131528915051339 := by
  unfold tailWord_456194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159690527323631144359909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11092508072863016384959757 4159690527323631144359909)
  ·
    refine ⟨779941973873180839567483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4159690527323631144359909 779941973873180839567483)
    ·
      refine ⟨1169912960809771259351225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779941973873180839567483 1169912960809771259351225)
      ·
        refine ⟨877434720607328444513419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1169912960809771259351225 877434720607328444513419)
        ·
          refine ⟨1316152080910992666770129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877434720607328444513419 1316152080910992666770129)
          ·
            refine ⟨987114060683244500077597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316152080910992666770129 987114060683244500077597)
            ·
              refine ⟨370167772756216687529099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 987114060683244500077597 370167772756216687529099)
              ·
                refine ⟨555251659134325031293649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370167772756216687529099 555251659134325031293649)
                ·
                  refine ⟨416438744350743773470237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555251659134325031293649 416438744350743773470237)
                  ·
                    refine ⟨156164529131528915051339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416438744350743773470237 156164529131528915051339)
                    ·
                      rfl

theorem cell22_456194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_456194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456194 prefixEnd_456194 := by exact prefixLift 456194
  have htrace : WordTrace (prefixWord ++ tailWord_456194) baseStart_456194 baseEnd_456194 := by
    simpa [prefixWord, tailWord_456194, baseEnd_456194] using wordTrace_append hprefix tailTrace_456194
  have hstable : (prefixWord ++ tailWord_456194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456194).length < 2 ^ (prefixWord ++ tailWord_456194).sum := by decide
  have hdescent : baseEnd_456194 < baseStart_456194 := by decide
  rcases family_descends (prefixWord ++ tailWord_456194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456252 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 5]
def baseStart_456252 : Nat := 118140960795 + 456252 * 2 ^ 59
def prefixEnd_456252 : Nat := 4983230072969 + 3 ^ 40 * 456252 * 2
def baseEnd_456252 : Nat := 52061461238945365700387

theorem tailTrace_456252 : CollatzResearch.WordTrace tailWord_456252 prefixEnd_456252 52061461238945365700387 := by
  unfold tailWord_456252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320438771542200241525505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11093918362056266988700673 8320438771542200241525505)
  ·
    refine ⟨6240329078656650181144129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8320438771542200241525505 6240329078656650181144129)
    ·
      refine ⟨4680246808992487635858097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6240329078656650181144129 4680246808992487635858097)
      ·
        refine ⟨3510185106744365726893573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4680246808992487635858097 3510185106744365726893573)
        ·
          refine ⟨658159707514568573792545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3510185106744365726893573 658159707514568573792545)
          ·
            refine ⟨493619780635926430344409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658159707514568573792545 493619780635926430344409)
            ·
              refine ⟨370214835476944822758307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493619780635926430344409 370214835476944822758307)
              ·
                refine ⟨555322253215417234137461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370214835476944822758307 555322253215417234137461)
                ·
                  refine ⟨52061461238945365700387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 555322253215417234137461 52061461238945365700387)
                  ·
                    rfl

theorem cell22_456252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_456252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456252 prefixEnd_456252 := by exact prefixLift 456252
  have htrace : WordTrace (prefixWord ++ tailWord_456252) baseStart_456252 baseEnd_456252 := by
    simpa [prefixWord, tailWord_456252, baseEnd_456252] using wordTrace_append hprefix tailTrace_456252
  have hstable : (prefixWord ++ tailWord_456252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456252).length < 2 ^ (prefixWord ++ tailWord_456252).sum := by decide
  have hdescent : baseEnd_456252 < baseStart_456252 := by decide
  rcases family_descends (prefixWord ++ tailWord_456252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456291 : List Nat := [1, 1, 1, 5, 1, 13]
def baseStart_456291 : Nat := 118140960795 + 456291 * 2 ^ 59
def prefixEnd_456291 : Nat := 4983230072969 + 3 ^ 40 * 456291 * 2
def baseEnd_456291 : Nat := 1928367089059913523161

theorem tailTrace_456291 : CollatzResearch.WordTrace tailWord_456291 prefixEnd_456291 1928367089059913523161 := by
  unfold tailWord_456291
  simp only [CollatzResearch.WordTrace]
  refine ⟨16642299989943110143720727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11094866659962073429147151 16642299989943110143720727)
  ·
    refine ⟨24963449984914665215581091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16642299989943110143720727 24963449984914665215581091)
    ·
      refine ⟨37445174977371997823371637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24963449984914665215581091 37445174977371997823371637)
      ·
        refine ⟨3510485154128624795941091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37445174977371997823371637 3510485154128624795941091)
        ·
          refine ⟨5265727731192937193911637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510485154128624795941091 5265727731192937193911637)
          ·
            refine ⟨1928367089059913523161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 5265727731192937193911637 1928367089059913523161)
            ·
              rfl

theorem cell22_456291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 13].length) (baseStart_456291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456291 prefixEnd_456291 := by exact prefixLift 456291
  have htrace : WordTrace (prefixWord ++ tailWord_456291) baseStart_456291 baseEnd_456291 := by
    simpa [prefixWord, tailWord_456291, baseEnd_456291] using wordTrace_append hprefix tailTrace_456291
  have hstable : (prefixWord ++ tailWord_456291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456291).length < 2 ^ (prefixWord ++ tailWord_456291).sum := by decide
  have hdescent : baseEnd_456291 < baseStart_456291 := by decide
  rcases family_descends (prefixWord ++ tailWord_456291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456295 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 2, 3]
def baseStart_456295 : Nat := 118140960795 + 456295 * 2 ^ 59
def prefixEnd_456295 : Nat := 4983230072969 + 3 ^ 40 * 456295 * 2
def baseEnd_456295 : Nat := 156199103495598318276029

theorem tailTrace_456295 : CollatzResearch.WordTrace tailWord_456295 prefixEnd_456295 156199103495598318276029 := by
  unfold tailWord_456295
  simp only [CollatzResearch.WordTrace]
  refine ⟨16642445881928618826866339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11094963921285745884577559 16642445881928618826866339)
  ·
    refine ⟨24963668822892928240299509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16642445881928618826866339 24963668822892928240299509)
    ·
      refine ⟨2340343952146212022528079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24963668822892928240299509 2340343952146212022528079)
      ·
        refine ⟨3510515928219318033792119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2340343952146212022528079 3510515928219318033792119)
        ·
          refine ⟨5265773892328977050688179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510515928219318033792119 5265773892328977050688179)
          ·
            refine ⟨7898660838493465576032269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265773892328977050688179 7898660838493465576032269)
            ·
              refine ⟨2961997814435049591012101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7898660838493465576032269 2961997814435049591012101)
              ·
                refine ⟨555374590206571798314769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2961997814435049591012101 555374590206571798314769)
                ·
                  refine ⟨416530942654928848736077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555374590206571798314769 416530942654928848736077)
                  ·
                    refine ⟨156199103495598318276029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416530942654928848736077 156199103495598318276029)
                    ·
                      rfl

theorem cell22_456295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_456295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456295 prefixEnd_456295 := by exact prefixLift 456295
  have htrace : WordTrace (prefixWord ++ tailWord_456295) baseStart_456295 baseEnd_456295 := by
    simpa [prefixWord, tailWord_456295, baseEnd_456295] using wordTrace_append hprefix tailTrace_456295
  have hstable : (prefixWord ++ tailWord_456295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456295).length < 2 ^ (prefixWord ++ tailWord_456295).sum := by decide
  have hdescent : baseEnd_456295 < baseStart_456295 := by decide
  rcases family_descends (prefixWord ++ tailWord_456295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456357 : List Nat := [1, 3, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_456357 : Nat := 118140960795 + 456357 * 2 ^ 59
def prefixEnd_456357 : Nat := 4983230072969 + 3 ^ 40 * 456357 * 2
def baseEnd_456357 : Nat := 156220327362650823225839

theorem tailTrace_456357 : CollatzResearch.WordTrace tailWord_456357 prefixEnd_456357 156220327362650823225839 := by
  unfold tailWord_456357
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644707207704003415623325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11096471471802668943748883 16644707207704003415623325)
  ·
    refine ⟨6241765202889001280858747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16644707207704003415623325 6241765202889001280858747)
    ·
      refine ⟨9362647804333501921288121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6241765202889001280858747 9362647804333501921288121)
      ·
        refine ⟨7021985853250126440966091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9362647804333501921288121 7021985853250126440966091)
        ·
          refine ⟨10532978779875189661449137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021985853250126440966091 10532978779875189661449137)
          ·
            refine ⟨7899734084906392246086853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532978779875189661449137 7899734084906392246086853)
            ·
              refine ⟨1481200140919948546141285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7899734084906392246086853 1481200140919948546141285)
              ·
                refine ⟨277725026422490352401491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1481200140919948546141285 277725026422490352401491)
                ·
                  refine ⟨416587539633735528602237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277725026422490352401491 416587539633735528602237)
                  ·
                    refine ⟨156220327362650823225839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416587539633735528602237 156220327362650823225839)
                    ·
                      rfl

theorem cell22_456357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_456357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456357 prefixEnd_456357 := by exact prefixLift 456357
  have htrace : WordTrace (prefixWord ++ tailWord_456357) baseStart_456357 baseEnd_456357 := by
    simpa [prefixWord, tailWord_456357, baseEnd_456357] using wordTrace_append hprefix tailTrace_456357
  have hstable : (prefixWord ++ tailWord_456357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456357).length < 2 ^ (prefixWord ++ tailWord_456357).sum := by decide
  have hdescent : baseEnd_456357 < baseStart_456357 := by decide
  rcases family_descends (prefixWord ++ tailWord_456357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456368 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_456368 : Nat := 118140960795 + 456368 * 2 ^ 59
def prefixEnd_456368 : Nat := 4983230072969 + 3 ^ 40 * 456368 * 2
def baseEnd_456368 : Nat := 156224092887450461200805

theorem tailTrace_456368 : CollatzResearch.WordTrace tailWord_456368 prefixEnd_456368 156224092887450461200805 := by
  unfold tailWord_456368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322554205332076147136879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11096738940442768196182505 8322554205332076147136879)
  ·
    refine ⟨12483831307998114220705319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8322554205332076147136879 12483831307998114220705319)
    ·
      refine ⟨18725746961997171331057979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12483831307998114220705319 18725746961997171331057979)
      ·
        refine ⟨28088620442995756996586969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18725746961997171331057979 28088620442995756996586969)
        ·
          refine ⟨21066465332246817747440227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28088620442995756996586969 21066465332246817747440227)
          ·
            refine ⟨31599697998370226621160341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21066465332246817747440227 31599697998370226621160341)
            ·
              refine ⟨1481235843673604372866891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31599697998370226621160341 1481235843673604372866891)
              ·
                refine ⟨2221853765510406559300337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481235843673604372866891 2221853765510406559300337)
                ·
                  refine ⟨1666390324132804919475253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2221853765510406559300337 1666390324132804919475253)
                  ·
                    refine ⟨156224092887450461200805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1666390324132804919475253 156224092887450461200805)
                    ·
                      rfl

theorem cell22_456368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_456368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456368 prefixEnd_456368 := by exact prefixLift 456368
  have htrace : WordTrace (prefixWord ++ tailWord_456368) baseStart_456368 baseEnd_456368 := by
    simpa [prefixWord, tailWord_456368, baseEnd_456368] using wordTrace_append hprefix tailTrace_456368
  have hstable : (prefixWord ++ tailWord_456368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456368).length < 2 ^ (prefixWord ++ tailWord_456368).sum := by decide
  have hdescent : baseEnd_456368 < baseStart_456368 := by decide
  rcases family_descends (prefixWord ++ tailWord_456368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456374 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_456374 : Nat := 118140960795 + 456374 * 2 ^ 59
def prefixEnd_456374 : Nat := 4983230072969 + 3 ^ 40 * 456374 * 2
def baseEnd_456374 : Nat := 156226146810068445550787

theorem tailTrace_456374 : CollatzResearch.WordTrace tailWord_456374 prefixEnd_456374 156226146810068445550787 := by
  unfold tailWord_456374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040332953040150957437011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11096884832428276879328117 1040332953040150957437011)
  ·
    refine ⟨1560499429560226436155517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1040332953040150957437011 1560499429560226436155517)
    ·
      refine ⟨585187286085084913558319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1560499429560226436155517 585187286085084913558319)
      ·
        refine ⟨877780929127627370337479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585187286085084913558319 877780929127627370337479)
        ·
          refine ⟨1316671393691441055506219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877780929127627370337479 1316671393691441055506219)
          ·
            refine ⟨1975007090537161583259329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316671393691441055506219 1975007090537161583259329)
            ·
              refine ⟨1481255317902871187444497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975007090537161583259329 1481255317902871187444497)
              ·
                refine ⟨1110941488427153390583373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481255317902871187444497 1110941488427153390583373)
                ·
                  refine ⟨416603058160182521468765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110941488427153390583373 416603058160182521468765)
                  ·
                    refine ⟨156226146810068445550787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416603058160182521468765 156226146810068445550787)
                    ·
                      rfl

theorem cell22_456374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_456374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456374 prefixEnd_456374 := by exact prefixLift 456374
  have htrace : WordTrace (prefixWord ++ tailWord_456374) baseStart_456374 baseEnd_456374 := by
    simpa [prefixWord, tailWord_456374, baseEnd_456374] using wordTrace_append hprefix tailTrace_456374
  have hstable : (prefixWord ++ tailWord_456374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456374).length < 2 ^ (prefixWord ++ tailWord_456374).sum := by decide
  have hdescent : baseEnd_456374 < baseStart_456374 := by decide
  rcases family_descends (prefixWord ++ tailWord_456374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456428 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_456428 : Nat := 118140960795 + 456428 * 2 ^ 59
def prefixEnd_456428 : Nat := 4983230072969 + 3 ^ 40 * 456428 * 2
def baseEnd_456428 : Nat := 156244632113630304700621

theorem tailTrace_456428 : CollatzResearch.WordTrace tailWord_456428 prefixEnd_456428 156244632113630304700621 := by
  unfold tailWord_456428
  simp only [CollatzResearch.WordTrace]
  refine ⟨8323648395223391270728969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11098197860297855027638625 8323648395223391270728969)
  ·
    refine ⟨6242736296417543453046727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8323648395223391270728969 6242736296417543453046727)
    ·
      refine ⟨9364104444626315179570091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242736296417543453046727 9364104444626315179570091)
      ·
        refine ⟨14046156666939472769355137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364104444626315179570091 14046156666939472769355137)
        ·
          refine ⟨10534617500204604577016353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14046156666939472769355137 10534617500204604577016353)
          ·
            refine ⟨7900963125153453432762265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10534617500204604577016353 7900963125153453432762265)
            ·
              refine ⟨5925722343865090074571699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7900963125153453432762265 5925722343865090074571699)
              ·
                refine ⟨8888583515797635111857549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925722343865090074571699 8888583515797635111857549)
                ·
                  refine ⟨3333218818424113166946581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8888583515797635111857549 3333218818424113166946581)
                  ·
                    refine ⟨156244632113630304700621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3333218818424113166946581 156244632113630304700621)
                    ·
                      rfl

theorem cell22_456428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_456428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456428 prefixEnd_456428 := by exact prefixLift 456428
  have htrace : WordTrace (prefixWord ++ tailWord_456428) baseStart_456428 baseEnd_456428 := by
    simpa [prefixWord, tailWord_456428, baseEnd_456428] using wordTrace_append hprefix tailTrace_456428
  have hstable : (prefixWord ++ tailWord_456428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456428).length < 2 ^ (prefixWord ++ tailWord_456428).sum := by decide
  have hdescent : baseEnd_456428 < baseStart_456428 := by decide
  rcases family_descends (prefixWord ++ tailWord_456428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456430 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_456430 : Nat := 118140960795 + 456430 * 2 ^ 59
def prefixEnd_456430 : Nat := 4983230072969 + 3 ^ 40 * 456430 * 2
def baseEnd_456430 : Nat := 156245316754502966150615

theorem tailTrace_456430 : CollatzResearch.WordTrace tailWord_456430 prefixEnd_456430 156245316754502966150615 := by
  unfold tailWord_456430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080921217054942110378843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11098246490959691255353829 2080921217054942110378843)
  ·
    refine ⟨3121381825582413165568265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2080921217054942110378843 3121381825582413165568265)
    ·
      refine ⟨2341036369186809874176199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3121381825582413165568265 2341036369186809874176199)
      ·
        refine ⟨3511554553780214811264299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341036369186809874176199 3511554553780214811264299)
        ·
          refine ⟨5267331830670322216896449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511554553780214811264299 5267331830670322216896449)
          ·
            refine ⟨3950498873002741662672337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5267331830670322216896449 3950498873002741662672337)
            ·
              refine ⟨2962874154752056247004253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950498873002741662672337 2962874154752056247004253)
              ·
                refine ⟨1111077808032021092626595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962874154752056247004253 1111077808032021092626595)
                ·
                  refine ⟨1666616712048031638939893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111077808032021092626595 1666616712048031638939893)
                  ·
                    refine ⟨156245316754502966150615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1666616712048031638939893 156245316754502966150615)
                    ·
                      rfl

theorem cell22_456430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_456430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456430 prefixEnd_456430 := by exact prefixLift 456430
  have htrace : WordTrace (prefixWord ++ tailWord_456430) baseStart_456430 baseEnd_456430 := by
    simpa [prefixWord, tailWord_456430, baseEnd_456430] using wordTrace_append hprefix tailTrace_456430
  have hstable : (prefixWord ++ tailWord_456430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456430).length < 2 ^ (prefixWord ++ tailWord_456430).sum := by decide
  have hdescent : baseEnd_456430 < baseStart_456430 := by decide
  rcases family_descends (prefixWord ++ tailWord_456430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456466 : List Nat := [3, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_456466 : Nat := 118140960795 + 456466 * 2 ^ 59
def prefixEnd_456466 : Nat := 4983230072969 + 3 ^ 40 * 456466 * 2
def baseEnd_456466 : Nat := 52085880096736957416835

theorem tailTrace_456466 : CollatzResearch.WordTrace tailWord_456466 prefixEnd_456466 52085880096736957416835 := by
  unfold tailWord_456466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162170691077278757835313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11099121842872743354227501 4162170691077278757835313)
  ·
    refine ⟨3121628018307959068376485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4162170691077278757835313 3121628018307959068376485)
    ·
      refine ⟨585305253432742325320591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3121628018307959068376485 585305253432742325320591)
      ·
        refine ⟨877957880149113487980887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585305253432742325320591 877957880149113487980887)
        ·
          refine ⟨1316936820223670231971331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877957880149113487980887 1316936820223670231971331)
          ·
            refine ⟨1975405230335505347956997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316936820223670231971331 1975405230335505347956997)
            ·
              refine ⟨370388480687907252741937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1975405230335505347956997 370388480687907252741937)
              ·
                refine ⟨277791360515930439556453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370388480687907252741937 277791360515930439556453)
                ·
                  refine ⟨52085880096736957416835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277791360515930439556453 52085880096736957416835)
                  ·
                    rfl

theorem cell22_456466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_456466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456466 prefixEnd_456466 := by exact prefixLift 456466
  have htrace : WordTrace (prefixWord ++ tailWord_456466) baseStart_456466 baseEnd_456466 := by
    simpa [prefixWord, tailWord_456466, baseEnd_456466] using wordTrace_append hprefix tailTrace_456466
  have hstable : (prefixWord ++ tailWord_456466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456466).length < 2 ^ (prefixWord ++ tailWord_456466).sum := by decide
  have hdescent : baseEnd_456466 < baseStart_456466 := by decide
  rcases family_descends (prefixWord ++ tailWord_456466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456492 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_456492 : Nat := 118140960795 + 456492 * 2 ^ 59
def prefixEnd_456492 : Nat := 4983230072969 + 3 ^ 40 * 456492 * 2
def baseEnd_456492 : Nat := 156266540621555471100425

theorem tailTrace_456492 : CollatzResearch.WordTrace tailWord_456492 prefixEnd_456492 156266540621555471100425 := by
  unfold tailWord_456492
  simp only [CollatzResearch.WordTrace]
  refine ⟨8324815531107460735893865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11099754041476614314525153 8324815531107460735893865)
  ·
    refine ⟨6243611648330595551920399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8324815531107460735893865 6243611648330595551920399)
    ·
      refine ⟨9365417472495893327880599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6243611648330595551920399 9365417472495893327880599)
      ·
        refine ⟨14048126208743839991820899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9365417472495893327880599 14048126208743839991820899)
        ·
          refine ⟨21072189313115759987731349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14048126208743839991820899 21072189313115759987731349)
          ·
            refine ⟨987758874052301249424907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21072189313115759987731349 987758874052301249424907)
            ·
              refine ⟨1481638311078451874137361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987758874052301249424907 1481638311078451874137361)
              ·
                refine ⟨1111228733308838905603021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481638311078451874137361 1111228733308838905603021)
                ·
                  refine ⟨416710774990814589601133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111228733308838905603021 416710774990814589601133)
                  ·
                    refine ⟨156266540621555471100425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416710774990814589601133 156266540621555471100425)
                    ·
                      rfl

theorem cell22_456492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_456492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456492 prefixEnd_456492 := by exact prefixLift 456492
  have htrace : WordTrace (prefixWord ++ tailWord_456492) baseStart_456492 baseEnd_456492 := by
    simpa [prefixWord, tailWord_456492, baseEnd_456492] using wordTrace_append hprefix tailTrace_456492
  have hstable : (prefixWord ++ tailWord_456492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456492).length < 2 ^ (prefixWord ++ tailWord_456492).sum := by decide
  have hdescent : baseEnd_456492 < baseStart_456492 := by decide
  rcases family_descends (prefixWord ++ tailWord_456492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456494 : List Nat := [4, 1, 3, 2, 2, 1, 3, 6]
def baseStart_456494 : Nat := 118140960795 + 456494 * 2 ^ 59
def prefixEnd_456494 : Nat := 4983230072969 + 3 ^ 40 * 456494 * 2
def baseEnd_456494 : Nat := 17363025029158681394491

theorem tailTrace_456494 : CollatzResearch.WordTrace tailWord_456494 prefixEnd_456494 17363025029158681394491 := by
  unfold tailWord_456494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081213001025959476670067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11099802672138450542240357 2081213001025959476670067)
  ·
    refine ⟨3121819501538939215005101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081213001025959476670067 3121819501538939215005101)
    ·
      refine ⟨1170682313077102205626913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3121819501538939215005101 1170682313077102205626913)
      ·
        refine ⟨878011734807826654220185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170682313077102205626913 878011734807826654220185)
        ·
          refine ⟨658508801105869990665139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878011734807826654220185 658508801105869990665139)
          ·
            refine ⟨987763201658804985997709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658508801105869990665139 987763201658804985997709)
            ·
              refine ⟨370411200622051869749141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 987763201658804985997709 370411200622051869749141)
              ·
                refine ⟨17363025029158681394491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 370411200622051869749141 17363025029158681394491)
                ·
                  rfl

theorem cell22_456494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_456494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456494 prefixEnd_456494 := by exact prefixLift 456494
  have htrace : WordTrace (prefixWord ++ tailWord_456494) baseStart_456494 baseEnd_456494 := by
    simpa [prefixWord, tailWord_456494, baseEnd_456494] using wordTrace_append hprefix tailTrace_456494
  have hstable : (prefixWord ++ tailWord_456494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456494).length < 2 ^ (prefixWord ++ tailWord_456494).sum := by decide
  have hdescent : baseEnd_456494 < baseStart_456494 := by decide
  rcases family_descends (prefixWord ++ tailWord_456494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456520 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_456520 : Nat := 118140960795 + 456520 * 2 ^ 59
def prefixEnd_456520 : Nat := 4983230072969 + 3 ^ 40 * 456520 * 2
def baseEnd_456520 : Nat := 156276125593772731400339

theorem tailTrace_456520 : CollatzResearch.WordTrace tailWord_456520 prefixEnd_456520 156276125593772731400339 := by
  unfold tailWord_456520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325326153056741126903507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11100434870742321502538009 8325326153056741126903507)
  ·
    refine ⟨12487989229585111690355261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8325326153056741126903507 12487989229585111690355261)
    ·
      refine ⟨4682995961094416883883223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12487989229585111690355261 4682995961094416883883223)
      ·
        refine ⟨7024493941641625325824835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682995961094416883883223 7024493941641625325824835)
        ·
          refine ⟨10536740912462437988737253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024493941641625325824835 10536740912462437988737253)
          ·
            refine ⟨1975638921086707122888235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10536740912462437988737253 1975638921086707122888235)
            ·
              refine ⟨2963458381630060684332353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975638921086707122888235 2963458381630060684332353)
              ·
                refine ⟨2222593786222545513249265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963458381630060684332353 2222593786222545513249265)
                ·
                  refine ⟨1666945339666909134936949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2222593786222545513249265 1666945339666909134936949)
                  ·
                    refine ⟨156276125593772731400339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1666945339666909134936949 156276125593772731400339)
                    ·
                      rfl

theorem cell22_456520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_456520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456520 prefixEnd_456520 := by exact prefixLift 456520
  have htrace : WordTrace (prefixWord ++ tailWord_456520) baseStart_456520 baseEnd_456520 := by
    simpa [prefixWord, tailWord_456520, baseEnd_456520] using wordTrace_append hprefix tailTrace_456520
  have hstable : (prefixWord ++ tailWord_456520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456520).length < 2 ^ (prefixWord ++ tailWord_456520).sum := by decide
  have hdescent : baseEnd_456520 < baseStart_456520 := by decide
  rcases family_descends (prefixWord ++ tailWord_456520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456584 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 6]
def baseStart_456584 : Nat := 118140960795 + 456584 * 2 ^ 59
def prefixEnd_456584 : Nat := 4983230072969 + 3 ^ 40 * 456584 * 2
def baseEnd_456584 : Nat := 52099344700565965933381

theorem tailTrace_456584 : CollatzResearch.WordTrace tailWord_456584 prefixEnd_456584 52099344700565965933381 := by
  unfold tailWord_456584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8326493288940810592068403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11101991051921080789424537 8326493288940810592068403)
  ·
    refine ⟨12489739933411215888102605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8326493288940810592068403 12489739933411215888102605)
    ·
      refine ⟨4683652475029205958038477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12489739933411215888102605 4683652475029205958038477)
      ·
        refine ⟨1756369678135952234264429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4683652475029205958038477 1756369678135952234264429)
        ·
          refine ⟨658638629300982087849161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1756369678135952234264429 658638629300982087849161)
          ·
            refine ⟨493978971975736565886871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658638629300982087849161 493978971975736565886871)
            ·
              refine ⟨740968457963604848830307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493978971975736565886871 740968457963604848830307)
              ·
                refine ⟨1111452686945407273245461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740968457963604848830307 1111452686945407273245461)
                ·
                  refine ⟨52099344700565965933381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1111452686945407273245461 52099344700565965933381)
                  ·
                    rfl

theorem cell22_456584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_456584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456584 prefixEnd_456584 := by exact prefixLift 456584
  have htrace : WordTrace (prefixWord ++ tailWord_456584) baseStart_456584 baseEnd_456584 := by
    simpa [prefixWord, tailWord_456584, baseEnd_456584] using wordTrace_append hprefix tailTrace_456584
  have hstable : (prefixWord ++ tailWord_456584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456584).length < 2 ^ (prefixWord ++ tailWord_456584).sum := by decide
  have hdescent : baseEnd_456584 < baseStart_456584 := by decide
  rcases family_descends (prefixWord ++ tailWord_456584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456599 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 2, 3]
def baseStart_456599 : Nat := 118140960795 + 456599 * 2 ^ 59
def prefixEnd_456599 : Nat := 4983230072969 + 3 ^ 40 * 456599 * 2
def baseEnd_456599 : Nat := 156303168908242858675097

theorem tailTrace_456599 : CollatzResearch.WordTrace tailWord_456599 prefixEnd_456599 156303168908242858675097 := by
  unfold tailWord_456599
  simp only [CollatzResearch.WordTrace]
  refine ⟨16653533672827278745932851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11102355781884852497288567 16653533672827278745932851)
  ·
    refine ⟨24980300509240918118899277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16653533672827278745932851 24980300509240918118899277)
    ·
      refine ⟨9367612690965344294587229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24980300509240918118899277 9367612690965344294587229)
      ·
        refine ⟨3512854759112004110470211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9367612690965344294587229 3512854759112004110470211)
        ·
          refine ⟨5269282138668006165705317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512854759112004110470211 5269282138668006165705317)
          ·
            refine ⟨987990401000251156069747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5269282138668006165705317 987990401000251156069747)
            ·
              refine ⟨1481985601500376734104621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987990401000251156069747 1481985601500376734104621)
              ·
                refine ⟨555744600562641275289233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481985601500376734104621 555744600562641275289233)
                ·
                  refine ⟨416808450421980956466925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555744600562641275289233 416808450421980956466925)
                  ·
                    refine ⟨156303168908242858675097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416808450421980956466925 156303168908242858675097)
                    ·
                      rfl

theorem cell22_456599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_456599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456599 prefixEnd_456599 := by exact prefixLift 456599
  have htrace : WordTrace (prefixWord ++ tailWord_456599) baseStart_456599 baseEnd_456599 := by
    simpa [prefixWord, tailWord_456599, baseEnd_456599] using wordTrace_append hprefix tailTrace_456599
  have hstable : (prefixWord ++ tailWord_456599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456599).length < 2 ^ (prefixWord ++ tailWord_456599).sum := by decide
  have hdescent : baseEnd_456599 < baseStart_456599 := by decide
  rcases family_descends (prefixWord ++ tailWord_456599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456616 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 1, 5]
def baseStart_456616 : Nat := 118140960795 + 456616 * 2 ^ 59
def prefixEnd_456616 : Nat := 4983230072969 + 3 ^ 40 * 456616 * 2
def baseEnd_456616 : Nat := 156308988355660481000045

theorem tailTrace_456616 : CollatzResearch.WordTrace tailWord_456616 prefixEnd_456616 156308988355660481000045 := by
  unfold tailWord_456616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327076856882845324650851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11102769142510460432867801 8327076856882845324650851)
  ·
    refine ⟨12490615285324267986976277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8327076856882845324650851 12490615285324267986976277)
    ·
      refine ⟨585497591499575061889513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12490615285324267986976277 585497591499575061889513)
      ·
        refine ⟨439123193624681296417135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585497591499575061889513 439123193624681296417135)
        ·
          refine ⟨658684790437021944625703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439123193624681296417135 658684790437021944625703)
          ·
            refine ⟨988027185655532916938555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658684790437021944625703 988027185655532916938555)
            ·
              refine ⟨1482040778483299375407833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988027185655532916938555 1482040778483299375407833)
              ·
                refine ⟨1111530583862474531555875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482040778483299375407833 1111530583862474531555875)
                ·
                  refine ⟨1667295875793711797333813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111530583862474531555875 1667295875793711797333813)
                  ·
                    refine ⟨156308988355660481000045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1667295875793711797333813 156308988355660481000045)
                    ·
                      rfl

theorem cell22_456616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_456616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456616 prefixEnd_456616 := by exact prefixLift 456616
  have htrace : WordTrace (prefixWord ++ tailWord_456616) baseStart_456616 baseEnd_456616 := by
    simpa [prefixWord, tailWord_456616, baseEnd_456616] using wordTrace_append hprefix tailTrace_456616
  have hstable : (prefixWord ++ tailWord_456616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456616).length < 2 ^ (prefixWord ++ tailWord_456616).sum := by decide
  have hdescent : baseEnd_456616 < baseStart_456616 := by decide
  rcases family_descends (prefixWord ++ tailWord_456616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456708 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 5]
def baseStart_456708 : Nat := 118140960795 + 456708 * 2 ^ 59
def prefixEnd_456708 : Nat := 4983230072969 + 3 ^ 40 * 456708 * 2
def baseEnd_456708 : Nat := 52113493945267635899921

theorem tailTrace_456708 : CollatzResearch.WordTrace tailWord_456708 prefixEnd_456708 52113493945267635899921 := by
  unfold tailWord_456708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328754614716195180825389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11105006152954926907767185 8328754614716195180825389)
  ·
    refine ⟨3123282980518573192809521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8328754614716195180825389 3123282980518573192809521)
    ·
      refine ⟨2342462235388929894607141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3123282980518573192809521 2342462235388929894607141)
      ·
        refine ⟨439211669135424355238839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2342462235388929894607141 439211669135424355238839)
        ·
          refine ⟨658817503703136532858259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439211669135424355238839 658817503703136532858259)
          ·
            refine ⟨988226255554704799287389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658817503703136532858259 988226255554704799287389)
            ·
              refine ⟨370584845833014299732771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 988226255554704799287389 370584845833014299732771)
              ·
                refine ⟨555877268749521449599157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370584845833014299732771 555877268749521449599157)
                ·
                  refine ⟨52113493945267635899921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 555877268749521449599157 52113493945267635899921)
                  ·
                    rfl

theorem cell22_456708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_456708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456708 prefixEnd_456708 := by exact prefixLift 456708
  have htrace : WordTrace (prefixWord ++ tailWord_456708) baseStart_456708 baseEnd_456708 := by
    simpa [prefixWord, tailWord_456708, baseEnd_456708] using wordTrace_append hprefix tailTrace_456708
  have hstable : (prefixWord ++ tailWord_456708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456708).length < 2 ^ (prefixWord ++ tailWord_456708).sum := by decide
  have hdescent : baseEnd_456708 < baseStart_456708 := by decide
  rcases family_descends (prefixWord ++ tailWord_456708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456768 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 2, 3]
def baseStart_456768 : Nat := 118140960795 + 456768 * 2 ^ 59
def prefixEnd_456768 : Nat := 4983230072969 + 3 ^ 40 * 456768 * 2
def baseEnd_456768 : Nat := 156361021061982751199579

theorem tailTrace_456768 : CollatzResearch.WordTrace tailWord_456768 prefixEnd_456768 156361021061982751199579 := by
  unfold tailWord_456768
  simp only [CollatzResearch.WordTrace]
  refine ⟨8329848804607510304417479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11106465072810013739223305 8329848804607510304417479)
  ·
    refine ⟨12494773206911265456626219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8329848804607510304417479 12494773206911265456626219)
    ·
      refine ⟨18742159810366898184939329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12494773206911265456626219 18742159810366898184939329)
      ·
        refine ⟨14056619857775173638704497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18742159810366898184939329 14056619857775173638704497)
        ·
          refine ⟨10542464893331380229028373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14056619857775173638704497 10542464893331380229028373)
          ·
            refine ⟨494178041874908448235705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10542464893331380229028373 494178041874908448235705)
            ·
              refine ⟨370633531406181336176779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494178041874908448235705 370633531406181336176779)
              ·
                refine ⟨555950297109272004265169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370633531406181336176779 555950297109272004265169)
                ·
                  refine ⟨416962722831954003198877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555950297109272004265169 416962722831954003198877)
                  ·
                    refine ⟨156361021061982751199579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416962722831954003198877 156361021061982751199579)
                    ·
                      rfl

theorem cell22_456768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_456768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456768 prefixEnd_456768 := by exact prefixLift 456768
  have htrace : WordTrace (prefixWord ++ tailWord_456768) baseStart_456768 baseEnd_456768 := by
    simpa [prefixWord, tailWord_456768, baseEnd_456768] using wordTrace_append hprefix tailTrace_456768
  have hstable : (prefixWord ++ tailWord_456768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456768).length < 2 ^ (prefixWord ++ tailWord_456768).sum := by decide
  have hdescent : baseEnd_456768 < baseStart_456768 := by decide
  rcases family_descends (prefixWord ++ tailWord_456768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456798 : List Nat := [4, 4, 1, 1, 3, 9]
def baseStart_456798 : Nat := 118140960795 + 456798 * 2 ^ 59
def prefixEnd_456798 : Nat := 4983230072969 + 3 ^ 40 * 456798 * 2
def baseEnd_456798 : Nat := 1930509761420650283327

theorem tailTrace_456798 : CollatzResearch.WordTrace tailWord_456798 prefixEnd_456798 1930509761420650283327 := by
  unfold tailWord_456798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082598974888291966553381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11107194532737557154951365 2082598974888291966553381)
  ·
    refine ⟨390487307791554743728759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2082598974888291966553381 390487307791554743728759)
    ·
      refine ⟨585730961687332115593139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390487307791554743728759 585730961687332115593139)
      ·
        refine ⟨878596442530998173389709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585730961687332115593139 878596442530998173389709)
        ·
          refine ⟨329473665949124315021141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878596442530998173389709 329473665949124315021141)
          ·
            refine ⟨1930509761420650283327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 329473665949124315021141 1930509761420650283327)
            ·
              rfl

theorem cell22_456798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 9].length) (baseStart_456798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456798 prefixEnd_456798 := by exact prefixLift 456798
  have htrace : WordTrace (prefixWord ++ tailWord_456798) baseStart_456798 baseEnd_456798 := by
    simpa [prefixWord, tailWord_456798, baseEnd_456798] using wordTrace_append hprefix tailTrace_456798
  have hstable : (prefixWord ++ tailWord_456798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456798).length < 2 ^ (prefixWord ++ tailWord_456798).sum := by decide
  have hdescent : baseEnd_456798 < baseStart_456798 := by decide
  rcases family_descends (prefixWord ++ tailWord_456798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456809 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 5]
def baseStart_456809 : Nat := 118140960795 + 456809 * 2 ^ 59
def prefixEnd_456809 : Nat := 4983230072969 + 3 ^ 40 * 456809 * 2
def baseEnd_456809 : Nat := 52125018733290770308151

theorem tailTrace_456809 : CollatzResearch.WordTrace tailWord_456809 prefixEnd_456809 52125018733290770308151 := by
  unfold tailWord_456809
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661193002066484611077481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11107462001377656407384987 16661193002066484611077481)
  ·
    refine ⟨12495894751549863458308111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16661193002066484611077481 12495894751549863458308111)
    ·
      refine ⟨18743842127324795187462167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12495894751549863458308111 18743842127324795187462167)
      ·
        refine ⟨28115763190987192781193251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18743842127324795187462167 28115763190987192781193251)
        ·
          refine ⟨42173644786480789171789877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28115763190987192781193251 42173644786480789171789877)
          ·
            refine ⟨3953779198732573984855301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42173644786480789171789877 3953779198732573984855301)
            ·
              refine ⟨741333599762357622160369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3953779198732573984855301 741333599762357622160369)
              ·
                refine ⟨556000199821768216620277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741333599762357622160369 556000199821768216620277)
                ·
                  refine ⟨52125018733290770308151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 556000199821768216620277 52125018733290770308151)
                  ·
                    rfl

theorem cell22_456809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_456809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456809 prefixEnd_456809 := by exact prefixLift 456809
  have htrace : WordTrace (prefixWord ++ tailWord_456809) baseStart_456809 baseEnd_456809 := by
    simpa [prefixWord, tailWord_456809, baseEnd_456809] using wordTrace_append hprefix tailTrace_456809
  have hstable : (prefixWord ++ tailWord_456809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456809).length < 2 ^ (prefixWord ++ tailWord_456809).sum := by decide
  have hdescent : baseEnd_456809 < baseStart_456809 := by decide
  rcases family_descends (prefixWord ++ tailWord_456809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456813 : List Nat := [1, 5, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_456813 : Nat := 118140960795 + 456813 * 2 ^ 59
def prefixEnd_456813 : Nat := 4983230072969 + 3 ^ 40 * 456813 * 2
def baseEnd_456813 : Nat := 156376425481617633824441

theorem tailTrace_456813 : CollatzResearch.WordTrace tailWord_456813 prefixEnd_456813 156376425481617633824441 := by
  unfold tailWord_456813
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661338894051993294223093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11107559262701328862815395 16661338894051993294223093)
  ·
    refine ⟨1562000521317374371333415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16661338894051993294223093 1562000521317374371333415)
    ·
      refine ⟨2343000781976061557000123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562000521317374371333415 2343000781976061557000123)
      ·
        refine ⟨3514501172964092335500185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343000781976061557000123 3514501172964092335500185)
        ·
          refine ⟨2635875879723069251625139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514501172964092335500185 2635875879723069251625139)
          ·
            refine ⟨3953813819584603877437709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635875879723069251625139 3953813819584603877437709)
            ·
              refine ⟨1482680182344226454039141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3953813819584603877437709 1482680182344226454039141)
              ·
                refine ⟨278002534189542460132339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1482680182344226454039141 278002534189542460132339)
                ·
                  refine ⟨417003801284313690198509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278002534189542460132339 417003801284313690198509)
                  ·
                    refine ⟨156376425481617633824441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417003801284313690198509 156376425481617633824441)
                    ·
                      rfl

theorem cell22_456813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_456813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456813 prefixEnd_456813 := by exact prefixLift 456813
  have htrace : WordTrace (prefixWord ++ tailWord_456813) baseStart_456813 baseEnd_456813 := by
    simpa [prefixWord, tailWord_456813, baseEnd_456813] using wordTrace_append hprefix tailTrace_456813
  have hstable : (prefixWord ++ tailWord_456813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456813).length < 2 ^ (prefixWord ++ tailWord_456813).sum := by decide
  have hdescent : baseEnd_456813 < baseStart_456813 := by decide
  rcases family_descends (prefixWord ++ tailWord_456813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456839 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 3, 4]
def baseStart_456839 : Nat := 118140960795 + 456839 * 2 ^ 59
def prefixEnd_456839 : Nat := 4983230072969 + 3 ^ 40 * 456839 * 2
def baseEnd_456839 : Nat := 156385325812962232674361

theorem tailTrace_456839 : CollatzResearch.WordTrace tailWord_456839 prefixEnd_456839 156385325812962232674361 := by
  unfold tailWord_456839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662287191957799734669571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11108191461305199823113047 16662287191957799734669571)
  ·
    refine ⟨24993430787936699602004357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16662287191957799734669571 24993430787936699602004357)
    ·
      refine ⟨4686268272738131175375817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24993430787936699602004357 4686268272738131175375817)
      ·
        refine ⟨3514701204553598381531863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4686268272738131175375817 3514701204553598381531863)
        ·
          refine ⟨5272051806830397572297795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514701204553598381531863 5272051806830397572297795)
          ·
            refine ⟨7908077710245596358446693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272051806830397572297795 7908077710245596358446693)
            ·
              refine ⟨1482764570671049317208755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7908077710245596358446693 1482764570671049317208755)
              ·
                refine ⟨2224146856006573975813133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482764570671049317208755 2224146856006573975813133)
                ·
                  refine ⟨834055071002465240929925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2224146856006573975813133 834055071002465240929925)
                  ·
                    refine ⟨156385325812962232674361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 834055071002465240929925 156385325812962232674361)
                    ·
                      rfl

theorem cell22_456839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_456839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456839 prefixEnd_456839 := by exact prefixLift 456839
  have htrace : WordTrace (prefixWord ++ tailWord_456839) baseStart_456839 baseEnd_456839 := by
    simpa [prefixWord, tailWord_456839, baseEnd_456839] using wordTrace_append hprefix tailTrace_456839
  have hstable : (prefixWord ++ tailWord_456839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456839).length < 2 ^ (prefixWord ++ tailWord_456839).sum := by decide
  have hdescent : baseEnd_456839 < baseStart_456839 := by decide
  rcases family_descends (prefixWord ++ tailWord_456839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456918 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_456918 : Nat := 118140960795 + 456918 * 2 ^ 59
def prefixEnd_456918 : Nat := 4983230072969 + 3 ^ 40 * 456918 * 2
def baseEnd_456918 : Nat := 156412369127432359949119

theorem tailTrace_456918 : CollatzResearch.WordTrace tailWord_456918 prefixEnd_456918 156412369127432359949119 := by
  unfold tailWord_456918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041573034916974764174713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11110112372447730817863605 1041573034916974764174713)
  ·
    refine ⟨781179776187731073131035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1041573034916974764174713 781179776187731073131035)
    ·
      refine ⟨1171769664281596609696553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781179776187731073131035 1171769664281596609696553)
      ·
        refine ⟨878827248211197457272415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171769664281596609696553 878827248211197457272415)
        ·
          refine ⟨1318240872316796185908623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878827248211197457272415 1318240872316796185908623)
          ·
            refine ⟨1977361308475194278862935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318240872316796185908623 1977361308475194278862935)
            ·
              refine ⟨2966041962712791418294403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977361308475194278862935 2966041962712791418294403)
              ·
                refine ⟨4449062944069187127441605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966041962712791418294403 4449062944069187127441605)
                ·
                  refine ⟨834199302012972586395301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4449062944069187127441605 834199302012972586395301)
                  ·
                    refine ⟨156412369127432359949119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 834199302012972586395301 156412369127432359949119)
                    ·
                      rfl

theorem cell22_456918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_456918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456918 prefixEnd_456918 := by exact prefixLift 456918
  have htrace : WordTrace (prefixWord ++ tailWord_456918) baseStart_456918 baseEnd_456918 := by
    simpa [prefixWord, tailWord_456918, baseEnd_456918] using wordTrace_append hprefix tailTrace_456918
  have hstable : (prefixWord ++ tailWord_456918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456918).length < 2 ^ (prefixWord ++ tailWord_456918).sum := by decide
  have hdescent : baseEnd_456918 < baseStart_456918 := by decide
  rcases family_descends (prefixWord ++ tailWord_456918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456929 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_456929 : Nat := 118140960795 + 456929 * 2 ^ 59
def prefixEnd_456929 : Nat := 4983230072969 + 3 ^ 40 * 456929 * 2
def baseEnd_456929 : Nat := 156416134652231997924085

theorem tailTrace_456929 : CollatzResearch.WordTrace tailWord_456929 prefixEnd_456929 156416134652231997924085 := by
  unfold tailWord_456929
  simp only [CollatzResearch.WordTrace]
  refine ⟨16665569761631745105445841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11110379841087830070297227 16665569761631745105445841)
  ·
    refine ⟨12499177321223808829084381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16665569761631745105445841 12499177321223808829084381)
    ·
      refine ⟨4687191495458928310906643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12499177321223808829084381 4687191495458928310906643)
      ·
        refine ⟨7030787243188392466359965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4687191495458928310906643 7030787243188392466359965)
        ·
          refine ⟨2636545216195647174884987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7030787243188392466359965 2636545216195647174884987)
          ·
            refine ⟨3954817824293470762327481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636545216195647174884987 3954817824293470762327481)
            ·
              refine ⟨2966113368220103071745611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954817824293470762327481 2966113368220103071745611)
              ·
                refine ⟨4449170052330154607618417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966113368220103071745611 4449170052330154607618417)
                ·
                  refine ⟨3336877539247615955713813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449170052330154607618417 3336877539247615955713813)
                  ·
                    refine ⟨156416134652231997924085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3336877539247615955713813 156416134652231997924085)
                    ·
                      rfl

theorem cell22_456929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_456929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456929 prefixEnd_456929 := by exact prefixLift 456929
  have htrace : WordTrace (prefixWord ++ tailWord_456929) baseStart_456929 baseEnd_456929 := by
    simpa [prefixWord, tailWord_456929, baseEnd_456929] using wordTrace_append hprefix tailTrace_456929
  have hstable : (prefixWord ++ tailWord_456929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456929).length < 2 ^ (prefixWord ++ tailWord_456929).sum := by decide
  have hdescent : baseEnd_456929 < baseStart_456929 := by decide
  rcases family_descends (prefixWord ++ tailWord_456929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456991 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 3, 4]
def baseStart_456991 : Nat := 118140960795 + 456991 * 2 ^ 59
def prefixEnd_456991 : Nat := 4983230072969 + 3 ^ 40 * 456991 * 2
def baseEnd_456991 : Nat := 156437358519284502873895

theorem tailTrace_456991 : CollatzResearch.WordTrace tailWord_456991 prefixEnd_456991 156437358519284502873895 := by
  unfold tailWord_456991
  simp only [CollatzResearch.WordTrace]
  refine ⟨16667831087407129694202827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11111887391604753129468551 16667831087407129694202827)
  ·
    refine ⟨25001746631110694541304241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16667831087407129694202827 25001746631110694541304241)
    ·
      refine ⟨18751309973333020905978181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25001746631110694541304241 18751309973333020905978181)
      ·
        refine ⟨3515870619999941419870909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18751309973333020905978181 3515870619999941419870909)
        ·
          refine ⟨1318451482499978032451591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3515870619999941419870909 1318451482499978032451591)
          ·
            refine ⟨1977677223749967048677387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318451482499978032451591 1977677223749967048677387)
            ·
              refine ⟨2966515835624950573016081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977677223749967048677387 2966515835624950573016081)
              ·
                refine ⟨2224886876718712929762061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966515835624950573016081 2224886876718712929762061)
                ·
                  refine ⟨834332578769517348660773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2224886876718712929762061 834332578769517348660773)
                  ·
                    refine ⟨156437358519284502873895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 834332578769517348660773 156437358519284502873895)
                    ·
                      rfl

theorem cell22_456991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_456991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_456991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_456991 prefixEnd_456991 := by exact prefixLift 456991
  have htrace : WordTrace (prefixWord ++ tailWord_456991) baseStart_456991 baseEnd_456991 := by
    simpa [prefixWord, tailWord_456991, baseEnd_456991] using wordTrace_append hprefix tailTrace_456991
  have hstable : (prefixWord ++ tailWord_456991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456991).length < 2 ^ (prefixWord ++ tailWord_456991).sum := by decide
  have hdescent : baseEnd_456991 < baseStart_456991 := by decide
  rcases family_descends (prefixWord ++ tailWord_456991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457023 : List Nat := [1, 1, 2, 2, 4, 1, 4, 3, 4]
def baseStart_457023 : Nat := 118140960795 + 457023 * 2 ^ 59
def prefixEnd_457023 : Nat := 4983230072969 + 3 ^ 40 * 457023 * 2
def baseEnd_457023 : Nat := 52149437591082362024599

theorem tailTrace_457023 : CollatzResearch.WordTrace tailWord_457023 prefixEnd_457023 52149437591082362024599 := by
  unfold tailWord_457023
  simp only [CollatzResearch.WordTrace]
  refine ⟨16668998223291199159367723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11112665482194132772911815 16668998223291199159367723)
  ·
    refine ⟨25003497334936798739051585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16668998223291199159367723 25003497334936798739051585)
    ·
      refine ⟨18752623001202599054288689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25003497334936798739051585 18752623001202599054288689)
      ·
        refine ⟨14064467250901949290716517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18752623001202599054288689 14064467250901949290716517)
        ·
          refine ⟨2637087609544115492009347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14064467250901949290716517 2637087609544115492009347)
          ·
            refine ⟨3955631414316173238014021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637087609544115492009347 3955631414316173238014021)
            ·
              refine ⟨741680890184282482127629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3955631414316173238014021 741680890184282482127629)
              ·
                refine ⟨278130333819105930797861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 741680890184282482127629 278130333819105930797861)
                ·
                  refine ⟨52149437591082362024599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278130333819105930797861 52149437591082362024599)
                  ·
                    rfl

theorem cell22_457023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 4].length) (baseStart_457023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457023 prefixEnd_457023 := by exact prefixLift 457023
  have htrace : WordTrace (prefixWord ++ tailWord_457023) baseStart_457023 baseEnd_457023 := by
    simpa [prefixWord, tailWord_457023, baseEnd_457023] using wordTrace_append hprefix tailTrace_457023
  have hstable : (prefixWord ++ tailWord_457023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457023).length < 2 ^ (prefixWord ++ tailWord_457023).sum := by decide
  have hdescent : baseEnd_457023 < baseStart_457023 := by decide
  rcases family_descends (prefixWord ++ tailWord_457023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457025 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_457025 : Nat := 118140960795 + 457025 * 2 ^ 59
def prefixEnd_457025 : Nat := 4983230072969 + 3 ^ 40 * 457025 * 2
def baseEnd_457025 : Nat := 156448997414119747523791

theorem tailTrace_457025 : CollatzResearch.WordTrace tailWord_457025 prefixEnd_457025 156448997414119747523791 := by
  unfold tailWord_457025
  simp only [CollatzResearch.WordTrace]
  refine ⟨16669071169283953500940529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11112714112855969000627019 16669071169283953500940529)
  ·
    refine ⟨12501803376962965125705397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16669071169283953500940529 12501803376962965125705397)
    ·
      refine ⟨1172044066590277980534881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12501803376962965125705397 1172044066590277980534881)
      ·
        refine ⟨879033049942708485401161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1172044066590277980534881 879033049942708485401161)
        ·
          refine ⟨659274787457031364050871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 879033049942708485401161 659274787457031364050871)
          ·
            refine ⟨988912181185547046076307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659274787457031364050871 988912181185547046076307)
            ·
              refine ⟨1483368271778320569114461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988912181185547046076307 1483368271778320569114461)
              ·
                refine ⟨556263101916870213417923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1483368271778320569114461 556263101916870213417923)
                ·
                  refine ⟨834394652875305320126885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556263101916870213417923 834394652875305320126885)
                  ·
                    refine ⟨156448997414119747523791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 834394652875305320126885 156448997414119747523791)
                    ·
                      rfl

theorem cell22_457025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_457025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457025 prefixEnd_457025 := by exact prefixLift 457025
  have htrace : WordTrace (prefixWord ++ tailWord_457025) baseStart_457025 baseEnd_457025 := by
    simpa [prefixWord, tailWord_457025, baseEnd_457025] using wordTrace_append hprefix tailTrace_457025
  have hstable : (prefixWord ++ tailWord_457025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457025).length < 2 ^ (prefixWord ++ tailWord_457025).sum := by decide
  have hdescent : baseEnd_457025 < baseStart_457025 := by decide
  rcases family_descends (prefixWord ++ tailWord_457025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457036 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_457036 : Nat := 118140960795 + 457036 * 2 ^ 59
def prefixEnd_457036 : Nat := 4983230072969 + 3 ^ 40 * 457036 * 2
def baseEnd_457036 : Nat := 156452762938919385498757

theorem tailTrace_457036 : CollatzResearch.WordTrace tailWord_457036 prefixEnd_457036 156452762938919385498757 := by
  unfold tailWord_457036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334736186122051189795481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11112981581496068253060641 8334736186122051189795481)
  ·
    refine ⟨6251052139591538392346611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8334736186122051189795481 6251052139591538392346611)
    ·
      refine ⟨9376578209387307588519917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251052139591538392346611 9376578209387307588519917)
      ·
        refine ⟨3516216828520240345694969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9376578209387307588519917 3516216828520240345694969)
        ·
          refine ⟨2637162621390180259271227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3516216828520240345694969 2637162621390180259271227)
          ·
            refine ⟨3955743932085270388906841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637162621390180259271227 3955743932085270388906841)
            ·
              refine ⟨2966807949063952791680131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3955743932085270388906841 2966807949063952791680131)
              ·
                refine ⟨4450211923595929187520197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966807949063952791680131 4450211923595929187520197)
                ·
                  refine ⟨834414735674236722660037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4450211923595929187520197 834414735674236722660037)
                  ·
                    refine ⟨156452762938919385498757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 834414735674236722660037 156452762938919385498757)
                    ·
                      rfl

theorem cell22_457036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_457036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457036 prefixEnd_457036 := by exact prefixLift 457036
  have htrace : WordTrace (prefixWord ++ tailWord_457036) baseStart_457036 baseEnd_457036 := by
    simpa [prefixWord, tailWord_457036, baseEnd_457036] using wordTrace_append hprefix tailTrace_457036
  have hstable : (prefixWord ++ tailWord_457036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457036).length < 2 ^ (prefixWord ++ tailWord_457036).sum := by decide
  have hdescent : baseEnd_457036 < baseStart_457036 := by decide
  rcases family_descends (prefixWord ++ tailWord_457036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457038 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_457038 : Nat := 118140960795 + 457038 * 2 ^ 59
def prefixEnd_457038 : Nat := 4983230072969 + 3 ^ 40 * 457038 * 2
def baseEnd_457038 : Nat := 156453447579792046948751

theorem tailTrace_457038 : CollatzResearch.WordTrace tailWord_457038 prefixEnd_457038 156453447579792046948751 := by
  unfold tailWord_457038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083693164779607090145471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11113030212157904480775845 2083693164779607090145471)
  ·
    refine ⟨3125539747169410635218207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2083693164779607090145471 3125539747169410635218207)
    ·
      refine ⟨4688309620754115952827311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3125539747169410635218207 4688309620754115952827311)
      ·
        refine ⟨7032464431131173929240967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4688309620754115952827311 7032464431131173929240967)
        ·
          refine ⟨10548696646696760893861451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7032464431131173929240967 10548696646696760893861451)
          ·
            refine ⟨15823044970045141340792177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10548696646696760893861451 15823044970045141340792177)
            ·
              refine ⟨11867283727533856005594133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15823044970045141340792177 11867283727533856005594133)
              ·
                refine ⟨556278924728149500262225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11867283727533856005594133 556278924728149500262225)
                ·
                  refine ⟨417209193546112125196669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556278924728149500262225 417209193546112125196669)
                  ·
                    refine ⟨156453447579792046948751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417209193546112125196669 156453447579792046948751)
                    ·
                      rfl

theorem cell22_457038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_457038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457038 prefixEnd_457038 := by exact prefixLift 457038
  have htrace : WordTrace (prefixWord ++ tailWord_457038) baseStart_457038 baseEnd_457038 := by
    simpa [prefixWord, tailWord_457038, baseEnd_457038] using wordTrace_append hprefix tailTrace_457038
  have hstable : (prefixWord ++ tailWord_457038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457038).length < 2 ^ (prefixWord ++ tailWord_457038).sum := by decide
  have hdescent : baseEnd_457038 < baseStart_457038 := by decide
  rcases family_descends (prefixWord ++ tailWord_457038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457096 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 7]
def baseStart_457096 : Nat := 118140960795 + 457096 * 2 ^ 59
def prefixEnd_457096 : Nat := 4983230072969 + 3 ^ 40 * 457096 * 2
def baseEnd_457096 : Nat := 52157767388366409666191

theorem tailTrace_457096 : CollatzResearch.WordTrace tailWord_457096 prefixEnd_457096 52157767388366409666191 := by
  unfold tailWord_457096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8335830376013366313387571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11114440501351155084516761 8335830376013366313387571)
  ·
    refine ⟨12503745564020049470081357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8335830376013366313387571 12503745564020049470081357)
    ·
      refine ⟨4688904586507518551280509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12503745564020049470081357 4688904586507518551280509)
      ·
        refine ⟨1758339219940319456730191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4688904586507518551280509 1758339219940319456730191)
        ·
          refine ⟨2637508829910479185095287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758339219940319456730191 2637508829910479185095287)
          ·
            refine ⟨3956263244865718777642931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637508829910479185095287 3956263244865718777642931)
            ·
              refine ⟨5934394867298578166464397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956263244865718777642931 5934394867298578166464397)
              ·
                refine ⟨2225398075236966812424149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5934394867298578166464397 2225398075236966812424149)
                ·
                  refine ⟨52157767388366409666191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2225398075236966812424149 52157767388366409666191)
                  ·
                    rfl

theorem cell22_457096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_457096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457096 prefixEnd_457096 := by exact prefixLift 457096
  have htrace : WordTrace (prefixWord ++ tailWord_457096) baseStart_457096 baseEnd_457096 := by
    simpa [prefixWord, tailWord_457096, baseEnd_457096] using wordTrace_append hprefix tailTrace_457096
  have hstable : (prefixWord ++ tailWord_457096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457096).length < 2 ^ (prefixWord ++ tailWord_457096).sum := by decide
  have hdescent : baseEnd_457096 < baseStart_457096 := by decide
  rcases family_descends (prefixWord ++ tailWord_457096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457100 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_457100 : Nat := 118140960795 + 457100 * 2 ^ 59
def prefixEnd_457100 : Nat := 4983230072969 + 3 ^ 40 * 457100 * 2
def baseEnd_457100 : Nat := 156474671446844551898561

theorem tailTrace_457100 : CollatzResearch.WordTrace tailWord_457100 prefixEnd_457100 156474671446844551898561 := by
  unfold tailWord_457100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8335903322006120654960377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11114537762674827539947169 8335903322006120654960377)
  ·
    refine ⟨6251927491504590491220283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8335903322006120654960377 6251927491504590491220283)
    ·
      refine ⟨9377891237256885736830425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251927491504590491220283 9377891237256885736830425)
      ·
        refine ⟨7033418427942664302622819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9377891237256885736830425 7033418427942664302622819)
        ·
          refine ⟨10550127641913996453934229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033418427942664302622819 10550127641913996453934229)
          ·
            refine ⟨494537233214718583778167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10550127641913996453934229 494537233214718583778167)
            ·
              refine ⟨741805849822077875667251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494537233214718583778167 741805849822077875667251)
              ·
                refine ⟨1112708774733116813500877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741805849822077875667251 1112708774733116813500877)
                ·
                  refine ⟨417265790524918805062829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112708774733116813500877 417265790524918805062829)
                  ·
                    refine ⟨156474671446844551898561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417265790524918805062829 156474671446844551898561)
                    ·
                      rfl

theorem cell22_457100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_457100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457100 prefixEnd_457100 := by exact prefixLift 457100
  have htrace : WordTrace (prefixWord ++ tailWord_457100) baseStart_457100 baseEnd_457100 := by
    simpa [prefixWord, tailWord_457100, baseEnd_457100] using wordTrace_append hprefix tailTrace_457100
  have hstable : (prefixWord ++ tailWord_457100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457100).length < 2 ^ (prefixWord ++ tailWord_457100).sum := by decide
  have hdescent : baseEnd_457100 < baseStart_457100 := by decide
  rcases family_descends (prefixWord ++ tailWord_457100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457111 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 2, 5]
def baseStart_457111 : Nat := 118140960795 + 457111 * 2 ^ 59
def prefixEnd_457111 : Nat := 4983230072969 + 3 ^ 40 * 457111 * 2
def baseEnd_457111 : Nat := 156478436971644189873527

theorem tailTrace_457111 : CollatzResearch.WordTrace tailWord_457111 prefixEnd_457111 156478436971644189873527 := by
  unfold tailWord_457111
  simp only [CollatzResearch.WordTrace]
  refine ⟨16672207846972390188571187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11114805231314926792380791 16672207846972390188571187)
  ·
    refine ⟨25008311770458585282856781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16672207846972390188571187 25008311770458585282856781)
    ·
      refine ⟨9378116913921969481071293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25008311770458585282856781 9378116913921969481071293)
      ·
        refine ⟨3516793842720738555401735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9378116913921969481071293 3516793842720738555401735)
        ·
          refine ⟨5275190764081107833102603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516793842720738555401735 5275190764081107833102603)
          ·
            refine ⟨7912786146121661749653905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275190764081107833102603 7912786146121661749653905)
            ·
              refine ⟨5934589609591246312240429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912786146121661749653905 5934589609591246312240429)
              ·
                refine ⟨2225471103596717367090161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5934589609591246312240429 2225471103596717367090161)
                ·
                  refine ⟨1669103327697538025317621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225471103596717367090161 1669103327697538025317621)
                  ·
                    refine ⟨156478436971644189873527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1669103327697538025317621 156478436971644189873527)
                    ·
                      rfl

theorem cell22_457111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_457111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457111 prefixEnd_457111 := by exact prefixLift 457111
  have htrace : WordTrace (prefixWord ++ tailWord_457111) baseStart_457111 baseEnd_457111 := by
    simpa [prefixWord, tailWord_457111, baseEnd_457111] using wordTrace_append hprefix tailTrace_457111
  have hstable : (prefixWord ++ tailWord_457111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457111).length < 2 ^ (prefixWord ++ tailWord_457111).sum := by decide
  have hdescent : baseEnd_457111 < baseStart_457111 := by decide
  rcases family_descends (prefixWord ++ tailWord_457111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
