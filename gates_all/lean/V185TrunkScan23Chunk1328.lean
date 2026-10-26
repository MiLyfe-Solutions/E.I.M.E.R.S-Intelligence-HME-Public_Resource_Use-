import V185TrunkScan23Chunk1327

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7866293 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_7866293 : Nat := 118140960795 + 7866293 * 2 ^ 59
def prefixEnd_7866293 : Nat := 4983230072969 + 3 ^ 40 * 7866293 * 2
def baseEnd_7866293 : Nat := 4039189278098096826161083

theorem tailTrace_7866293 : CollatzResearch.WordTrace tailWord_7866293 prefixEnd_7866293 4039189278098096826161083 := by
  unfold tailWord_7866293
  simp only [CollatzResearch.WordTrace]
  refine ⟨286907276090771391731523533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191271517393847594487682355 286907276090771391731523533)
  ·
    refine ⟨107590228534039271899321325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286907276090771391731523533 107590228534039271899321325)
    ·
      refine ⟨40346335700264726962245497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107590228534039271899321325 40346335700264726962245497)
      ·
        refine ⟨30259751775198545221684123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40346335700264726962245497 30259751775198545221684123)
        ·
          refine ⟨45389627662797817832526185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30259751775198545221684123 45389627662797817832526185)
          ·
            refine ⟨34042220747098363374394639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45389627662797817832526185 34042220747098363374394639)
            ·
              refine ⟨51063331120647545061591959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34042220747098363374394639 51063331120647545061591959)
              ·
                refine ⟨76594996680971317592387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51063331120647545061591959 76594996680971317592387939)
                ·
                  refine ⟨114892495021456976388581909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76594996680971317592387939 114892495021456976388581909)
                  ·
                    refine ⟨5385585704130795768214777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114892495021456976388581909 5385585704130795768214777)
                    ·
                      refine ⟨4039189278098096826161083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385585704130795768214777 4039189278098096826161083)
                      ·
                        rfl

theorem cell23_7866293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_7866293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866293 prefixEnd_7866293 := by exact prefixLift 7866293
  have htrace : WordTrace (prefixWord ++ tailWord_7866293) baseStart_7866293 baseEnd_7866293 := by
    simpa [prefixWord, tailWord_7866293, baseEnd_7866293] using wordTrace_append hprefix tailTrace_7866293
  have hstable : (prefixWord ++ tailWord_7866293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866293).length < 2 ^ (prefixWord ++ tailWord_7866293).sum := by decide
  have hdescent : baseEnd_7866293 < baseStart_7866293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866296 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_7866296 : Nat := 118140960795 + 7866296 * 2 ^ 59
def prefixEnd_7866296 : Nat := 4983230072969 + 3 ^ 40 * 7866296 * 2
def baseEnd_7866296 : Nat := 4039190818540060314423569

theorem tailTrace_7866296 : CollatzResearch.WordTrace tailWord_7866296 prefixEnd_7866296 4039190818540060314423569 := by
  unfold tailWord_7866296
  simp only [CollatzResearch.WordTrace]
  refine ⟨143453692754880261621941371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191271590339840348829255161 143453692754880261621941371)
  ·
    refine ⟨215180539132320392432912057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143453692754880261621941371 215180539132320392432912057)
    ·
      refine ⟨161385404349240294324684043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215180539132320392432912057 161385404349240294324684043)
      ·
        refine ⟨242078106523860441487026065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161385404349240294324684043 242078106523860441487026065)
        ·
          refine ⟨181558579892895331115269549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242078106523860441487026065 181558579892895331115269549)
          ·
            refine ⟨68084467459835749168226081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181558579892895331115269549 68084467459835749168226081)
            ·
              refine ⟨51063350594876811876169561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68084467459835749168226081 51063350594876811876169561)
              ·
                refine ⟨38297512946157608907127171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51063350594876811876169561 38297512946157608907127171)
                ·
                  refine ⟨57446269419236413360690757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38297512946157608907127171 57446269419236413360690757)
                  ·
                    refine ⟨10771175516106827505129517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57446269419236413360690757 10771175516106827505129517)
                    ·
                      refine ⟨4039190818540060314423569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10771175516106827505129517 4039190818540060314423569)
                      ·
                        rfl

theorem cell23_7866296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_7866296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866296 prefixEnd_7866296 := by exact prefixLift 7866296
  have htrace : WordTrace (prefixWord ++ tailWord_7866296) baseStart_7866296 baseEnd_7866296 := by
    simpa [prefixWord, tailWord_7866296, baseEnd_7866296] using wordTrace_append hprefix tailTrace_7866296
  have hstable : (prefixWord ++ tailWord_7866296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866296).length < 2 ^ (prefixWord ++ tailWord_7866296).sum := by decide
  have hdescent : baseEnd_7866296 < baseStart_7866296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866333 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 8]
def baseStart_7866333 : Nat := 118140960795 + 7866333 * 2 ^ 59
def prefixEnd_7866333 : Nat := 4983230072969 + 3 ^ 40 * 7866333 * 2
def baseEnd_7866333 : Nat := 448801090813808518851211

theorem tailTrace_7866333 : CollatzResearch.WordTrace tailWord_7866333 prefixEnd_7866333 448801090813808518851211 := by
  unfold tailWord_7866333
  simp only [CollatzResearch.WordTrace]
  refine ⟨286908735010626478562979653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191272490007084319041986435 286908735010626478562979653)
  ·
    refine ⟨53795387814492464730558685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286908735010626478562979653 53795387814492464730558685)
    ·
      refine ⟨20173270430434674273959507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53795387814492464730558685 20173270430434674273959507)
      ·
        refine ⟨30259905645652011410939261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20173270430434674273959507 30259905645652011410939261)
        ·
          refine ⟨11347464617119504279102223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30259905645652011410939261 11347464617119504279102223)
          ·
            refine ⟨17021196925679256418653335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11347464617119504279102223 17021196925679256418653335)
            ·
              refine ⟨25531795388518884627980003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17021196925679256418653335 25531795388518884627980003)
              ·
                refine ⟨38297693082778326941970005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25531795388518884627980003 38297693082778326941970005)
                ·
                  refine ⟨448801090813808518851211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38297693082778326941970005 448801090813808518851211)
                  ·
                    rfl

theorem cell23_7866333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_7866333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866333 prefixEnd_7866333 := by exact prefixLift 7866333
  have htrace : WordTrace (prefixWord ++ tailWord_7866333) baseStart_7866333 baseEnd_7866333 := by
    simpa [prefixWord, tailWord_7866333, baseEnd_7866333] using wordTrace_append hprefix tailTrace_7866333
  have hstable : (prefixWord ++ tailWord_7866333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866333).length < 2 ^ (prefixWord ++ tailWord_7866333).sum := by decide
  have hdescent : baseEnd_7866333 < baseStart_7866333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866350 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_7866350 : Nat := 118140960795 + 7866350 * 2 ^ 59
def prefixEnd_7866350 : Nat := 4983230072969 + 3 ^ 40 * 7866350 * 2
def baseEnd_7866350 : Nat := 448802060721711455905369

theorem tailTrace_7866350 : CollatzResearch.WordTrace tailWord_7866350 prefixEnd_7866350 448802060721711455905369 := by
  unfold tailWord_7866350
  simp only [CollatzResearch.WordTrace]
  refine ⟨35863669381445611308293563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191272903367709926977565669 35863669381445611308293563)
  ·
    refine ⟨53795504072168416962440345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35863669381445611308293563 53795504072168416962440345)
    ·
      refine ⟨40346628054126312721830259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53795504072168416962440345 40346628054126312721830259)
      ·
        refine ⟨60519942081189469082745389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40346628054126312721830259 60519942081189469082745389)
        ·
          refine ⟨22694978280446050906029521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60519942081189469082745389 22694978280446050906029521)
          ·
            refine ⟨17021233710334538179522141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22694978280446050906029521 17021233710334538179522141)
            ·
              refine ⟨6382962641375451817320803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17021233710334538179522141 6382962641375451817320803)
              ·
                refine ⟨9574443962063177725981205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382962641375451817320803 9574443962063177725981205)
                ·
                  refine ⟨448802060721711455905369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9574443962063177725981205 448802060721711455905369)
                  ·
                    rfl

theorem cell23_7866350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_7866350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866350 prefixEnd_7866350 := by exact prefixLift 7866350
  have htrace : WordTrace (prefixWord ++ tailWord_7866350) baseStart_7866350 baseEnd_7866350 := by
    simpa [prefixWord, tailWord_7866350, baseEnd_7866350] using wordTrace_append hprefix tailTrace_7866350
  have hstable : (prefixWord ++ tailWord_7866350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866350).length < 2 ^ (prefixWord ++ tailWord_7866350).sum := by decide
  have hdescent : baseEnd_7866350 < baseStart_7866350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866376 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 3, 6]
def baseStart_7866376 : Nat := 118140960795 + 7866376 * 2 ^ 59
def prefixEnd_7866376 : Nat := 4983230072969 + 3 ^ 40 * 7866376 * 2
def baseEnd_7866376 : Nat := 1346410632330806667141067

theorem tailTrace_7866376 : CollatzResearch.WordTrace tailWord_7866376 prefixEnd_7866376 1346410632330806667141067 := by
  unfold tailWord_7866376
  simp only [CollatzResearch.WordTrace]
  refine ⟨143455151674735348453397491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191273535566313797937863321 143455151674735348453397491)
  ·
    refine ⟨215182727512103022680096237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143455151674735348453397491 215182727512103022680096237)
    ·
      refine ⟨80693522817038633505036089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215182727512103022680096237 80693522817038633505036089)
      ·
        refine ⟨60520142112778975128777067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80693522817038633505036089 60520142112778975128777067)
        ·
          refine ⟨90780213169168462693165601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60520142112778975128777067 90780213169168462693165601)
          ·
            refine ⟨68085159876876347019874201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90780213169168462693165601 68085159876876347019874201)
            ·
              refine ⟨51063869907657260264905651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68085159876876347019874201 51063869907657260264905651)
              ·
                refine ⟨76595804861485890397358477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51063869907657260264905651 76595804861485890397358477)
                ·
                  refine ⟨28723426823057208899009429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76595804861485890397358477 28723426823057208899009429)
                  ·
                    refine ⟨1346410632330806667141067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28723426823057208899009429 1346410632330806667141067)
                    ·
                      rfl

theorem cell23_7866376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_7866376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866376 prefixEnd_7866376 := by exact prefixLift 7866376
  have htrace : WordTrace (prefixWord ++ tailWord_7866376) baseStart_7866376 baseEnd_7866376 := by
    simpa [prefixWord, tailWord_7866376, baseEnd_7866376] using wordTrace_append hprefix tailTrace_7866376
  have hstable : (prefixWord ++ tailWord_7866376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866376).length < 2 ^ (prefixWord ++ tailWord_7866376).sum := by decide
  have hdescent : baseEnd_7866376 < baseStart_7866376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866393 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 2, 4]
def baseStart_7866393 : Nat := 118140960795 + 7866393 * 2 ^ 59
def prefixEnd_7866393 : Nat := 4983230072969 + 3 ^ 40 * 7866393 * 2
def baseEnd_7866393 : Nat := 1346413542054515478303541

theorem tailTrace_7866393 : CollatzResearch.WordTrace tailWord_7866393 prefixEnd_7866393 1346413542054515478303541 := by
  unfold tailWord_7866393
  simp only [CollatzResearch.WordTrace]
  refine ⟨286910923390409108810163833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191273948926939405873442555 286910923390409108810163833)
  ·
    refine ⟨215183192542806831607622875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286910923390409108810163833 215183192542806831607622875)
    ·
      refine ⟨322774788814210247411434313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215183192542806831607622875 322774788814210247411434313)
      ·
        refine ⟨242081091610657685558575735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322774788814210247411434313 242081091610657685558575735)
        ·
          refine ⟨363121637415986528337863603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242081091610657685558575735 363121637415986528337863603)
          ·
            refine ⟨544682456123979792506795405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363121637415986528337863603 544682456123979792506795405)
            ·
              refine ⟨204255921046492422190048277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544682456123979792506795405 204255921046492422190048277)
              ·
                refine ⟨9574496299054332290158513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204255921046492422190048277 9574496299054332290158513)
                ·
                  refine ⟨7180872224290749217618885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9574496299054332290158513 7180872224290749217618885)
                  ·
                    refine ⟨1346413542054515478303541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7180872224290749217618885 1346413542054515478303541)
                    ·
                      rfl

theorem cell23_7866393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_7866393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866393 prefixEnd_7866393 := by exact prefixLift 7866393
  have htrace : WordTrace (prefixWord ++ tailWord_7866393) baseStart_7866393 baseEnd_7866393 := by
    simpa [prefixWord, tailWord_7866393, baseEnd_7866393] using wordTrace_append hprefix tailTrace_7866393
  have hstable : (prefixWord ++ tailWord_7866393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866393).length < 2 ^ (prefixWord ++ tailWord_7866393).sum := by decide
  have hdescent : baseEnd_7866393 < baseStart_7866393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866394 : List Nat := [3, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3]
def baseStart_7866394 : Nat := 118140960795 + 7866394 * 2 ^ 59
def prefixEnd_7866394 : Nat := 4983230072969 + 3 ^ 40 * 7866394 * 2
def baseEnd_7866394 : Nat := 4039241139644200930998119

theorem tailTrace_7866394 : CollatzResearch.WordTrace tailWord_7866394 prefixEnd_7866394 4039241139644200930998119 := by
  unfold tailWord_7866394
  simp only [CollatzResearch.WordTrace]
  refine ⟨71727739965851371495237559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191273973242270323987300157 71727739965851371495237559)
  ·
    refine ⟨107591609948777057242856339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71727739965851371495237559 107591609948777057242856339)
    ·
      refine ⟨161387414923165585864284509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107591609948777057242856339 161387414923165585864284509)
      ·
        refine ⟨60520280596187094699106691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161387414923165585864284509 60520280596187094699106691)
        ·
          refine ⟨90780420894280642048660037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60520280596187094699106691 90780420894280642048660037)
          ·
            refine ⟨17021328917677620384123757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90780420894280642048660037 17021328917677620384123757)
            ·
              refine ⟨6382998344129107644046409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17021328917677620384123757 6382998344129107644046409)
              ·
                refine ⟨4787248758096830733034807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6382998344129107644046409 4787248758096830733034807)
                ·
                  refine ⟨7180873137145246099552211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787248758096830733034807 7180873137145246099552211)
                  ·
                    refine ⟨10771309705717869149328317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7180873137145246099552211 10771309705717869149328317)
                    ·
                      refine ⟨4039241139644200930998119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10771309705717869149328317 4039241139644200930998119)
                      ·
                        rfl

theorem cell23_7866394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_7866394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866394 prefixEnd_7866394 := by exact prefixLift 7866394
  have htrace : WordTrace (prefixWord ++ tailWord_7866394) baseStart_7866394 baseEnd_7866394 := by
    simpa [prefixWord, tailWord_7866394, baseEnd_7866394] using wordTrace_append hprefix tailTrace_7866394
  have hstable : (prefixWord ++ tailWord_7866394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866394).length < 2 ^ (prefixWord ++ tailWord_7866394).sum := by decide
  have hdescent : baseEnd_7866394 < baseStart_7866394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866403 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 3]
def baseStart_7866403 : Nat := 118140960795 + 7866403 * 2 ^ 59
def prefixEnd_7866403 : Nat := 4983230072969 + 3 ^ 40 * 7866403 * 2
def baseEnd_7866403 : Nat := 4039245760970091395785577

theorem tailTrace_7866403 : CollatzResearch.WordTrace tailWord_7866403 prefixEnd_7866403 4039245760970091395785577 := by
  unfold tailWord_7866403
  simp only [CollatzResearch.WordTrace]
  refine ⟨286911288120372880518027863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191274192080248587012018575 286911288120372880518027863)
  ·
    refine ⟨430366932180559320777041795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286911288120372880518027863 430366932180559320777041795)
    ·
      refine ⟨645550398270838981165562693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430366932180559320777041795 645550398270838981165562693)
      ·
        refine ⟨121040699675782308968543005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 645550398270838981165562693 121040699675782308968543005)
        ·
          refine ⟨45390262378418365863203627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121040699675782308968543005 45390262378418365863203627)
          ·
            refine ⟨68085393567627548794805441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45390262378418365863203627 68085393567627548794805441)
            ·
              refine ⟨51064045175720661596104081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68085393567627548794805441 51064045175720661596104081)
              ·
                refine ⟨38298033881790496197078061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51064045175720661596104081 38298033881790496197078061)
                ·
                  refine ⟨14361762705671436073904273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38298033881790496197078061 14361762705671436073904273)
                  ·
                    refine ⟨10771322029253577055428205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14361762705671436073904273 10771322029253577055428205)
                    ·
                      refine ⟨4039245760970091395785577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10771322029253577055428205 4039245760970091395785577)
                      ·
                        rfl

theorem cell23_7866403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_7866403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866403 prefixEnd_7866403 := by exact prefixLift 7866403
  have htrace : WordTrace (prefixWord ++ tailWord_7866403) baseStart_7866403 baseEnd_7866403 := by
    simpa [prefixWord, tailWord_7866403, baseEnd_7866403] using wordTrace_append hprefix tailTrace_7866403
  have hstable : (prefixWord ++ tailWord_7866403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866403).length < 2 ^ (prefixWord ++ tailWord_7866403).sum := by decide
  have hdescent : baseEnd_7866403 < baseStart_7866403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866477 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_7866477 : Nat := 118140960795 + 7866477 * 2 ^ 59
def prefixEnd_7866477 : Nat := 4983230072969 + 3 ^ 40 * 7866477 * 2
def baseEnd_7866477 : Nat := 4039283758538524106260237

theorem tailTrace_7866477 : CollatzResearch.WordTrace tailWord_7866477 prefixEnd_7866477 4039283758538524106260237 := by
  unfold tailWord_7866477
  simp only [CollatzResearch.WordTrace]
  refine ⟨286913987122104791156221685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191275991414736527437481123 286913987122104791156221685)
  ·
    refine ⟨26898186292697324170895783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286913987122104791156221685 26898186292697324170895783)
    ·
      refine ⟨40347279439045986256343675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26898186292697324170895783 40347279439045986256343675)
      ·
        refine ⟨60520919158568979384515513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40347279439045986256343675 60520919158568979384515513)
        ·
          refine ⟨45390689368926734538386635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60520919158568979384515513 45390689368926734538386635)
          ·
            refine ⟨68086034053390101807579953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45390689368926734538386635 68086034053390101807579953)
            ·
              refine ⟨51064525540042576355684965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68086034053390101807579953 51064525540042576355684965)
              ·
                refine ⟨9574598538757983066690931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51064525540042576355684965 9574598538757983066690931)
                ·
                  refine ⟨14361897808136974600036397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9574598538757983066690931 14361897808136974600036397)
                  ·
                    refine ⟨5385711678051365475013649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14361897808136974600036397 5385711678051365475013649)
                    ·
                      refine ⟨4039283758538524106260237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385711678051365475013649 4039283758538524106260237)
                      ·
                        rfl

theorem cell23_7866477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_7866477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866477 prefixEnd_7866477 := by exact prefixLift 7866477
  have htrace : WordTrace (prefixWord ++ tailWord_7866477) baseStart_7866477 baseEnd_7866477 := by
    simpa [prefixWord, tailWord_7866477, baseEnd_7866477] using wordTrace_append hprefix tailTrace_7866477
  have hstable : (prefixWord ++ tailWord_7866477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866477).length < 2 ^ (prefixWord ++ tailWord_7866477).sum := by decide
  have hdescent : baseEnd_7866477 < baseStart_7866477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866496 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 11]
def baseStart_7866496 : Nat := 118140960795 + 7866496 * 2 ^ 59
def prefixEnd_7866496 : Nat := 4983230072969 + 3 ^ 40 * 7866496 * 2
def baseEnd_7866496 : Nat := 448810390518995503546961

theorem tailTrace_7866496 : CollatzResearch.WordTrace tailWord_7866496 prefixEnd_7866496 448810390518995503546961 := by
  unfold tailWord_7866496
  simp only [CollatzResearch.WordTrace]
  refine ⟨143457340054517978700581671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191276453406023971600775561 143457340054517978700581671)
  ·
    refine ⟨215186010081776968050872507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143457340054517978700581671 215186010081776968050872507)
    ·
      refine ⟨322779015122665452076308761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215186010081776968050872507 322779015122665452076308761)
      ·
        refine ⟨242084261341999089057231571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322779015122665452076308761 242084261341999089057231571)
        ·
          refine ⟨363126392012998633585847357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242084261341999089057231571 363126392012998633585847357)
          ·
            refine ⟨136172397004874487594692759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363126392012998633585847357 136172397004874487594692759)
            ·
              refine ⟨204258595507311731392039139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136172397004874487594692759 204258595507311731392039139)
              ·
                refine ⟨306387893260967597088058709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204258595507311731392039139 306387893260967597088058709)
                ·
                  refine ⟨448810390518995503546961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 306387893260967597088058709 448810390518995503546961)
                  ·
                    rfl

theorem cell23_7866496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_7866496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866496 prefixEnd_7866496 := by exact prefixLift 7866496
  have htrace : WordTrace (prefixWord ++ tailWord_7866496) baseStart_7866496 baseEnd_7866496 := by
    simpa [prefixWord, tailWord_7866496, baseEnd_7866496] using wordTrace_append hprefix tailTrace_7866496
  have hstable : (prefixWord ++ tailWord_7866496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866496).length < 2 ^ (prefixWord ++ tailWord_7866496).sum := by decide
  have hdescent : baseEnd_7866496 < baseStart_7866496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866503 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_7866503 : Nat := 118140960795 + 7866503 * 2 ^ 59
def prefixEnd_7866503 : Nat := 4983230072969 + 3 ^ 40 * 7866503 * 2
def baseEnd_7866503 : Nat := 4039297109035541004535117

theorem tailTrace_7866503 : CollatzResearch.WordTrace tailWord_7866503 prefixEnd_7866503 4039297109035541004535117 := by
  unfold tailWord_7866503
  simp only [CollatzResearch.WordTrace]
  refine ⟨286914935420010597596668163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191276623613340398397778775 286914935420010597596668163)
  ·
    refine ⟨430372403130015896395002245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286914935420010597596668163 430372403130015896395002245)
    ·
      refine ⟨80694825586877980574062921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430372403130015896395002245 80694825586877980574062921)
      ·
        refine ⟨60521119190158485430547191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80694825586877980574062921 60521119190158485430547191)
        ·
          refine ⟨90781678785237728145820787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60521119190158485430547191 90781678785237728145820787)
          ·
            refine ⟨136172518177856592218731181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90781678785237728145820787 136172518177856592218731181)
            ·
              refine ⟨51064694316696222082024193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136172518177856592218731181 51064694316696222082024193)
              ·
                refine ⟨38298520737522166561518145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51064694316696222082024193 38298520737522166561518145)
                ·
                  refine ⟨28723890553141624921138609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38298520737522166561518145 28723890553141624921138609)
                  ·
                    refine ⟨21542917914856218690853957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28723890553141624921138609 21542917914856218690853957)
                    ·
                      refine ⟨4039297109035541004535117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21542917914856218690853957 4039297109035541004535117)
                      ·
                        rfl

theorem cell23_7866503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_7866503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866503 prefixEnd_7866503 := by exact prefixLift 7866503
  have htrace : WordTrace (prefixWord ++ tailWord_7866503) baseStart_7866503 baseEnd_7866503 := by
    simpa [prefixWord, tailWord_7866503, baseEnd_7866503] using wordTrace_append hprefix tailTrace_7866503
  have hstable : (prefixWord ++ tailWord_7866503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866503).length < 2 ^ (prefixWord ++ tailWord_7866503).sum := by decide
  have hdescent : baseEnd_7866503 < baseStart_7866503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866523 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 3]
def baseStart_7866523 : Nat := 118140960795 + 7866523 * 2 ^ 59
def prefixEnd_7866523 : Nat := 4983230072969 + 3 ^ 40 * 7866523 * 2
def baseEnd_7866523 : Nat := 4039307378648630926285025

theorem tailTrace_7866523 : CollatzResearch.WordTrace tailWord_7866523 prefixEnd_7866523 4039307378648630926285025 := by
  unfold tailWord_7866523
  simp only [CollatzResearch.WordTrace]
  refine ⟨286915664879938141012396223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191277109919958760674930815 286915664879938141012396223)
  ·
    refine ⟨430373497319907211518594335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286915664879938141012396223 430373497319907211518594335)
    ·
      refine ⟨645560245979860817277891503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430373497319907211518594335 645560245979860817277891503)
      ·
        refine ⟨968340368969791225916837255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645560245979860817277891503 968340368969791225916837255)
        ·
          refine ⟨1452510553454686838875255883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968340368969791225916837255 1452510553454686838875255883)
          ·
            refine ⟨2178765830182030258312883825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452510553454686838875255883 2178765830182030258312883825)
            ·
              refine ⟨1634074372636522693734662869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178765830182030258312883825 1634074372636522693734662869)
              ·
                refine ⟨38298618108668500634406161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1634074372636522693734662869 38298618108668500634406161)
                ·
                  refine ⟨28723963581501375475804621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38298618108668500634406161 28723963581501375475804621)
                  ·
                    refine ⟨10771486343063015803426733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28723963581501375475804621 10771486343063015803426733)
                    ·
                      refine ⟨4039307378648630926285025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10771486343063015803426733 4039307378648630926285025)
                      ·
                        rfl

theorem cell23_7866523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 3].length) (baseStart_7866523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866523 prefixEnd_7866523 := by exact prefixLift 7866523
  have htrace : WordTrace (prefixWord ++ tailWord_7866523) baseStart_7866523 baseEnd_7866523 := by
    simpa [prefixWord, tailWord_7866523, baseEnd_7866523] using wordTrace_append hprefix tailTrace_7866523
  have hstable : (prefixWord ++ tailWord_7866523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866523).length < 2 ^ (prefixWord ++ tailWord_7866523).sum := by decide
  have hdescent : baseEnd_7866523 < baseStart_7866523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866530 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 7]
def baseStart_7866530 : Nat := 118140960795 + 7866530 * 2 ^ 59
def prefixEnd_7866530 : Nat := 4983230072969 + 3 ^ 40 * 7866530 * 2
def baseEnd_7866530 : Nat := 448812330334801377655277

theorem tailTrace_7866530 : CollatzResearch.WordTrace tailWord_7866530 prefixEnd_7866530 448812330334801377655277 := by
  unfold tailWord_7866530
  simp only [CollatzResearch.WordTrace]
  refine ⟨71728980047728195301975261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191277280127275187471934029 71728980047728195301975261)
  ·
    refine ⟨26898367517898073238240723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71728980047728195301975261 26898367517898073238240723)
    ·
      refine ⟨40347551276847109857361085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26898367517898073238240723 40347551276847109857361085)
      ·
        refine ⟨15130331728817666196510407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40347551276847109857361085 15130331728817666196510407)
        ·
          refine ⟨22695497593226499294765611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15130331728817666196510407 22695497593226499294765611)
          ·
            refine ⟨34043246389839748942148417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22695497593226499294765611 34043246389839748942148417)
            ·
              refine ⟨25532434792379811706611313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34043246389839748942148417 25532434792379811706611313)
              ·
                refine ⟨19149326094284858779958485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25532434792379811706611313 19149326094284858779958485)
                ·
                  refine ⟨448812330334801377655277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19149326094284858779958485 448812330334801377655277)
                  ·
                    rfl

theorem cell23_7866530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_7866530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866530 prefixEnd_7866530 := by exact prefixLift 7866530
  have htrace : WordTrace (prefixWord ++ tailWord_7866530) baseStart_7866530 baseEnd_7866530 := by
    simpa [prefixWord, tailWord_7866530, baseEnd_7866530] using wordTrace_append hprefix tailTrace_7866530
  have hstable : (prefixWord ++ tailWord_7866530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866530).length < 2 ^ (prefixWord ++ tailWord_7866530).sum := by decide
  have hdescent : baseEnd_7866530 < baseStart_7866530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866543 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 2, 5]
def baseStart_7866543 : Nat := 118140960795 + 7866543 * 2 ^ 59
def prefixEnd_7866543 : Nat := 4983230072969 + 3 ^ 40 * 7866543 * 2
def baseEnd_7866543 : Nat := 1346439216087240282678311

theorem tailTrace_7866543 : CollatzResearch.WordTrace tailWord_7866543 prefixEnd_7866543 1346439216087240282678311 := by
  unfold tailWord_7866543
  simp only [CollatzResearch.WordTrace]
  refine ⟨286916394339865684428124283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191277596226577122952082855 286916394339865684428124283)
  ·
    refine ⟨430374591509798526642186425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286916394339865684428124283 430374591509798526642186425)
    ·
      refine ⟨322780943632348894981639819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430374591509798526642186425 322780943632348894981639819)
      ·
        refine ⟨484171415448523342472459729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322780943632348894981639819 484171415448523342472459729)
        ·
          refine ⟨363128561586392506854344797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484171415448523342472459729 363128561586392506854344797)
          ·
            refine ⟨136173210594897190070379299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363128561586392506854344797 136173210594897190070379299)
            ·
              refine ⟨204259815892345785105568949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136173210594897190070379299 204259815892345785105568949)
              ·
                refine ⟨19149357739907417353647089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204259815892345785105568949 19149357739907417353647089)
                ·
                  refine ⟨14362018304930563015235317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19149357739907417353647089 14362018304930563015235317)
                  ·
                    refine ⟨1346439216087240282678311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14362018304930563015235317 1346439216087240282678311)
                    ·
                      rfl

theorem cell23_7866543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_7866543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866543 prefixEnd_7866543 := by exact prefixLift 7866543
  have htrace : WordTrace (prefixWord ++ tailWord_7866543) baseStart_7866543 baseEnd_7866543 := by
    simpa [prefixWord, tailWord_7866543, baseEnd_7866543] using wordTrace_append hprefix tailTrace_7866543
  have hstable : (prefixWord ++ tailWord_7866543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866543).length < 2 ^ (prefixWord ++ tailWord_7866543).sum := by decide
  have hdescent : baseEnd_7866543 < baseStart_7866543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866553 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_7866553 : Nat := 118140960795 + 7866553 * 2 ^ 59
def prefixEnd_7866553 : Nat := 4983230072969 + 3 ^ 40 * 7866553 * 2
def baseEnd_7866553 : Nat := 4039322783068265808909887

theorem tailTrace_7866553 : CollatzResearch.WordTrace tailWord_7866553 prefixEnd_7866553 4039322783068265808909887 := by
  unfold tailWord_7866553
  simp only [CollatzResearch.WordTrace]
  refine ⟨286916759069829456135988313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191277839379886304090658875 286916759069829456135988313)
  ·
    refine ⟨215187569302372092101991235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286916759069829456135988313 215187569302372092101991235)
    ·
      refine ⟨322781353953558138152986853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215187569302372092101991235 322781353953558138152986853)
      ·
        refine ⟨60521503866292150903685035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322781353953558138152986853 60521503866292150903685035)
        ·
          refine ⟨90782255799438226355527553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60521503866292150903685035 90782255799438226355527553)
          ·
            refine ⟨68086691849578669766645665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90782255799438226355527553 68086691849578669766645665)
            ·
              refine ⟨51065018887184002324984249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68086691849578669766645665 51065018887184002324984249)
              ·
                refine ⟨38298764165388001743738187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51065018887184002324984249 38298764165388001743738187)
                ·
                  refine ⟨57448146248082002615607281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38298764165388001743738187 57448146248082002615607281)
                  ·
                    refine ⟨43086109686061501961705461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57448146248082002615607281 43086109686061501961705461)
                    ·
                      refine ⟨4039322783068265808909887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43086109686061501961705461 4039322783068265808909887)
                      ·
                        rfl

theorem cell23_7866553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_7866553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866553 prefixEnd_7866553 := by exact prefixLift 7866553
  have htrace : WordTrace (prefixWord ++ tailWord_7866553) baseStart_7866553 baseEnd_7866553 := by
    simpa [prefixWord, tailWord_7866553, baseEnd_7866553] using wordTrace_append hprefix tailTrace_7866553
  have hstable : (prefixWord ++ tailWord_7866553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866553).length < 2 ^ (prefixWord ++ tailWord_7866553).sum := by decide
  have hdescent : baseEnd_7866553 < baseStart_7866553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866560 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 2, 5]
def baseStart_7866560 : Nat := 118140960795 + 7866560 * 2 ^ 59
def prefixEnd_7866560 : Nat := 4983230072969 + 3 ^ 40 * 7866560 * 2
def baseEnd_7866560 : Nat := 1346442125810949093840785

theorem tailTrace_7866560 : CollatzResearch.WordTrace tailWord_7866560 prefixEnd_7866560 1346442125810949093840785 := by
  unfold tailWord_7866560
  simp only [CollatzResearch.WordTrace]
  refine ⟨143458507190402048165746567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191278009587202730887662089 143458507190402048165746567)
  ·
    refine ⟨215187760785603072248619851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143458507190402048165746567 215187760785603072248619851)
    ·
      refine ⟨322781641178404608372929777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215187760785603072248619851 322781641178404608372929777)
      ·
        refine ⟨242086230883803456279697333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322781641178404608372929777 242086230883803456279697333)
        ·
          refine ⟨22695584145356574026221625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242086230883803456279697333 22695584145356574026221625)
          ·
            refine ⟨17021688109017430519666219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22695584145356574026221625 17021688109017430519666219)
            ·
              refine ⟨25532532163526145779499329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17021688109017430519666219 25532532163526145779499329)
              ·
                refine ⟨19149399122644609334624497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25532532163526145779499329 19149399122644609334624497)
                ·
                  refine ⟨14362049341983457000968373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19149399122644609334624497 14362049341983457000968373)
                  ·
                    refine ⟨1346442125810949093840785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14362049341983457000968373 1346442125810949093840785)
                    ·
                      rfl

theorem cell23_7866560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_7866560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866560 prefixEnd_7866560 := by exact prefixLift 7866560
  have htrace : WordTrace (prefixWord ++ tailWord_7866560) baseStart_7866560 baseEnd_7866560 := by
    simpa [prefixWord, tailWord_7866560, baseEnd_7866560] using wordTrace_append hprefix tailTrace_7866560
  have hstable : (prefixWord ++ tailWord_7866560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866560).length < 2 ^ (prefixWord ++ tailWord_7866560).sum := by decide
  have hdescent : baseEnd_7866560 < baseStart_7866560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866564 : List Nat := [2, 3, 3, 1, 2, 2, 3, 2, 5]
def baseStart_7866564 : Nat := 118140960795 + 7866564 * 2 ^ 59
def prefixEnd_7866564 : Nat := 4983230072969 + 3 ^ 40 * 7866564 * 2
def baseEnd_7866564 : Nat := 448814270150607251763593

theorem tailTrace_7866564 : CollatzResearch.WordTrace tailWord_7866564 prefixEnd_7866564 448814270150607251763593 := by
  unfold tailWord_7866564
  simp only [CollatzResearch.WordTrace]
  refine ⟨143458580136394802507319373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191278106848526403343092497 143458580136394802507319373)
  ·
    refine ⟨53796967551148050940244765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143458580136394802507319373 53796967551148050940244765)
    ·
      refine ⟨20173862831680519102591787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53796967551148050940244765 20173862831680519102591787)
      ·
        refine ⟨30260794247520778653887681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20173862831680519102591787 30260794247520778653887681)
        ·
          refine ⟨22695595685640583990415761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30260794247520778653887681 22695595685640583990415761)
          ·
            refine ⟨17021696764230437992811821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22695595685640583990415761 17021696764230437992811821)
            ·
              refine ⟨6383136286586414247304433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17021696764230437992811821 6383136286586414247304433)
              ·
                refine ⟨4787352214939810685478325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6383136286586414247304433 4787352214939810685478325)
                ·
                  refine ⟨448814270150607251763593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4787352214939810685478325 448814270150607251763593)
                  ·
                    rfl

theorem cell23_7866564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_7866564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866564 prefixEnd_7866564 := by exact prefixLift 7866564
  have htrace : WordTrace (prefixWord ++ tailWord_7866564) baseStart_7866564 baseEnd_7866564 := by
    simpa [prefixWord, tailWord_7866564, baseEnd_7866564] using wordTrace_append hprefix tailTrace_7866564
  have hstable : (prefixWord ++ tailWord_7866564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866564).length < 2 ^ (prefixWord ++ tailWord_7866564).sum := by decide
  have hdescent : baseEnd_7866564 < baseStart_7866564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866597 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_7866597 : Nat := 118140960795 + 7866597 * 2 ^ 59
def prefixEnd_7866597 : Nat := 4983230072969 + 3 ^ 40 * 7866597 * 2
def baseEnd_7866597 : Nat := 4039345376217063636759685

theorem tailTrace_7866597 : CollatzResearch.WordTrace tailWord_7866597 prefixEnd_7866597 4039345376217063636759685 := by
  unfold tailWord_7866597
  simp only [CollatzResearch.WordTrace]
  refine ⟨286918363881670051650590045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191278909254446701100393363 286918363881670051650590045)
  ·
    refine ⟨107594386455626269368971267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286918363881670051650590045 107594386455626269368971267)
    ·
      refine ⟨161391579683439404053456901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107594386455626269368971267 161391579683439404053456901)
      ·
        refine ⟨30260921190644888260023169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161391579683439404053456901 30260921190644888260023169)
        ·
          refine ⟨22695690892983666195017377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30260921190644888260023169 22695690892983666195017377)
          ·
            refine ⟨17021768169737749646263033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22695690892983666195017377 17021768169737749646263033)
            ·
              refine ⟨12766326127303312234697275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17021768169737749646263033 12766326127303312234697275)
              ·
                refine ⟨19149489190954968352045913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12766326127303312234697275 19149489190954968352045913)
                ·
                  refine ⟨14362116893216226264034435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19149489190954968352045913 14362116893216226264034435)
                  ·
                    refine ⟨21543175339824339396051653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14362116893216226264034435 21543175339824339396051653)
                    ·
                      refine ⟨4039345376217063636759685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21543175339824339396051653 4039345376217063636759685)
                      ·
                        rfl

theorem cell23_7866597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_7866597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866597 prefixEnd_7866597 := by exact prefixLift 7866597
  have htrace : WordTrace (prefixWord ++ tailWord_7866597) baseStart_7866597 baseEnd_7866597 := by
    simpa [prefixWord, tailWord_7866597, baseEnd_7866597] using wordTrace_append hprefix tailTrace_7866597
  have hstable : (prefixWord ++ tailWord_7866597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866597).length < 2 ^ (prefixWord ++ tailWord_7866597).sum := by decide
  have hdescent : baseEnd_7866597 < baseStart_7866597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866620 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 6]
def baseStart_7866620 : Nat := 118140960795 + 7866620 * 2 ^ 59
def prefixEnd_7866620 : Nat := 4983230072969 + 3 ^ 40 * 7866620 * 2
def baseEnd_7866620 : Nat := 448817465141346338530231

theorem tailTrace_7866620 : CollatzResearch.WordTrace tailWord_7866620 prefixEnd_7866620 448817465141346338530231 := by
  unfold tailWord_7866620
  simp only [CollatzResearch.WordTrace]
  refine ⟨143459601380293363289338657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191279468507057817719118209 143459601380293363289338657)
  ·
    refine ⟨107594701035220022467003993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143459601380293363289338657 107594701035220022467003993)
    ·
      refine ⟨80696025776415016850252995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107594701035220022467003993 80696025776415016850252995)
      ·
        refine ⟨121044038664622525275379493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80696025776415016850252995 121044038664622525275379493)
        ·
          refine ⟨22695757249616723489133655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121044038664622525275379493 22695757249616723489133655)
          ·
            refine ⟨34043635874425085233700483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22695757249616723489133655 34043635874425085233700483)
            ·
              refine ⟨51065453811637627850550725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34043635874425085233700483 51065453811637627850550725)
              ·
                refine ⟨9574772589682055221978261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51065453811637627850550725 9574772589682055221978261)
                ·
                  refine ⟨448817465141346338530231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9574772589682055221978261 448817465141346338530231)
                  ·
                    rfl

theorem cell23_7866620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_7866620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866620 prefixEnd_7866620 := by exact prefixLift 7866620
  have htrace : WordTrace (prefixWord ++ tailWord_7866620) baseStart_7866620 baseEnd_7866620 := by
    simpa [prefixWord, tailWord_7866620, baseEnd_7866620] using wordTrace_append hprefix tailTrace_7866620
  have hstable : (prefixWord ++ tailWord_7866620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866620).length < 2 ^ (prefixWord ++ tailWord_7866620).sum := by decide
  have hdescent : baseEnd_7866620 < baseStart_7866620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866623 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_7866623 : Nat := 118140960795 + 7866623 * 2 ^ 59
def prefixEnd_7866623 : Nat := 4983230072969 + 3 ^ 40 * 7866623 * 2
def baseEnd_7866623 : Nat := 4039358726714080535034565

theorem tailTrace_7866623 : CollatzResearch.WordTrace tailWord_7866623 prefixEnd_7866623 4039358726714080535034565 := by
  unfold tailWord_7866623
  simp only [CollatzResearch.WordTrace]
  refine ⟨286919312179575858091036523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191279541453050572060691015 286919312179575858091036523)
  ·
    refine ⟨430378968269363787136554785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286919312179575858091036523 430378968269363787136554785)
    ·
      refine ⟨322784226202022840352416089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430378968269363787136554785 322784226202022840352416089)
      ·
        refine ⟨242088169651517130264312067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322784226202022840352416089 242088169651517130264312067)
        ·
          refine ⟨363132254477275695396468101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242088169651517130264312067 363132254477275695396468101)
          ·
            refine ⟨68087297714489192886837769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363132254477275695396468101 68087297714489192886837769)
            ·
              refine ⟨51065473285866894665128327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68087297714489192886837769 51065473285866894665128327)
              ·
                refine ⟨76598209928800341997692491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51065473285866894665128327 76598209928800341997692491)
                ·
                  refine ⟨114897314893200512996538737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76598209928800341997692491 114897314893200512996538737)
                  ·
                    refine ⟨86172986169900384747404053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114897314893200512996538737 86172986169900384747404053)
                    ·
                      refine ⟨4039358726714080535034565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86172986169900384747404053 4039358726714080535034565)
                      ·
                        rfl

theorem cell23_7866623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_7866623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866623 prefixEnd_7866623 := by exact prefixLift 7866623
  have htrace : WordTrace (prefixWord ++ tailWord_7866623) baseStart_7866623 baseEnd_7866623 := by
    simpa [prefixWord, tailWord_7866623, baseEnd_7866623] using wordTrace_append hprefix tailTrace_7866623
  have hstable : (prefixWord ++ tailWord_7866623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866623).length < 2 ^ (prefixWord ++ tailWord_7866623).sum := by decide
  have hdescent : baseEnd_7866623 < baseStart_7866623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866624 : List Nat := [2, 1, 1, 2, 1, 1, 8, 2, 1, 4]
def baseStart_7866624 : Nat := 118140960795 + 7866624 * 2 ^ 59
def prefixEnd_7866624 : Nat := 4983230072969 + 3 ^ 40 * 7866624 * 2
def baseEnd_7866624 : Nat := 1346453080064911677040687

theorem tailTrace_7866624 : CollatzResearch.WordTrace tailWord_7866624 prefixEnd_7866624 1346453080064911677040687 := by
  unfold tailWord_7866624
  simp only [CollatzResearch.WordTrace]
  refine ⟨143459674326286117630911463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191279565768381490174548617 143459674326286117630911463)
  ·
    refine ⟨215189511489429176446367195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143459674326286117630911463 215189511489429176446367195)
    ·
      refine ⟨322784267234143764669550793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215189511489429176446367195 322784267234143764669550793)
      ·
        refine ⟨242088200425607823502163095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322784267234143764669550793 242088200425607823502163095)
        ·
          refine ⟨363132300638411735253244643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242088200425607823502163095 363132300638411735253244643)
          ·
            refine ⟨544698450957617602879866965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363132300638411735253244643 544698450957617602879866965)
            ·
              refine ⟨6383184972159581283748441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 544698450957617602879866965 6383184972159581283748441)
              ·
                refine ⟨4787388729119685962811331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6383184972159581283748441 4787388729119685962811331)
                ·
                  refine ⟨7181083093679528944216997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787388729119685962811331 7181083093679528944216997)
                  ·
                    refine ⟨1346453080064911677040687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7181083093679528944216997 1346453080064911677040687)
                    ·
                      rfl

theorem cell23_7866624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 4].length) (baseStart_7866624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866624 prefixEnd_7866624 := by exact prefixLift 7866624
  have htrace : WordTrace (prefixWord ++ tailWord_7866624) baseStart_7866624 baseEnd_7866624 := by
    simpa [prefixWord, tailWord_7866624, baseEnd_7866624] using wordTrace_append hprefix tailTrace_7866624
  have hstable : (prefixWord ++ tailWord_7866624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866624).length < 2 ^ (prefixWord ++ tailWord_7866624).sum := by decide
  have hdescent : baseEnd_7866624 < baseStart_7866624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866647 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_7866647 : Nat := 118140960795 + 7866647 * 2 ^ 59
def prefixEnd_7866647 : Nat := 4983230072969 + 3 ^ 40 * 7866647 * 2
def baseEnd_7866647 : Nat := 4039371050249788441134455

theorem tailTrace_7866647 : CollatzResearch.WordTrace tailWord_7866647 prefixEnd_7866647 4039371050249788441134455 := by
  unfold tailWord_7866647
  simp only [CollatzResearch.WordTrace]
  refine ⟨286920187531488910189910195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191280125020992606793273463 286920187531488910189910195)
  ·
    refine ⟨430380281297233365284865293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286920187531488910189910195 430380281297233365284865293)
    ·
      refine ⟨161392605486462511981824485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430380281297233365284865293 161392605486462511981824485)
      ·
        refine ⟨30261113528711720996592091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161392605486462511981824485 30261113528711720996592091)
        ·
          refine ⟨45391670293067581494888137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30261113528711720996592091 45391670293067581494888137)
          ·
            refine ⟨34043752719800686121166103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45391670293067581494888137 34043752719800686121166103)
            ·
              refine ⟨51065629079701029181749155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34043752719800686121166103 51065629079701029181749155)
              ·
                refine ⟨76598443619551543772623733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51065629079701029181749155 76598443619551543772623733)
                ·
                  refine ⟨7181104089332957228683475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76598443619551543772623733 7181104089332957228683475)
                  ·
                    refine ⟨10771656133999435843025213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7181104089332957228683475 10771656133999435843025213)
                    ·
                      refine ⟨4039371050249788441134455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10771656133999435843025213 4039371050249788441134455)
                      ·
                        rfl

theorem cell23_7866647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_7866647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866647 prefixEnd_7866647 := by exact prefixLift 7866647
  have htrace : WordTrace (prefixWord ++ tailWord_7866647) baseStart_7866647 baseEnd_7866647 := by
    simpa [prefixWord, tailWord_7866647, baseEnd_7866647] using wordTrace_append hprefix tailTrace_7866647
  have hstable : (prefixWord ++ tailWord_7866647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866647).length < 2 ^ (prefixWord ++ tailWord_7866647).sum := by decide
  have hdescent : baseEnd_7866647 < baseStart_7866647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866681 : List Nat := [1, 2, 1, 6, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7866681 : Nat := 118140960795 + 7866681 * 2 ^ 59
def prefixEnd_7866681 : Nat := 4983230072969 + 3 ^ 40 * 7866681 * 2
def baseEnd_7866681 : Nat := 4039388508592041308109299

theorem tailTrace_7866681 : CollatzResearch.WordTrace tailWord_7866681 prefixEnd_7866681 4039388508592041308109299 := by
  unfold tailWord_7866681
  simp only [CollatzResearch.WordTrace]
  refine ⟨286921427613365733996647897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191280951742243822664431931 286921427613365733996647897)
  ·
    refine ⟨215191070710024300497485923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286921427613365733996647897 215191070710024300497485923)
    ·
      refine ⟨322786606065036450746228885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215191070710024300497485923 322786606065036450746228885)
      ·
        refine ⟨15130622159298583628729479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 322786606065036450746228885 15130622159298583628729479)
        ·
          refine ⟨22695933238947875443094219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15130622159298583628729479 22695933238947875443094219)
          ·
            refine ⟨34043899858421813164641329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22695933238947875443094219 34043899858421813164641329)
            ·
              refine ⟨25532924893816359873480997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34043899858421813164641329 25532924893816359873480997)
              ·
                refine ⟨4787423417590567476277687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25532924893816359873480997 4787423417590567476277687)
                ·
                  refine ⟨7181135126385851214416531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787423417590567476277687 7181135126385851214416531)
                  ·
                    refine ⟨10771702689578776821624797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7181135126385851214416531 10771702689578776821624797)
                    ·
                      refine ⟨4039388508592041308109299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10771702689578776821624797 4039388508592041308109299)
                      ·
                        rfl

theorem cell23_7866681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7866681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866681 prefixEnd_7866681 := by exact prefixLift 7866681
  have htrace : WordTrace (prefixWord ++ tailWord_7866681) baseStart_7866681 baseEnd_7866681 := by
    simpa [prefixWord, tailWord_7866681, baseEnd_7866681] using wordTrace_append hprefix tailTrace_7866681
  have hstable : (prefixWord ++ tailWord_7866681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866681).length < 2 ^ (prefixWord ++ tailWord_7866681).sum := by decide
  have hdescent : baseEnd_7866681 < baseStart_7866681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866700 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_7866700 : Nat := 118140960795 + 7866700 * 2 ^ 59
def prefixEnd_7866700 : Nat := 4983230072969 + 3 ^ 40 * 7866700 * 2
def baseEnd_7866700 : Nat := 4039398264724476733771711

theorem tailTrace_7866700 : CollatzResearch.WordTrace tailWord_7866700 prefixEnd_7866700 4039398264724476733771711 := by
  unfold tailWord_7866700
  simp only [CollatzResearch.WordTrace]
  refine ⟨143461060300148450120794777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191281413733531266827726369 143461060300148450120794777)
  ·
    refine ⟨107595795225111337590596083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143461060300148450120794777 107595795225111337590596083)
    ·
      refine ⟨161393692837667006385894125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107595795225111337590596083 161393692837667006385894125)
      ·
        refine ⟨60522634814125127394710297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161393692837667006385894125 60522634814125127394710297)
        ·
          refine ⟨45391976110593845546032723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60522634814125127394710297 45391976110593845546032723)
          ·
            refine ⟨68087964165890768319049085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45391976110593845546032723 68087964165890768319049085)
            ·
              refine ⟨25532986562209038119643407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68087964165890768319049085 25532986562209038119643407)
              ·
                refine ⟨38299479843313557179465111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25532986562209038119643407 38299479843313557179465111)
                ·
                  refine ⟨57449219764970335769197667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38299479843313557179465111 57449219764970335769197667)
                  ·
                    refine ⟨86173829647455503653796501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57449219764970335769197667 86173829647455503653796501)
                    ·
                      refine ⟨4039398264724476733771711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86173829647455503653796501 4039398264724476733771711)
                      ·
                        rfl

theorem cell23_7866700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_7866700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866700 prefixEnd_7866700 := by exact prefixLift 7866700
  have htrace : WordTrace (prefixWord ++ tailWord_7866700) baseStart_7866700 baseEnd_7866700 := by
    simpa [prefixWord, tailWord_7866700, baseEnd_7866700] using wordTrace_append hprefix tailTrace_7866700
  have hstable : (prefixWord ++ tailWord_7866700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866700).length < 2 ^ (prefixWord ++ tailWord_7866700).sum := by decide
  have hdescent : baseEnd_7866700 < baseStart_7866700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866704 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 3, 2, 2]
def baseStart_7866704 : Nat := 118140960795 + 7866704 * 2 ^ 59
def prefixEnd_7866704 : Nat := 4983230072969 + 3 ^ 40 * 7866704 * 2
def baseEnd_7866704 : Nat := 4039400318647094718121693

theorem tailTrace_7866704 : CollatzResearch.WordTrace tailWord_7866704 prefixEnd_7866704 4039400318647094718121693 := by
  unfold tailWord_7866704
  simp only [CollatzResearch.WordTrace]
  refine ⟨143461133246141204462367583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191281510994854939283156777 143461133246141204462367583)
  ·
    refine ⟨215191699869211806693551375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143461133246141204462367583 215191699869211806693551375)
    ·
      refine ⟨322787549803817710040327063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215191699869211806693551375 322787549803817710040327063)
      ·
        refine ⟨484181324705726565060490595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322787549803817710040327063 484181324705726565060490595)
        ·
          refine ⟨726271987058589847590735893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484181324705726565060490595 726271987058589847590735893)
          ·
            refine ⟨34043999393371399105815745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 726271987058589847590735893 34043999393371399105815745)
            ·
              refine ⟨25532999545028549329361809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34043999393371399105815745 25532999545028549329361809)
              ·
                refine ⟨19149749658771411997021357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25532999545028549329361809 19149749658771411997021357)
                ·
                  refine ⟨7181156122039279498883009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19149749658771411997021357 7181156122039279498883009)
                  ·
                    refine ⟨5385867091529459624162257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7181156122039279498883009 5385867091529459624162257)
                    ·
                      refine ⟨4039400318647094718121693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385867091529459624162257 4039400318647094718121693)
                      ·
                        rfl

theorem cell23_7866704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 2, 2].length) (baseStart_7866704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866704 prefixEnd_7866704 := by exact prefixLift 7866704
  have htrace : WordTrace (prefixWord ++ tailWord_7866704) baseStart_7866704 baseEnd_7866704 := by
    simpa [prefixWord, tailWord_7866704, baseEnd_7866704] using wordTrace_append hprefix tailTrace_7866704
  have hstable : (prefixWord ++ tailWord_7866704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866704).length < 2 ^ (prefixWord ++ tailWord_7866704).sum := by decide
  have hdescent : baseEnd_7866704 < baseStart_7866704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866764 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 3, 3, 2]
def baseStart_7866764 : Nat := 118140960795 + 7866764 * 2 ^ 59
def prefixEnd_7866764 : Nat := 4983230072969 + 3 ^ 40 * 7866764 * 2
def baseEnd_7866764 : Nat := 4039431127486364483371417

theorem tailTrace_7866764 : CollatzResearch.WordTrace tailWord_7866764 prefixEnd_7866764 4039431127486364483371417 := by
  unfold tailWord_7866764
  simp only [CollatzResearch.WordTrace]
  refine ⟨143462227436032519585959673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191282969914710026114612897 143462227436032519585959673)
  ·
    refine ⟨107596670577024389689469755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143462227436032519585959673 107596670577024389689469755)
    ·
      refine ⟨161395005865536584534204633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107596670577024389689469755 161395005865536584534204633)
      ·
        refine ⟨121046254399152438400653475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161395005865536584534204633 121046254399152438400653475)
        ·
          refine ⟨181569381598728657600980213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121046254399152438400653475 181569381598728657600980213)
          ·
            refine ⟨17022129524880811650091895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181569381598728657600980213 17022129524880811650091895)
            ·
              refine ⟨25533194287321217475137843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17022129524880811650091895 25533194287321217475137843)
              ·
                refine ⟨38299791430981826212706765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25533194287321217475137843 38299791430981826212706765)
                ·
                  refine ⟨14362421786618184829765037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38299791430981826212706765 14362421786618184829765037)
                  ·
                    refine ⟨5385908169981819311161889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14362421786618184829765037 5385908169981819311161889)
                    ·
                      refine ⟨4039431127486364483371417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5385908169981819311161889 4039431127486364483371417)
                      ·
                        rfl

theorem cell23_7866764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_7866764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866764 prefixEnd_7866764 := by exact prefixLift 7866764
  have htrace : WordTrace (prefixWord ++ tailWord_7866764) baseStart_7866764 baseEnd_7866764 := by
    simpa [prefixWord, tailWord_7866764, baseEnd_7866764] using wordTrace_append hprefix tailTrace_7866764
  have hstable : (prefixWord ++ tailWord_7866764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866764).length < 2 ^ (prefixWord ++ tailWord_7866764).sum := by decide
  have hdescent : baseEnd_7866764 < baseStart_7866764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866807 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_7866807 : Nat := 118140960795 + 7866807 * 2 ^ 59
def prefixEnd_7866807 : Nat := 4983230072969 + 3 ^ 40 * 7866807 * 2
def baseEnd_7866807 : Nat := 4039453207154507815133719

theorem tailTrace_7866807 : CollatzResearch.WordTrace tailWord_7866807 prefixEnd_7866807 4039453207154507815133719 := by
  unfold tailWord_7866807
  simp only [CollatzResearch.WordTrace]
  refine ⟨286926023210909257515734675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191284015473939505010489783 286926023210909257515734675)
  ·
    refine ⟨430389034816363886273602013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286926023210909257515734675 430389034816363886273602013)
    ·
      refine ⟨161395888056136457352600755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430389034816363886273602013 161395888056136457352600755)
      ·
        refine ⟨242093832084204686028901133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161395888056136457352600755 242093832084204686028901133)
        ·
          refine ⟨90785187031576757260837925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242093832084204686028901133 90785187031576757260837925)
          ·
            refine ⟨17022222568420641986407111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90785187031576757260837925 17022222568420641986407111)
            ·
              refine ⟨25533333852630962979610667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17022222568420641986407111 25533333852630962979610667)
              ·
                refine ⟨38300000778946444469416001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25533333852630962979610667 38300000778946444469416001)
                ·
                  refine ⟨28725000584209833352062001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38300000778946444469416001 28725000584209833352062001)
                  ·
                    refine ⟨21543750438157375014046501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28725000584209833352062001 21543750438157375014046501)
                    ·
                      refine ⟨4039453207154507815133719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21543750438157375014046501 4039453207154507815133719)
                      ·
                        rfl

theorem cell23_7866807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_7866807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866807 prefixEnd_7866807 := by exact prefixLift 7866807
  have htrace : WordTrace (prefixWord ++ tailWord_7866807) baseStart_7866807 baseEnd_7866807 := by
    simpa [prefixWord, tailWord_7866807, baseEnd_7866807] using wordTrace_append hprefix tailTrace_7866807
  have hstable : (prefixWord ++ tailWord_7866807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866807).length < 2 ^ (prefixWord ++ tailWord_7866807).sum := by decide
  have hdescent : baseEnd_7866807 < baseStart_7866807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866884 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7866884 : Nat := 118140960795 + 7866884 * 2 ^ 59
def prefixEnd_7866884 : Nat := 4983230072969 + 3 ^ 40 * 7866884 * 2
def baseEnd_7866884 : Nat := 4039492745164904013870865

theorem tailTrace_7866884 : CollatzResearch.WordTrace tailWord_7866884 prefixEnd_7866884 4039492745164904013870865 := by
  unfold tailWord_7866884
  simp only [CollatzResearch.WordTrace]
  refine ⟨143464415815815149833143853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191285887754420199777525137 143464415815815149833143853)
  ·
    refine ⟨53799155930930681187428945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143464415815815149833143853 53799155930930681187428945)
    ·
      refine ⟨40349366948198010890571709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53799155930930681187428945 40349366948198010890571709)
      ·
        refine ⟨15131012605574254083964391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40349366948198010890571709 15131012605574254083964391)
        ·
          refine ⟨22696518908361381125946587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15131012605574254083964391 22696518908361381125946587)
          ·
            refine ⟨34044778362542071688919881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22696518908361381125946587 34044778362542071688919881)
            ·
              refine ⟨25533583771906553766689911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34044778362542071688919881 25533583771906553766689911)
              ·
                refine ⟨38300375657859830650034867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25533583771906553766689911 38300375657859830650034867)
                ·
                  refine ⟨57450563486789745975052301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38300375657859830650034867 57450563486789745975052301)
                  ·
                    refine ⟨21543961307546154740644613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57450563486789745975052301 21543961307546154740644613)
                    ·
                      refine ⟨4039492745164904013870865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21543961307546154740644613 4039492745164904013870865)
                      ·
                        rfl

theorem cell23_7866884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7866884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866884 prefixEnd_7866884 := by exact prefixLift 7866884
  have htrace : WordTrace (prefixWord ++ tailWord_7866884) baseStart_7866884 baseEnd_7866884 := by
    simpa [prefixWord, tailWord_7866884, baseEnd_7866884] using wordTrace_append hprefix tailTrace_7866884
  have hstable : (prefixWord ++ tailWord_7866884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866884).length < 2 ^ (prefixWord ++ tailWord_7866884).sum := by decide
  have hdescent : baseEnd_7866884 < baseStart_7866884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866904 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_7866904 : Nat := 118140960795 + 7866904 * 2 ^ 59
def prefixEnd_7866904 : Nat := 4983230072969 + 3 ^ 40 * 7866904 * 2
def baseEnd_7866904 : Nat := 4039503014777993935620773

theorem tailTrace_7866904 : CollatzResearch.WordTrace tailWord_7866904 prefixEnd_7866904 4039503014777993935620773 := by
  unfold tailWord_7866904
  simp only [CollatzResearch.WordTrace]
  refine ⟨143464780545778921541007883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191286374061038562054677177 143464780545778921541007883)
  ·
    refine ⟨215197170818668382311511825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143464780545778921541007883 215197170818668382311511825)
    ·
      refine ⟨161397878114001286733633869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215197170818668382311511825 161397878114001286733633869)
      ·
        refine ⟨60524204292750482525112701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161397878114001286733633869 60524204292750482525112701)
        ·
          refine ⟨22696576609781430946917263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60524204292750482525112701 22696576609781430946917263)
          ·
            refine ⟨34044864914672146420375895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22696576609781430946917263 34044864914672146420375895)
            ·
              refine ⟨51067297372008219630563843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34044864914672146420375895 51067297372008219630563843)
              ·
                refine ⟨76600946058012329445845765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51067297372008219630563843 76600946058012329445845765)
                ·
                  refine ⟨14362677385877311771096081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76600946058012329445845765 14362677385877311771096081)
                  ·
                    refine ⟨10772008039407983828322061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14362677385877311771096081 10772008039407983828322061)
                    ·
                      refine ⟨4039503014777993935620773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10772008039407983828322061 4039503014777993935620773)
                      ·
                        rfl

theorem cell23_7866904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_7866904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866904 prefixEnd_7866904 := by exact prefixLift 7866904
  have htrace : WordTrace (prefixWord ++ tailWord_7866904) baseStart_7866904 baseEnd_7866904 := by
    simpa [prefixWord, tailWord_7866904, baseEnd_7866904] using wordTrace_append hprefix tailTrace_7866904
  have hstable : (prefixWord ++ tailWord_7866904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866904).length < 2 ^ (prefixWord ++ tailWord_7866904).sum := by decide
  have hdescent : baseEnd_7866904 < baseStart_7866904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866944 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 1, 5, 2]
def baseStart_7866944 : Nat := 118140960795 + 7866944 * 2 ^ 59
def prefixEnd_7866944 : Nat := 4983230072969 + 3 ^ 40 * 7866944 * 2
def baseEnd_7866944 : Nat := 4039523554004173779120589

theorem tailTrace_7866944 : CollatzResearch.WordTrace tailWord_7866944 prefixEnd_7866944 4039523554004173779120589 := by
  unfold tailWord_7866944
  simp only [CollatzResearch.WordTrace]
  refine ⟨143465510005706464956735943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191287346674275286608981257 143465510005706464956735943)
  ·
    refine ⟨215198265008559697435103915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143465510005706464956735943 215198265008559697435103915)
    ·
      refine ⟨322797397512839546152655873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215198265008559697435103915 322797397512839546152655873)
      ·
        refine ⟨242098048134629659614491905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322797397512839546152655873 242098048134629659614491905)
        ·
          refine ⟨181573536100972244710868929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242098048134629659614491905 181573536100972244710868929)
          ·
            refine ⟨136180152075729183533151697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181573536100972244710868929 136180152075729183533151697)
            ·
              refine ⟨102135114056796887649863773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136180152075729183533151697 102135114056796887649863773)
              ·
                refine ⟨38300667771298832868698915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102135114056796887649863773 38300667771298832868698915)
                ·
                  refine ⟨57451001656948249303048373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38300667771298832868698915 57451001656948249303048373)
                  ·
                    refine ⟨5386031405338898372160785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57451001656948249303048373 5386031405338898372160785)
                    ·
                      refine ⟨4039523554004173779120589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386031405338898372160785 4039523554004173779120589)
                      ·
                        rfl

theorem cell23_7866944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_7866944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866944 prefixEnd_7866944 := by exact prefixLift 7866944
  have htrace : WordTrace (prefixWord ++ tailWord_7866944) baseStart_7866944 baseEnd_7866944 := by
    simpa [prefixWord, tailWord_7866944, baseEnd_7866944] using wordTrace_append hprefix tailTrace_7866944
  have hstable : (prefixWord ++ tailWord_7866944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866944).length < 2 ^ (prefixWord ++ tailWord_7866944).sum := by decide
  have hdescent : baseEnd_7866944 < baseStart_7866944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866961 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 2, 3, 2]
def baseStart_7866961 : Nat := 118140960795 + 7866961 * 2 ^ 59
def prefixEnd_7866961 : Nat := 4983230072969 + 3 ^ 40 * 7866961 * 2
def baseEnd_7866961 : Nat := 4039532283175300212608011

theorem tailTrace_7866961 : CollatzResearch.WordTrace tailWord_7866961 prefixEnd_7866961 4039532283175300212608011 := by
  unfold tailWord_7866961
  simp only [CollatzResearch.WordTrace]
  refine ⟨286931640052351341816840737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191287760034900894544560491 286931640052351341816840737)
  ·
    refine ⟨215198730039263506362630553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286931640052351341816840737 215198730039263506362630553)
    ·
      refine ⟨161399047529447629771972915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215198730039263506362630553 161399047529447629771972915)
      ·
        refine ⟨242098571294171444657959373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161399047529447629771972915 242098571294171444657959373)
        ·
          refine ⟨90786964235314291746734765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242098571294171444657959373 90786964235314291746734765)
          ·
            refine ⟨34045111588242859405025537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90786964235314291746734765 34045111588242859405025537)
            ·
              refine ⟨25533833691182144553769153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34045111588242859405025537 25533833691182144553769153)
              ·
                refine ⟨19150375268386608415326865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25533833691182144553769153 19150375268386608415326865)
                ·
                  refine ⟨14362781451289956311495149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19150375268386608415326865 14362781451289956311495149)
                  ·
                    refine ⟨5386043044233733616810681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14362781451289956311495149 5386043044233733616810681)
                    ·
                      refine ⟨4039532283175300212608011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386043044233733616810681 4039532283175300212608011)
                      ·
                        rfl

theorem cell23_7866961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_7866961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866961 prefixEnd_7866961 := by exact prefixLift 7866961
  have htrace : WordTrace (prefixWord ++ tailWord_7866961) baseStart_7866961 baseEnd_7866961 := by
    simpa [prefixWord, tailWord_7866961, baseEnd_7866961] using wordTrace_append hprefix tailTrace_7866961
  have hstable : (prefixWord ++ tailWord_7866961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866961).length < 2 ^ (prefixWord ++ tailWord_7866961).sum := by decide
  have hdescent : baseEnd_7866961 < baseStart_7866961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866967 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 3, 6]
def baseStart_7866967 : Nat := 118140960795 + 7866967 * 2 ^ 59
def prefixEnd_7866967 : Nat := 4983230072969 + 3 ^ 40 * 7866967 * 2
def baseEnd_7866967 : Nat := 1346511788019742396377661

theorem tailTrace_7866967 : CollatzResearch.WordTrace tailWord_7866967 prefixEnd_7866967 1346511788019742396377661 := by
  unfold tailWord_7866967
  simp only [CollatzResearch.WordTrace]
  refine ⟨286931858890329604841559155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191287905926886403227706103 286931858890329604841559155)
  ·
    refine ⟨430397788335494407262338733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286931858890329604841559155 430397788335494407262338733)
    ·
      refine ⟨161399170625810402723377025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430397788335494407262338733 161399170625810402723377025)
      ·
        refine ⟨121049377969357802042532769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161399170625810402723377025 121049377969357802042532769)
        ·
          refine ⟨90787033477018351531899577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121049377969357802042532769 90787033477018351531899577)
          ·
            refine ⟨68090275107763763648924683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90787033477018351531899577 68090275107763763648924683)
            ·
              refine ⟨102135412661645645473387025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68090275107763763648924683 102135412661645645473387025)
              ·
                refine ⟨76601559496234234105040269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102135412661645645473387025 76601559496234234105040269)
                ·
                  refine ⟨28725584811087837789390101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76601559496234234105040269 28725584811087837789390101)
                  ·
                    refine ⟨1346511788019742396377661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28725584811087837789390101 1346511788019742396377661)
                    ·
                      rfl

theorem cell23_7866967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_7866967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866967 prefixEnd_7866967 := by exact prefixLift 7866967
  have htrace : WordTrace (prefixWord ++ tailWord_7866967) baseStart_7866967 baseEnd_7866967 := by
    simpa [prefixWord, tailWord_7866967, baseEnd_7866967] using wordTrace_append hprefix tailTrace_7866967
  have hstable : (prefixWord ++ tailWord_7866967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866967).length < 2 ^ (prefixWord ++ tailWord_7866967).sum := by decide
  have hdescent : baseEnd_7866967 < baseStart_7866967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7866991 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 5, 2, 2]
def baseStart_7866991 : Nat := 118140960795 + 7866991 * 2 ^ 59
def prefixEnd_7866991 : Nat := 4983230072969 + 3 ^ 40 * 7866991 * 2
def baseEnd_7866991 : Nat := 4039547687594935095232873

theorem tailTrace_7866991 : CollatzResearch.WordTrace tailWord_7866991 prefixEnd_7866991 4039547687594935095232873 := by
  unfold tailWord_7866991
  simp only [CollatzResearch.WordTrace]
  refine ⟨286932734242242656940432827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191288489494828437960288551 286932734242242656940432827)
  ·
    refine ⟨430399101363363985410649241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286932734242242656940432827 430399101363363985410649241)
    ·
      refine ⟨322799326022522989057986931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430399101363363985410649241 322799326022522989057986931)
      ·
        refine ⟨484198989033784483586980397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322799326022522989057986931 484198989033784483586980397)
        ·
          refine ⟨181574620887669181345117649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484198989033784483586980397 181574620887669181345117649)
          ·
            refine ⟨136180965665751886008838237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181574620887669181345117649 136180965665751886008838237)
            ·
              refine ⟨51067862124656957253314339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136180965665751886008838237 51067862124656957253314339)
              ·
                refine ⟨76601793186985435879971509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51067862124656957253314339 76601793186985435879971509)
                ·
                  refine ⟨7181418111279884613747329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76601793186985435879971509 7181418111279884613747329)
                  ·
                    refine ⟨5386063583459913460310497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7181418111279884613747329 5386063583459913460310497)
                    ·
                      refine ⟨4039547687594935095232873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386063583459913460310497 4039547687594935095232873)
                      ·
                        rfl

theorem cell23_7866991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 2, 2].length) (baseStart_7866991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7866991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7866991 prefixEnd_7866991 := by exact prefixLift 7866991
  have htrace : WordTrace (prefixWord ++ tailWord_7866991) baseStart_7866991 baseEnd_7866991 := by
    simpa [prefixWord, tailWord_7866991, baseEnd_7866991] using wordTrace_append hprefix tailTrace_7866991
  have hstable : (prefixWord ++ tailWord_7866991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7866991).length < 2 ^ (prefixWord ++ tailWord_7866991).sum := by decide
  have hdescent : baseEnd_7866991 < baseStart_7866991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7866991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867004 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_7867004 : Nat := 118140960795 + 7867004 * 2 ^ 59
def prefixEnd_7867004 : Nat := 4983230072969 + 3 ^ 40 * 7867004 * 2
def baseEnd_7867004 : Nat := 4039554362843443544370313

theorem tailTrace_7867004 : CollatzResearch.WordTrace tailWord_7867004 prefixEnd_7867004 4039554362843443544370313 := by
  unfold tailWord_7867004
  simp only [CollatzResearch.WordTrace]
  refine ⟨143466604195597780080328033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191288805594130373440437377 143466604195597780080328033)
  ·
    refine ⟨107599953146698335060246025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143466604195597780080328033 107599953146698335060246025)
    ·
      refine ⟨80699964860023751295184519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107599953146698335060246025 80699964860023751295184519)
      ·
        refine ⟨121049947290035626942776779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80699964860023751295184519 121049947290035626942776779)
        ·
          refine ⟨181574920935053440414165169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121049947290035626942776779 181574920935053440414165169)
          ·
            refine ⟨136181190701290080310623877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181574920935053440414165169 136181190701290080310623877)
            ·
              refine ⟨25533973256491890058241977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136181190701290080310623877 25533973256491890058241977)
              ·
                refine ⟨19150479942368917543681483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25533973256491890058241977 19150479942368917543681483)
                ·
                  refine ⟨28725719913553376315522225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19150479942368917543681483 28725719913553376315522225)
                  ·
                    refine ⟨21544289935165032236641669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28725719913553376315522225 21544289935165032236641669)
                    ·
                      refine ⟨4039554362843443544370313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21544289935165032236641669 4039554362843443544370313)
                      ·
                        rfl

theorem cell23_7867004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_7867004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867004 prefixEnd_7867004 := by exact prefixLift 7867004
  have htrace : WordTrace (prefixWord ++ tailWord_7867004) baseStart_7867004 baseEnd_7867004 := by
    simpa [prefixWord, tailWord_7867004, baseEnd_7867004] using wordTrace_append hprefix tailTrace_7867004
  have hstable : (prefixWord ++ tailWord_7867004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867004).length < 2 ^ (prefixWord ++ tailWord_7867004).sum := by decide
  have hdescent : baseEnd_7867004 < baseStart_7867004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867005 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_7867005 : Nat := 118140960795 + 7867005 * 2 ^ 59
def prefixEnd_7867005 : Nat := 4983230072969 + 3 ^ 40 * 7867005 * 2
def baseEnd_7867005 : Nat := 1346518292108032680152603

theorem tailTrace_7867005 : CollatzResearch.WordTrace tailWord_7867005 prefixEnd_7867005 1346518292108032680152603 := by
  unfold tailWord_7867005
  simp only [CollatzResearch.WordTrace]
  refine ⟨286933244864191937331442469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191288829909461291554294979 286933244864191937331442469)
  ·
    refine ⟨53799983412035988249645463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286933244864191937331442469 53799983412035988249645463)
    ·
      refine ⟨80699975118053982374468195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53799983412035988249645463 80699975118053982374468195)
      ·
        refine ⟨121049962677080973561702293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80699975118053982374468195 121049962677080973561702293)
        ·
          refine ⟨5674217000488170635704795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121049962677080973561702293 5674217000488170635704795)
          ·
            refine ⟨8511325500732255953557193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5674217000488170635704795 8511325500732255953557193)
            ·
              refine ⟨6383494125549191965167895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8511325500732255953557193 6383494125549191965167895)
              ·
                refine ⟨9575241188323787947751843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383494125549191965167895 9575241188323787947751843)
                ·
                  refine ⟨14362861782485681921627765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575241188323787947751843 14362861782485681921627765)
                  ·
                    refine ⟨1346518292108032680152603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14362861782485681921627765 1346518292108032680152603)
                    ·
                      rfl

theorem cell23_7867005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_7867005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867005 prefixEnd_7867005 := by exact prefixLift 7867005
  have htrace : WordTrace (prefixWord ++ tailWord_7867005) baseStart_7867005 baseEnd_7867005 := by
    simpa [prefixWord, tailWord_7867005, baseEnd_7867005] using wordTrace_append hprefix tailTrace_7867005
  have hstable : (prefixWord ++ tailWord_7867005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867005).length < 2 ^ (prefixWord ++ tailWord_7867005).sum := by decide
  have hdescent : baseEnd_7867005 < baseStart_7867005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867008 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 1, 1, 4]
def baseStart_7867008 : Nat := 118140960795 + 7867008 * 2 ^ 59
def prefixEnd_7867008 : Nat := 4983230072969 + 3 ^ 40 * 7867008 * 2
def baseEnd_7867008 : Nat := 4039556416766061528720295

theorem tailTrace_7867008 : CollatzResearch.WordTrace tailWord_7867008 prefixEnd_7867008 4039556416766061528720295 := by
  unfold tailWord_7867008
  simp only [CollatzResearch.WordTrace]
  refine ⟨143466677141590534421900839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191288902855454045895867785 143466677141590534421900839)
  ·
    refine ⟨215200015712385801632851259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143466677141590534421900839 215200015712385801632851259)
    ·
      refine ⟨322800023568578702449276889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215200015712385801632851259 322800023568578702449276889)
      ·
        refine ⟨242100017676434026836957667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322800023568578702449276889 242100017676434026836957667)
        ·
          refine ⟨363150026514651040255436501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242100017676434026836957667 363150026514651040255436501)
          ·
            refine ⟨8511328746437133755986793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 363150026514651040255436501 8511328746437133755986793)
            ·
              refine ⟨6383496559827850316990095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8511328746437133755986793 6383496559827850316990095)
              ·
                refine ⟨9575244839741775475485143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383496559827850316990095 9575244839741775475485143)
                ·
                  refine ⟨14362867259612663213227715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575244839741775475485143 14362867259612663213227715)
                  ·
                    refine ⟨21544300889418994819841573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14362867259612663213227715 21544300889418994819841573)
                    ·
                      refine ⟨4039556416766061528720295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21544300889418994819841573 4039556416766061528720295)
                      ·
                        rfl

theorem cell23_7867008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_7867008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867008 prefixEnd_7867008 := by exact prefixLift 7867008
  have htrace : WordTrace (prefixWord ++ tailWord_7867008) baseStart_7867008 baseEnd_7867008 := by
    simpa [prefixWord, tailWord_7867008, baseEnd_7867008] using wordTrace_append hprefix tailTrace_7867008
  have hstable : (prefixWord ++ tailWord_7867008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867008).length < 2 ^ (prefixWord ++ tailWord_7867008).sum := by decide
  have hdescent : baseEnd_7867008 < baseStart_7867008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867017 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_7867017 : Nat := 118140960795 + 7867017 * 2 ^ 59
def prefixEnd_7867017 : Nat := 4983230072969 + 3 ^ 40 * 7867017 * 2
def baseEnd_7867017 : Nat := 4039561038091951993507753

theorem tailTrace_7867017 : CollatzResearch.WordTrace tailWord_7867017 prefixEnd_7867017 4039561038091951993507753 := by
  unfold tailWord_7867017
  simp only [CollatzResearch.WordTrace]
  refine ⟨286933682540148463380879305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191289121693432308920586203 286933682540148463380879305)
  ·
    refine ⟨215200261905111347535659479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286933682540148463380879305 215200261905111347535659479)
    ·
      refine ⟨322800392857667021303489219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215200261905111347535659479 322800392857667021303489219)
      ·
        refine ⟨484200589286500531955233829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322800392857667021303489219 484200589286500531955233829)
        ·
          refine ⟨90787610491218849741606343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484200589286500531955233829 90787610491218849741606343)
          ·
            refine ⟨136181415736828274612409515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90787610491218849741606343 136181415736828274612409515)
            ·
              refine ⟨204272123605242411918614273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136181415736828274612409515 204272123605242411918614273)
              ·
                refine ⟨153204092703931808938960705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204272123605242411918614273 153204092703931808938960705)
                ·
                  refine ⟨114903069527948856704220529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153204092703931808938960705 114903069527948856704220529)
                  ·
                    refine ⟨86177302145961642528165397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114903069527948856704220529 86177302145961642528165397)
                    ·
                      refine ⟨4039561038091951993507753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86177302145961642528165397 4039561038091951993507753)
                      ·
                        rfl

theorem cell23_7867017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_7867017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867017 prefixEnd_7867017 := by exact prefixLift 7867017
  have htrace : WordTrace (prefixWord ++ tailWord_7867017) baseStart_7867017 baseEnd_7867017 := by
    simpa [prefixWord, tailWord_7867017, baseEnd_7867017] using wordTrace_append hprefix tailTrace_7867017
  have hstable : (prefixWord ++ tailWord_7867017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867017).length < 2 ^ (prefixWord ++ tailWord_7867017).sum := by decide
  have hdescent : baseEnd_7867017 < baseStart_7867017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867068 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7867068 : Nat := 118140960795 + 7867068 * 2 ^ 59
def prefixEnd_7867068 : Nat := 4983230072969 + 3 ^ 40 * 7867068 * 2
def baseEnd_7867068 : Nat := 4039587225605331293970019

theorem tailTrace_7867068 : CollatzResearch.WordTrace tailWord_7867068 prefixEnd_7867068 4039587225605331293970019 := by
  unfold tailWord_7867068
  simp only [CollatzResearch.WordTrace]
  refine ⟨143467771331481849545492929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191290361775309132727323905 143467771331481849545492929)
  ·
    refine ⟨107600828498611387159119697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143467771331481849545492929 107600828498611387159119697)
    ·
      refine ⟨80700621373958540369339773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107600828498611387159119697 80700621373958540369339773)
      ·
        refine ⟨30262733015234452638502415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80700621373958540369339773 30262733015234452638502415)
        ·
          refine ⟨45394099522851678957753623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30262733015234452638502415 45394099522851678957753623)
          ·
            refine ⟨68091149284277518436630435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45394099522851678957753623 68091149284277518436630435)
            ·
              refine ⟨102136723926416277654945653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68091149284277518436630435 102136723926416277654945653)
              ·
                refine ⟨9575317868101526030151155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102136723926416277654945653 9575317868101526030151155)
                ·
                  refine ⟨14362976802152289045226733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575317868101526030151155 14362976802152289045226733)
                  ·
                    refine ⟨5386116300807108391960025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14362976802152289045226733 5386116300807108391960025)
                    ·
                      refine ⟨4039587225605331293970019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386116300807108391960025 4039587225605331293970019)
                      ·
                        rfl

theorem cell23_7867068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7867068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867068 prefixEnd_7867068 := by exact prefixLift 7867068
  have htrace : WordTrace (prefixWord ++ tailWord_7867068) baseStart_7867068 baseEnd_7867068 := by
    simpa [prefixWord, tailWord_7867068, baseEnd_7867068] using wordTrace_append hprefix tailTrace_7867068
  have hstable : (prefixWord ++ tailWord_7867068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867068).length < 2 ^ (prefixWord ++ tailWord_7867068).sum := by decide
  have hdescent : baseEnd_7867068 < baseStart_7867068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867121 : List Nat := [1, 2, 2, 2, 2, 2, 2, 5, 5]
def baseStart_7867121 : Nat := 118140960795 + 7867121 * 2 ^ 59
def prefixEnd_7867121 : Nat := 4983230072969 + 3 ^ 40 * 7867121 * 2
def baseEnd_7867121 : Nat := 448846048897779954067475

theorem tailTrace_7867121 : CollatzResearch.WordTrace tailWord_7867121 prefixEnd_7867121 448846048897779954067475 := by
  unfold tailWord_7867121
  simp only [CollatzResearch.WordTrace]
  refine ⟨286937475731771689142665217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191291650487847792761776811 286937475731771689142665217)
  ·
    refine ⟨215203106798828766856998913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286937475731771689142665217 215203106798828766856998913)
    ·
      refine ⟨161402330099121575142749185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215203106798828766856998913 161402330099121575142749185)
      ·
        refine ⟨121051747574341181357061889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161402330099121575142749185 121051747574341181357061889)
        ·
          refine ⟨90788810680755886017796417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121051747574341181357061889 90788810680755886017796417)
          ·
            refine ⟨68091608010566914513347313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90788810680755886017796417 68091608010566914513347313)
            ·
              refine ⟨51068706007925185885010485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68091608010566914513347313 51068706007925185885010485)
              ·
                refine ⟨4787691188242986176719733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51068706007925185885010485 4787691188242986176719733)
                ·
                  refine ⟨448846048897779954067475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4787691188242986176719733 448846048897779954067475)
                  ·
                    rfl

theorem cell23_7867121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 5].length) (baseStart_7867121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867121 prefixEnd_7867121 := by exact prefixLift 7867121
  have htrace : WordTrace (prefixWord ++ tailWord_7867121) baseStart_7867121 baseEnd_7867121 := by
    simpa [prefixWord, tailWord_7867121, baseEnd_7867121] using wordTrace_append hprefix tailTrace_7867121
  have hstable : (prefixWord ++ tailWord_7867121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867121).length < 2 ^ (prefixWord ++ tailWord_7867121).sum := by decide
  have hdescent : baseEnd_7867121 < baseStart_7867121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867168 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 2, 5]
def baseStart_7867168 : Nat := 118140960795 + 7867168 * 2 ^ 59
def prefixEnd_7867168 : Nat := 4983230072969 + 3 ^ 40 * 7867168 * 2
def baseEnd_7867168 : Nat := 1346546191223593634239853

theorem tailTrace_7867168 : CollatzResearch.WordTrace tailWord_7867168 prefixEnd_7867168 1346546191223593634239853 := by
  unfold tailWord_7867168
  simp only [CollatzResearch.WordTrace]
  refine ⟨143469594981300708084813079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191292793308400944113084105 143469594981300708084813079)
  ·
    refine ⟨215204392471951062127219619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143469594981300708084813079 215204392471951062127219619)
    ·
      refine ⟨322806588707926593190829429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215204392471951062127219619 322806588707926593190829429)
      ·
        refine ⟨30263117691368118111640259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322806588707926593190829429 30263117691368118111640259)
        ·
          refine ⟨45394676537052177167460389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30263117691368118111640259 45394676537052177167460389)
          ·
            refine ⟨8511501850697283218898823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45394676537052177167460389 8511501850697283218898823)
            ·
              refine ⟨12767252776045924828348235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8511501850697283218898823 12767252776045924828348235)
              ·
                refine ⟨19150879164068887242522353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12767252776045924828348235 19150879164068887242522353)
                ·
                  refine ⟨14363159373051665431891765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19150879164068887242522353 14363159373051665431891765)
                  ·
                    refine ⟨1346546191223593634239853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14363159373051665431891765 1346546191223593634239853)
                    ·
                      rfl

theorem cell23_7867168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_7867168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867168 prefixEnd_7867168 := by exact prefixLift 7867168
  have htrace : WordTrace (prefixWord ++ tailWord_7867168) baseStart_7867168 baseEnd_7867168 := by
    simpa [prefixWord, tailWord_7867168, baseEnd_7867168] using wordTrace_append hprefix tailTrace_7867168
  have hstable : (prefixWord ++ tailWord_7867168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867168).length < 2 ^ (prefixWord ++ tailWord_7867168).sum := by decide
  have hdescent : baseEnd_7867168 < baseStart_7867168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867171 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 3, 6, 2]
def baseStart_7867171 : Nat := 118140960795 + 7867171 * 2 ^ 59
def prefixEnd_7867171 : Nat := 4983230072969 + 3 ^ 40 * 7867171 * 2
def baseEnd_7867171 : Nat := 4039640114112744390982045

theorem tailTrace_7867171 : CollatzResearch.WordTrace tailWord_7867171 prefixEnd_7867171 4039640114112744390982045 := by
  unfold tailWord_7867171
  simp only [CollatzResearch.WordTrace]
  refine ⟨286939299381590547681985367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191292866254393698454656911 286939299381590547681985367)
  ·
    refine ⟨430408949072385821522978051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286939299381590547681985367 430408949072385821522978051)
    ·
      refine ⟨645613423608578732284467077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430408949072385821522978051 645613423608578732284467077)
      ·
        refine ⟨121052516926608512303337577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 645613423608578732284467077 121052516926608512303337577)
        ·
          refine ⟨90789387694956384227503183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121052516926608512303337577 90789387694956384227503183)
          ·
            refine ⟨136184081542434576341254775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90789387694956384227503183 136184081542434576341254775)
            ·
              refine ⟨204276122313651864511882163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136184081542434576341254775 204276122313651864511882163)
              ·
                refine ⟨306414183470477796767823245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204276122313651864511882163 306414183470477796767823245)
                ·
                  refine ⟨114905318801429173787933717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306414183470477796767823245 114905318801429173787933717)
                  ·
                    refine ⟨5386186818816992521309393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114905318801429173787933717 5386186818816992521309393)
                    ·
                      refine ⟨4039640114112744390982045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386186818816992521309393 4039640114112744390982045)
                      ·
                        rfl

theorem cell23_7867171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_7867171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867171 prefixEnd_7867171 := by exact prefixLift 7867171
  have htrace : WordTrace (prefixWord ++ tailWord_7867171) baseStart_7867171 baseEnd_7867171 := by
    simpa [prefixWord, tailWord_7867171, baseEnd_7867171] using wordTrace_append hprefix tailTrace_7867171
  have hstable : (prefixWord ++ tailWord_7867171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867171).length < 2 ^ (prefixWord ++ tailWord_7867171).sum := by decide
  have hdescent : baseEnd_7867171 < baseStart_7867171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867184 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_7867184 : Nat := 118140960795 + 7867184 * 2 ^ 59
def prefixEnd_7867184 : Nat := 4983230072969 + 3 ^ 40 * 7867184 * 2
def baseEnd_7867184 : Nat := 4039646789361252840119485

theorem tailTrace_7867184 : CollatzResearch.WordTrace tailWord_7867184 prefixEnd_7867184 4039646789361252840119485 := by
  unfold tailWord_7867184
  simp only [CollatzResearch.WordTrace]
  refine ⟨143469886765271725451104303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191293182353695633934805737 143469886765271725451104303)
  ·
    refine ⟨215204830147907588176656455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143469886765271725451104303 215204830147907588176656455)
    ·
      refine ⟨322807245221861382264984683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215204830147907588176656455 322807245221861382264984683)
      ·
        refine ⟨484210867832792073397477025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322807245221861382264984683 484210867832792073397477025)
        ·
          refine ⟨363158150874594055048107769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484210867832792073397477025 363158150874594055048107769)
          ·
            refine ⟨272368613155945541286080827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363158150874594055048107769 272368613155945541286080827)
            ·
              refine ⟨408552919733918311929121241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272368613155945541286080827 408552919733918311929121241)
              ·
                refine ⟨306414689800438733946840931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408552919733918311929121241 306414689800438733946840931)
                ·
                  refine ⟨459622034700658100920261397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306414689800438733946840931 459622034700658100920261397)
                  ·
                    refine ⟨21544782876593348480637253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 459622034700658100920261397 21544782876593348480637253)
                    ·
                      refine ⟨4039646789361252840119485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21544782876593348480637253 4039646789361252840119485)
                      ·
                        rfl

theorem cell23_7867184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_7867184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867184 prefixEnd_7867184 := by exact prefixLift 7867184
  have htrace : WordTrace (prefixWord ++ tailWord_7867184) baseStart_7867184 baseEnd_7867184 := by
    simpa [prefixWord, tailWord_7867184, baseEnd_7867184] using wordTrace_append hprefix tailTrace_7867184
  have hstable : (prefixWord ++ tailWord_7867184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867184).length < 2 ^ (prefixWord ++ tailWord_7867184).sum := by decide
  have hdescent : baseEnd_7867184 < baseStart_7867184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867191 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_7867191 : Nat := 118140960795 + 7867191 * 2 ^ 59
def prefixEnd_7867191 : Nat := 4983230072969 + 3 ^ 40 * 7867191 * 2
def baseEnd_7867191 : Nat := 4039650383725834312731953

theorem tailTrace_7867191 : CollatzResearch.WordTrace tailWord_7867191 prefixEnd_7867191 4039650383725834312731953 := by
  unfold tailWord_7867191
  simp only [CollatzResearch.WordTrace]
  refine ⟨286940028841518091097713427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191293352561012060731808951 286940028841518091097713427)
  ·
    refine ⟨430410043262277136646570141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286940028841518091097713427 430410043262277136646570141)
    ·
      refine ⟨161403766223353926242463803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430410043262277136646570141 161403766223353926242463803)
      ·
        refine ⟨242105649335030889363695705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161403766223353926242463803 242105649335030889363695705)
        ·
          refine ⟨181579237001273167022771779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242105649335030889363695705 181579237001273167022771779)
          ·
            refine ⟨272368855501909750534157669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181579237001273167022771779 272368855501909750534157669)
            ·
              refine ⟨51069160406608078225154563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272368855501909750534157669 51069160406608078225154563)
              ·
                refine ⟨76603740609912117337731845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51069160406608078225154563 76603740609912117337731845)
                ·
                  refine ⟨14363201364358522000824721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76603740609912117337731845 14363201364358522000824721)
                  ·
                    refine ⟨10772401023268891500618541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14363201364358522000824721 10772401023268891500618541)
                    ·
                      refine ⟨4039650383725834312731953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10772401023268891500618541 4039650383725834312731953)
                      ·
                        rfl

theorem cell23_7867191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_7867191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867191 prefixEnd_7867191 := by exact prefixLift 7867191
  have htrace : WordTrace (prefixWord ++ tailWord_7867191) baseStart_7867191 baseEnd_7867191 := by
    simpa [prefixWord, tailWord_7867191, baseEnd_7867191] using wordTrace_append hprefix tailTrace_7867191
  have hstable : (prefixWord ++ tailWord_7867191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867191).length < 2 ^ (prefixWord ++ tailWord_7867191).sum := by decide
  have hdescent : baseEnd_7867191 < baseStart_7867191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867221 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_7867221 : Nat := 118140960795 + 7867221 * 2 ^ 59
def prefixEnd_7867221 : Nat := 4983230072969 + 3 ^ 40 * 7867221 * 2
def baseEnd_7867221 : Nat := 4039665788145469195356815

theorem tailTrace_7867221 : CollatzResearch.WordTrace tailWord_7867221 prefixEnd_7867221 4039665788145469195356815 := by
  unfold tailWord_7867221
  simp only [CollatzResearch.WordTrace]
  refine ⟨286941123031409406221305517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191294082020939604147537011 286941123031409406221305517)
  ·
    refine ⟨107602921136778527332989569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286941123031409406221305517 107602921136778527332989569)
    ·
      refine ⟨80702190852583895499742177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107602921136778527332989569 80702190852583895499742177)
      ·
        refine ⟨60526643139437921624806633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80702190852583895499742177 60526643139437921624806633)
        ·
          refine ⟨45394982354578441218604975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60526643139437921624806633 45394982354578441218604975)
          ·
            refine ⟨68092473531867661827907463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45394982354578441218604975 68092473531867661827907463)
            ·
              refine ⟨102138710297801492741861195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68092473531867661827907463 102138710297801492741861195)
              ·
                refine ⟨153208065446702239112791793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102138710297801492741861195 153208065446702239112791793)
                ·
                  refine ⟨114906049085026679334593845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153208065446702239112791793 114906049085026679334593845)
                  ·
                    refine ⟨10772442101721251187618173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114906049085026679334593845 10772442101721251187618173)
                    ·
                      refine ⟨4039665788145469195356815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10772442101721251187618173 4039665788145469195356815)
                      ·
                        rfl

theorem cell23_7867221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_7867221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867221 prefixEnd_7867221 := by exact prefixLift 7867221
  have htrace : WordTrace (prefixWord ++ tailWord_7867221) baseStart_7867221 baseEnd_7867221 := by
    simpa [prefixWord, tailWord_7867221, baseEnd_7867221] using wordTrace_append hprefix tailTrace_7867221
  have hstable : (prefixWord ++ tailWord_7867221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867221).length < 2 ^ (prefixWord ++ tailWord_7867221).sum := by decide
  have hdescent : baseEnd_7867221 < baseStart_7867221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867224 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 9]
def baseStart_7867224 : Nat := 118140960795 + 7867224 * 2 ^ 59
def prefixEnd_7867224 : Nat := 4983230072969 + 3 ^ 40 * 7867224 * 2
def baseEnd_7867224 : Nat := 1346555776195810894539767

theorem tailTrace_7867224 : CollatzResearch.WordTrace tailWord_7867224 prefixEnd_7867224 1346555776195810894539767 := by
  unfold tailWord_7867224
  simp only [CollatzResearch.WordTrace]
  refine ⟨143470616225199268866832363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191294154966932358489109817 143470616225199268866832363)
  ·
    refine ⟨215205924337798903300248545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143470616225199268866832363 215205924337798903300248545)
    ·
      refine ⟨161404443253349177475186409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215205924337798903300248545 161404443253349177475186409)
      ·
        refine ⟨121053332440011883106389807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161404443253349177475186409 121053332440011883106389807)
        ·
          refine ⟨181579998660017824659584711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121053332440011883106389807 181579998660017824659584711)
          ·
            refine ⟨272369997990026736989377067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181579998660017824659584711 272369997990026736989377067)
            ·
              refine ⟨408554996985040105484065601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272369997990026736989377067 408554996985040105484065601)
              ·
                refine ⟨306416247738780079113049201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408554996985040105484065601 306416247738780079113049201)
                ·
                  refine ⟨229812185804085059334786901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306416247738780079113049201 229812185804085059334786901)
                  ·
                    refine ⟨1346555776195810894539767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 229812185804085059334786901 1346555776195810894539767)
                    ·
                      rfl

theorem cell23_7867224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_7867224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867224 prefixEnd_7867224 := by exact prefixLift 7867224
  have htrace : WordTrace (prefixWord ++ tailWord_7867224) baseStart_7867224 baseEnd_7867224 := by
    simpa [prefixWord, tailWord_7867224, baseEnd_7867224] using wordTrace_append hprefix tailTrace_7867224
  have hstable : (prefixWord ++ tailWord_7867224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867224).length < 2 ^ (prefixWord ++ tailWord_7867224).sum := by decide
  have hdescent : baseEnd_7867224 < baseStart_7867224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867248 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 4, 3, 2]
def baseStart_7867248 : Nat := 118140960795 + 7867248 * 2 ^ 59
def prefixEnd_7867248 : Nat := 4983230072969 + 3 ^ 40 * 7867248 * 2
def baseEnd_7867248 : Nat := 4039679652123140589719191

theorem tailTrace_7867248 : CollatzResearch.WordTrace tailWord_7867248 prefixEnd_7867248 4039679652123140589719191 := by
  unfold tailWord_7867248
  simp only [CollatzResearch.WordTrace]
  refine ⟨143471053901155794916269199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191294738534874393221692265 143471053901155794916269199)
  ·
    refine ⟨215206580851733692374403799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143471053901155794916269199 215206580851733692374403799)
    ·
      refine ⟨322809871277600538561605699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215206580851733692374403799 322809871277600538561605699)
      ·
        refine ⟨484214806916400807842408549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322809871277600538561605699 484214806916400807842408549)
        ·
          refine ⟨90790276296825151470451603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484214806916400807842408549 90790276296825151470451603)
          ·
            refine ⟨136185414445237727205677405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90790276296825151470451603 136185414445237727205677405)
            ·
              refine ⟨51069530416964147702129027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136185414445237727205677405 51069530416964147702129027)
              ·
                refine ⟨76604295625446221553193541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51069530416964147702129027 76604295625446221553193541)
                ·
                  refine ⟨14363305429771166541223789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76604295625446221553193541 14363305429771166541223789)
                  ·
                    refine ⟨5386239536164187452958921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14363305429771166541223789 5386239536164187452958921)
                    ·
                      refine ⟨4039679652123140589719191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386239536164187452958921 4039679652123140589719191)
                      ·
                        rfl

theorem cell23_7867248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 3, 2].length) (baseStart_7867248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867248 prefixEnd_7867248 := by exact prefixLift 7867248
  have htrace : WordTrace (prefixWord ++ tailWord_7867248) baseStart_7867248 baseEnd_7867248 := by
    simpa [prefixWord, tailWord_7867248, baseEnd_7867248] using wordTrace_append hprefix tailTrace_7867248
  have hstable : (prefixWord ++ tailWord_7867248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867248).length < 2 ^ (prefixWord ++ tailWord_7867248).sum := by decide
  have hdescent : baseEnd_7867248 < baseStart_7867248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867255 : List Nat := [1, 1, 3, 1, 1, 2, 1, 8, 1, 1, 3]
def baseStart_7867255 : Nat := 118140960795 + 7867255 * 2 ^ 59
def prefixEnd_7867255 : Nat := 4983230072969 + 3 ^ 40 * 7867255 * 2
def baseEnd_7867255 : Nat := 4039683246487722062331659

theorem tailTrace_7867255 : CollatzResearch.WordTrace tailWord_7867255 prefixEnd_7867255 4039683246487722062331659 := by
  unfold tailWord_7867255
  simp only [CollatzResearch.WordTrace]
  refine ⟨286942363113286230028043219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191294908742190820018695479 286942363113286230028043219)
  ·
    refine ⟨430413544669929345042064829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286942363113286230028043219 430413544669929345042064829)
    ·
      refine ⟨161405079251223504390774311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430413544669929345042064829 161405079251223504390774311)
      ·
        refine ⟨242107618876835256586161467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161405079251223504390774311 242107618876835256586161467)
        ·
          refine ⟨363161428315252884879242201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242107618876835256586161467 363161428315252884879242201)
          ·
            refine ⟨272371071236439663659431651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363161428315252884879242201 272371071236439663659431651)
            ·
              refine ⟨408556606854659495489147477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272371071236439663659431651 408556606854659495489147477)
              ·
                refine ⟨4787772736578040962763447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 408556606854659495489147477 4787772736578040962763447)
                ·
                  refine ⟨7181659104867061444145171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787772736578040962763447 7181659104867061444145171)
                  ·
                    refine ⟨10772488657300592166217757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7181659104867061444145171 10772488657300592166217757)
                    ·
                      refine ⟨4039683246487722062331659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10772488657300592166217757 4039683246487722062331659)
                      ·
                        rfl

theorem cell23_7867255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_7867255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867255 prefixEnd_7867255 := by exact prefixLift 7867255
  have htrace : WordTrace (prefixWord ++ tailWord_7867255) baseStart_7867255 baseEnd_7867255 := by
    simpa [prefixWord, tailWord_7867255, baseEnd_7867255] using wordTrace_append hprefix tailTrace_7867255
  have hstable : (prefixWord ++ tailWord_7867255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867255).length < 2 ^ (prefixWord ++ tailWord_7867255).sum := by decide
  have hdescent : baseEnd_7867255 < baseStart_7867255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867292 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_7867292 : Nat := 118140960795 + 7867292 * 2 ^ 59
def prefixEnd_7867292 : Nat := 4983230072969 + 3 ^ 40 * 7867292 * 2
def baseEnd_7867292 : Nat := 1346567415090646139189663

theorem tailTrace_7867292 : CollatzResearch.WordTrace tailWord_7867292 prefixEnd_7867292 1346567415090646139189663 := by
  unfold tailWord_7867292
  simp only [CollatzResearch.WordTrace]
  refine ⟨143471856307076092673570065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191295808409434790231426753 143471856307076092673570065)
  ·
    refine ⟨107603892230307069505177549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143471856307076092673570065 107603892230307069505177549)
    ·
      refine ⟨40351459586365151064441581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107603892230307069505177549 40351459586365151064441581)
      ·
        refine ⟨15131797344886931649165593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40351459586365151064441581 15131797344886931649165593)
        ·
          refine ⟨11348848008665198736874195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15131797344886931649165593 11348848008665198736874195)
          ·
            refine ⟨17023272012997798105311293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11348848008665198736874195 17023272012997798105311293)
            ·
              refine ⟨6383727004874174289491735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17023272012997798105311293 6383727004874174289491735)
              ·
                refine ⟨9575590507311261434237603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383727004874174289491735 9575590507311261434237603)
                ·
                  refine ⟨14363385760966892151356405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575590507311261434237603 14363385760966892151356405)
                  ·
                    refine ⟨1346567415090646139189663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14363385760966892151356405 1346567415090646139189663)
                    ·
                      rfl

theorem cell23_7867292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_7867292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867292 prefixEnd_7867292 := by exact prefixLift 7867292
  have htrace : WordTrace (prefixWord ++ tailWord_7867292) baseStart_7867292 baseEnd_7867292 := by
    simpa [prefixWord, tailWord_7867292, baseEnd_7867292] using wordTrace_append hprefix tailTrace_7867292
  have hstable : (prefixWord ++ tailWord_7867292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867292).length < 2 ^ (prefixWord ++ tailWord_7867292).sum := by decide
  have hdescent : baseEnd_7867292 < baseStart_7867292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867325 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_7867325 : Nat := 118140960795 + 7867325 * 2 ^ 59
def prefixEnd_7867325 : Nat := 4983230072969 + 3 ^ 40 * 7867325 * 2
def baseEnd_7867325 : Nat := 4039719190133536788456337

theorem tailTrace_7867325 : CollatzResearch.WordTrace tailWord_7867325 prefixEnd_7867325 4039719190133536788456337 := by
  unfold tailWord_7867325
  simp only [CollatzResearch.WordTrace]
  refine ⟨286944916223032631983091429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191296610815355087988727619 286944916223032631983091429)
  ·
    refine ⟨53802171791818618496829643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286944916223032631983091429 53802171791818618496829643)
    ·
      refine ⟨80703257687727927745244465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53802171791818618496829643 80703257687727927745244465)
      ·
        refine ⟨60527443265795945808933349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80703257687727927745244465 60527443265795945808933349)
        ·
          refine ⟨11348895612336739839175003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60527443265795945808933349 11348895612336739839175003)
          ·
            refine ⟨17023343418505109758762505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11348895612336739839175003 17023343418505109758762505)
            ·
              refine ⟨12767507563878832319071879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17023343418505109758762505 12767507563878832319071879)
              ·
                refine ⟨19151261345818248478607819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12767507563878832319071879 19151261345818248478607819)
                ·
                  refine ⟨28726892018727372717911729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19151261345818248478607819 28726892018727372717911729)
                  ·
                    refine ⟨21545169014045529538433797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28726892018727372717911729 21545169014045529538433797)
                    ·
                      refine ⟨4039719190133536788456337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21545169014045529538433797 4039719190133536788456337)
                      ·
                        rfl

theorem cell23_7867325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_7867325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867325 prefixEnd_7867325 := by exact prefixLift 7867325
  have htrace : WordTrace (prefixWord ++ tailWord_7867325) baseStart_7867325 baseEnd_7867325 := by
    simpa [prefixWord, tailWord_7867325, baseEnd_7867325] using wordTrace_append hprefix tailTrace_7867325
  have hstable : (prefixWord ++ tailWord_7867325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867325).length < 2 ^ (prefixWord ++ tailWord_7867325).sum := by decide
  have hdescent : baseEnd_7867325 < baseStart_7867325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867328 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3]
def baseStart_7867328 : Nat := 118140960795 + 7867328 * 2 ^ 59
def prefixEnd_7867328 : Nat := 4983230072969 + 3 ^ 40 * 7867328 * 2
def baseEnd_7867328 : Nat := 4039720730575500276718823

theorem tailTrace_7867328 : CollatzResearch.WordTrace tailWord_7867328 prefixEnd_7867328 4039720730575500276718823 := by
  unfold tailWord_7867328
  simp only [CollatzResearch.WordTrace]
  refine ⟨143472512821010881747725319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191296683761347842330300425 143472512821010881747725319)
  ·
    refine ⟨215208769231516322621587979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143472512821010881747725319 215208769231516322621587979)
    ·
      refine ⟨322813153847274483932381969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215208769231516322621587979 322813153847274483932381969)
      ·
        refine ⟨242109865385455862949286477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322813153847274483932381969 242109865385455862949286477)
        ·
          refine ⟨90791199519545948605982429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242109865385455862949286477 90791199519545948605982429)
          ·
            refine ⟨34046699819829730727243411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90791199519545948605982429 34046699819829730727243411)
            ·
              refine ⟨51070049729744596090865117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34046699819829730727243411 51070049729744596090865117)
              ·
                refine ⟨19151268648654223534074419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51070049729744596090865117 19151268648654223534074419)
                ·
                  refine ⟨28726902972981335301111629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19151268648654223534074419 28726902972981335301111629)
                  ·
                    refine ⟨10772588614868000737916861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28726902972981335301111629 10772588614868000737916861)
                    ·
                      refine ⟨4039720730575500276718823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10772588614868000737916861 4039720730575500276718823)
                      ·
                        rfl

theorem cell23_7867328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_7867328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867328 prefixEnd_7867328 := by exact prefixLift 7867328
  have htrace : WordTrace (prefixWord ++ tailWord_7867328) baseStart_7867328 baseEnd_7867328 := by
    simpa [prefixWord, tailWord_7867328, baseEnd_7867328] using wordTrace_append hprefix tailTrace_7867328
  have hstable : (prefixWord ++ tailWord_7867328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867328).length < 2 ^ (prefixWord ++ tailWord_7867328).sum := by decide
  have hdescent : baseEnd_7867328 < baseStart_7867328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867346 : List Nat := [3, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7867346 : Nat := 118140960795 + 7867346 * 2 ^ 59
def prefixEnd_7867346 : Nat := 4983230072969 + 3 ^ 40 * 7867346 * 2
def baseEnd_7867346 : Nat := 4039729973227281206293741

theorem tailTrace_7867346 : CollatzResearch.WordTrace tailWord_7867346 prefixEnd_7867346 4039729973227281206293741 := by
  unfold tailWord_7867346
  simp only [CollatzResearch.WordTrace]
  refine ⟨71736420538989138142401473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191297121437304368379737261 71736420538989138142401473)
  ·
    refine ⟨53802315404241853606801105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71736420538989138142401473 53802315404241853606801105)
    ·
      refine ⟨40351736553181390205100829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53802315404241853606801105 40351736553181390205100829)
      ·
        refine ⟨15131901207443021326912811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40351736553181390205100829 15131901207443021326912811)
        ·
          refine ⟨22697851811164531990369217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15131901207443021326912811 22697851811164531990369217)
          ·
            refine ⟨17023388858373398992776913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22697851811164531990369217 17023388858373398992776913)
            ·
              refine ⟨12767541643780049244582685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17023388858373398992776913 12767541643780049244582685)
              ·
                refine ⟨4787828116417518466718507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12767541643780049244582685 4787828116417518466718507)
                ·
                  refine ⟨7181742174626277700077761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787828116417518466718507 7181742174626277700077761)
                  ·
                    refine ⟨5386306630969708275058321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7181742174626277700077761 5386306630969708275058321)
                    ·
                      refine ⟨4039729973227281206293741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386306630969708275058321 4039729973227281206293741)
                      ·
                        rfl

theorem cell23_7867346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7867346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867346 prefixEnd_7867346 := by exact prefixLift 7867346
  have htrace : WordTrace (prefixWord ++ tailWord_7867346) baseStart_7867346 baseEnd_7867346 := by
    simpa [prefixWord, tailWord_7867346, baseEnd_7867346] using wordTrace_append hprefix tailTrace_7867346
  have hstable : (prefixWord ++ tailWord_7867346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867346).length < 2 ^ (prefixWord ++ tailWord_7867346).sum := by decide
  have hdescent : baseEnd_7867346 < baseStart_7867346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867349 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7867349 : Nat := 118140960795 + 7867349 * 2 ^ 59
def prefixEnd_7867349 : Nat := 4983230072969 + 3 ^ 40 * 7867349 * 2
def baseEnd_7867349 : Nat := 4039731513669244694556227

theorem tailTrace_7867349 : CollatzResearch.WordTrace tailWord_7867349 prefixEnd_7867349 4039731513669244694556227 := by
  unfold tailWord_7867349
  simp only [CollatzResearch.WordTrace]
  refine ⟨286945791574945684081965101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191297194383297122721310067 286945791574945684081965101)
  ·
    refine ⟨107604671840604631530736913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286945791574945684081965101 107604671840604631530736913)
    ·
      refine ⟨80703503880453473648052685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107604671840604631530736913 80703503880453473648052685)
      ·
        refine ⟨30263813955170052618019757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80703503880453473648052685 30263813955170052618019757)
        ·
          refine ⟨11348930233188769731757409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30263813955170052618019757 11348930233188769731757409)
          ·
            refine ⟨8511697674891577298818057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11348930233188769731757409 8511697674891577298818057)
            ·
              refine ⟨6383773256168682974113543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8511697674891577298818057 6383773256168682974113543)
              ·
                refine ⟨9575659884253024461170315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383773256168682974113543 9575659884253024461170315)
                ·
                  refine ⟨14363489826379536691755473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9575659884253024461170315 14363489826379536691755473)
                  ·
                    refine ⟨10772617369784652518816605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14363489826379536691755473 10772617369784652518816605)
                    ·
                      refine ⟨4039731513669244694556227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10772617369784652518816605 4039731513669244694556227)
                      ·
                        rfl

theorem cell23_7867349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7867349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867349 prefixEnd_7867349 := by exact prefixLift 7867349
  have htrace : WordTrace (prefixWord ++ tailWord_7867349) baseStart_7867349 baseEnd_7867349 := by
    simpa [prefixWord, tailWord_7867349, baseEnd_7867349] using wordTrace_append hprefix tailTrace_7867349
  have hstable : (prefixWord ++ tailWord_7867349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867349).length < 2 ^ (prefixWord ++ tailWord_7867349).sum := by decide
  have hdescent : baseEnd_7867349 < baseStart_7867349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867351 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_7867351 : Nat := 118140960795 + 7867351 * 2 ^ 59
def prefixEnd_7867351 : Nat := 4983230072969 + 3 ^ 40 * 7867351 * 2
def baseEnd_7867351 : Nat := 4039732540630553686731217

theorem tailTrace_7867351 : CollatzResearch.WordTrace tailWord_7867351 prefixEnd_7867351 4039732540630553686731217 := by
  unfold tailWord_7867351
  simp only [CollatzResearch.WordTrace]
  refine ⟨286945864520938438423537907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191297243013958958949025271 286945864520938438423537907)
  ·
    refine ⟨430418796781407657635306861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286945864520938438423537907 430418796781407657635306861)
    ·
      refine ⟨161407048793027871613240073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430418796781407657635306861 161407048793027871613240073)
      ·
        refine ⟨121055286594770903709930055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161407048793027871613240073 121055286594770903709930055)
        ·
          refine ⟨181582929892156355564895083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121055286594770903709930055 181582929892156355564895083)
          ·
            refine ⟨272374394838234533347342625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181582929892156355564895083 272374394838234533347342625)
            ·
              refine ⟨204280796128675900010506969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272374394838234533347342625 204280796128675900010506969)
              ·
                refine ⟨153210597096506925007880227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204280796128675900010506969 153210597096506925007880227)
                ·
                  refine ⟨229815895644760387511820341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153210597096506925007880227 229815895644760387511820341)
                  ·
                    refine ⟨21545240216696286329233157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229815895644760387511820341 21545240216696286329233157)
                    ·
                      refine ⟨4039732540630553686731217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21545240216696286329233157 4039732540630553686731217)
                      ·
                        rfl

theorem cell23_7867351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_7867351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867351 prefixEnd_7867351 := by exact prefixLift 7867351
  have htrace : WordTrace (prefixWord ++ tailWord_7867351) baseStart_7867351 baseEnd_7867351 := by
    simpa [prefixWord, tailWord_7867351, baseEnd_7867351] using wordTrace_append hprefix tailTrace_7867351
  have hstable : (prefixWord ++ tailWord_7867351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867351).length < 2 ^ (prefixWord ++ tailWord_7867351).sum := by decide
  have hdescent : baseEnd_7867351 < baseStart_7867351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867371 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5]
def baseStart_7867371 : Nat := 118140960795 + 7867371 * 2 ^ 59
def prefixEnd_7867371 : Nat := 4983230072969 + 3 ^ 40 * 7867371 * 2
def baseEnd_7867371 : Nat := 4039742810243643608481125

theorem tailTrace_7867371 : CollatzResearch.WordTrace tailWord_7867371 prefixEnd_7867371 4039742810243643608481125 := by
  unfold tailWord_7867371
  simp only [CollatzResearch.WordTrace]
  refine ⟨286946593980865981839265967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191297729320577321226177311 286946593980865981839265967)
  ·
    refine ⟨430419890971298972758898951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286946593980865981839265967 430419890971298972758898951)
    ·
      refine ⟨645629836456948459138348427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430419890971298972758898951 645629836456948459138348427)
      ·
        refine ⟨968444754685422688707522641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645629836456948459138348427 968444754685422688707522641)
        ·
          refine ⟨726333566014067016530641981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968444754685422688707522641 726333566014067016530641981)
          ·
            refine ⟨272375087255275131198990743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726333566014067016530641981 272375087255275131198990743)
            ·
              refine ⟨408562630882912696798486115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272375087255275131198990743 408562630882912696798486115)
              ·
                refine ⟨612843946324369045197729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408562630882912696798486115 612843946324369045197729173)
                ·
                  refine ⟨28727059983954798993643555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 612843946324369045197729173 28727059983954798993643555)
                  ·
                    refine ⟨43090589975932198490465333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28727059983954798993643555 43090589975932198490465333)
                    ·
                      refine ⟨4039742810243643608481125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43090589975932198490465333 4039742810243643608481125)
                      ·
                        rfl

theorem cell23_7867371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_7867371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867371 prefixEnd_7867371 := by exact prefixLift 7867371
  have htrace : WordTrace (prefixWord ++ tailWord_7867371) baseStart_7867371 baseEnd_7867371 := by
    simpa [prefixWord, tailWord_7867371, baseEnd_7867371] using wordTrace_append hprefix tailTrace_7867371
  have hstable : (prefixWord ++ tailWord_7867371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867371).length < 2 ^ (prefixWord ++ tailWord_7867371).sum := by decide
  have hdescent : baseEnd_7867371 < baseStart_7867371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867402 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_7867402 : Nat := 118140960795 + 7867402 * 2 ^ 59
def prefixEnd_7867402 : Nat := 4983230072969 + 3 ^ 40 * 7867402 * 2
def baseEnd_7867402 : Nat := 4039758728143932987193483

theorem tailTrace_7867402 : CollatzResearch.WordTrace tailWord_7867402 prefixEnd_7867402 4039758728143932987193483 := by
  unfold tailWord_7867402
  simp only [CollatzResearch.WordTrace]
  refine ⟨71736931160938418533411115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191298483095835782755762973 71736931160938418533411115)
  ·
    refine ⟨107605396741407627800116673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71736931160938418533411115 107605396741407627800116673)
    ·
      refine ⟨80704047556055720850087505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107605396741407627800116673 80704047556055720850087505)
      ·
        refine ⟨60528035667041790637565629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80704047556055720850087505 60528035667041790637565629)
        ·
          refine ⟨22698013375140671489087111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60528035667041790637565629 22698013375140671489087111)
          ·
            refine ⟨34047020062711007233630667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22698013375140671489087111 34047020062711007233630667)
            ·
              refine ⟨51070530094066510850446001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34047020062711007233630667 51070530094066510850446001)
              ·
                refine ⟨38302897570549883137834501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51070530094066510850446001 38302897570549883137834501)
                ·
                  refine ⟨7181793294478103088343969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38302897570549883137834501 7181793294478103088343969)
                  ·
                    refine ⟨5386344970858577316257977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7181793294478103088343969 5386344970858577316257977)
                    ·
                      refine ⟨4039758728143932987193483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386344970858577316257977 4039758728143932987193483)
                      ·
                        rfl

theorem cell23_7867402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_7867402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867402 prefixEnd_7867402 := by exact prefixLift 7867402
  have htrace : WordTrace (prefixWord ++ tailWord_7867402) baseStart_7867402 baseEnd_7867402 := by
    simpa [prefixWord, tailWord_7867402, baseEnd_7867402] using wordTrace_append hprefix tailTrace_7867402
  have hstable : (prefixWord ++ tailWord_7867402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867402).length < 2 ^ (prefixWord ++ tailWord_7867402).sum := by decide
  have hdescent : baseEnd_7867402 < baseStart_7867402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867425 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 7]
def baseStart_7867425 : Nat := 118140960795 + 7867425 * 2 ^ 59
def prefixEnd_7867425 : Nat := 4983230072969 + 3 ^ 40 * 7867425 * 2
def baseEnd_7867425 : Nat := 448863393133220710800653

theorem tailTrace_7867425 : CollatzResearch.WordTrace tailWord_7867425 prefixEnd_7867425 448863393133220710800653 := by
  unfold tailWord_7867425
  simp only [CollatzResearch.WordTrace]
  refine ⟨286948563522670349061731729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191299042348446899374487819 286948563522670349061731729)
  ·
    refine ⟨215211422642002761796298797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286948563522670349061731729 215211422642002761796298797)
    ·
      refine ⟨80704283490751035673612049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215211422642002761796298797 80704283490751035673612049)
      ·
        refine ⟨60528212618063276755209037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80704283490751035673612049 60528212618063276755209037)
        ·
          refine ⟨22698079731773728783203389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60528212618063276755209037 22698079731773728783203389)
          ·
            refine ⟨8511779899415148293701271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22698079731773728783203389 8511779899415148293701271)
            ·
              refine ⟨12767669849122722440551907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8511779899415148293701271 12767669849122722440551907)
              ·
                refine ⟨19151504773684083660827861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12767669849122722440551907 19151504773684083660827861)
                ·
                  refine ⟨448863393133220710800653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19151504773684083660827861 448863393133220710800653)
                  ·
                    rfl

theorem cell23_7867425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 7].length) (baseStart_7867425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867425 prefixEnd_7867425 := by exact prefixLift 7867425
  have htrace : WordTrace (prefixWord ++ tailWord_7867425) baseStart_7867425 baseEnd_7867425 := by
    simpa [prefixWord, tailWord_7867425, baseEnd_7867425] using wordTrace_append hprefix tailTrace_7867425
  have hstable : (prefixWord ++ tailWord_7867425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867425).length < 2 ^ (prefixWord ++ tailWord_7867425).sum := by decide
  have hdescent : baseEnd_7867425 < baseStart_7867425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867502 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_7867502 : Nat := 118140960795 + 7867502 * 2 ^ 59
def prefixEnd_7867502 : Nat := 4983230072969 + 3 ^ 40 * 7867502 * 2
def baseEnd_7867502 : Nat := 1346603358736460865314341

theorem tailTrace_7867502 : CollatzResearch.WordTrace tailWord_7867502 prefixEnd_7867502 1346603358736460865314341 := by
  unfold tailWord_7867502
  simp only [CollatzResearch.WordTrace]
  refine ⟨35868921492923923901535595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191300914628927594141523173 35868921492923923901535595)
  ·
    refine ⟨53803382239385885852303393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35868921492923923901535595 53803382239385885852303393)
    ·
      refine ⟨40352536679539414389227545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53803382239385885852303393 40352536679539414389227545)
      ·
        refine ⟨30264402509654560791920659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40352536679539414389227545 30264402509654560791920659)
        ·
          refine ⟨45396603764481841187880989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30264402509654560791920659 45396603764481841187880989)
          ·
            refine ⟨17023726411680690445455371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45396603764481841187880989 17023726411680690445455371)
            ·
              refine ⟨25535589617521035668183057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17023726411680690445455371 25535589617521035668183057)
              ·
                refine ⟨19151692213140776751137293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25535589617521035668183057 19151692213140776751137293)
                ·
                  refine ⟨7181884579927791281676485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19151692213140776751137293 7181884579927791281676485)
                  ·
                    refine ⟨1346603358736460865314341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7181884579927791281676485 1346603358736460865314341)
                    ·
                      rfl

theorem cell23_7867502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_7867502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867502 prefixEnd_7867502 := by exact prefixLift 7867502
  have htrace : WordTrace (prefixWord ++ tailWord_7867502) baseStart_7867502 baseEnd_7867502 := by
    simpa [prefixWord, tailWord_7867502, baseEnd_7867502] using wordTrace_append hprefix tailTrace_7867502
  have hstable : (prefixWord ++ tailWord_7867502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867502).length < 2 ^ (prefixWord ++ tailWord_7867502).sum := by decide
  have hdescent : baseEnd_7867502 < baseStart_7867502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867559 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7867559 : Nat := 118140960795 + 7867559 * 2 ^ 59
def prefixEnd_7867559 : Nat := 4983230072969 + 3 ^ 40 * 7867559 * 2
def baseEnd_7867559 : Nat := 4039839344606688872930261

theorem tailTrace_7867559 : CollatzResearch.WordTrace tailWord_7867559 prefixEnd_7867559 4039839344606688872930261 := by
  unfold tailWord_7867559
  simp only [CollatzResearch.WordTrace]
  refine ⟨286953450904184889947109731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191302300602789926631406487 286953450904184889947109731)
  ·
    refine ⟨430430176356277334920664597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286953450904184889947109731 430430176356277334920664597)
    ·
      refine ⟨20176414516700500074406153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 430430176356277334920664597 20176414516700500074406153)
      ·
        refine ⟨15132310887525375055804615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20176414516700500074406153 15132310887525375055804615)
        ·
          refine ⟨22698466331288062583706923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15132310887525375055804615 22698466331288062583706923)
          ·
            refine ⟨34047699496932093875560385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22698466331288062583706923 34047699496932093875560385)
            ·
              refine ⟨25535774622699070406670289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34047699496932093875560385 25535774622699070406670289)
              ·
                refine ⟨19151830967024302805002717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25535774622699070406670289 19151830967024302805002717)
                ·
                  refine ⟨7181936612634113551876019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19151830967024302805002717 7181936612634113551876019)
                  ·
                    refine ⟨10772904918951170327814029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7181936612634113551876019 10772904918951170327814029)
                    ·
                      refine ⟨4039839344606688872930261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10772904918951170327814029 4039839344606688872930261)
                      ·
                        rfl

theorem cell23_7867559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7867559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867559 prefixEnd_7867559 := by exact prefixLift 7867559
  have htrace : WordTrace (prefixWord ++ tailWord_7867559) baseStart_7867559 baseEnd_7867559 := by
    simpa [prefixWord, tailWord_7867559, baseEnd_7867559] using wordTrace_append hprefix tailTrace_7867559
  have hstable : (prefixWord ++ tailWord_7867559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867559).length < 2 ^ (prefixWord ++ tailWord_7867559).sum := by decide
  have hdescent : baseEnd_7867559 < baseStart_7867559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867575 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 6, 4]
def baseStart_7867575 : Nat := 118140960795 + 7867575 * 2 ^ 59
def prefixEnd_7867575 : Nat := 4983230072969 + 3 ^ 40 * 7867575 * 2
def baseEnd_7867575 : Nat := 1346615853432386936776729

theorem tailTrace_7867575 : CollatzResearch.WordTrace tailWord_7867575 prefixEnd_7867575 1346615853432386936776729 := by
  unfold tailWord_7867575
  simp only [CollatzResearch.WordTrace]
  refine ⟨286954034472126924679692179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191302689648084616453128119 286954034472126924679692179)
  ·
    refine ⟨430431051708190387019538269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286954034472126924679692179 430431051708190387019538269)
    ·
      refine ⟨161411644390571395132326851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430431051708190387019538269 161411644390571395132326851)
      ·
        refine ⟨242117466585857092698490277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161411644390571395132326851 242117466585857092698490277)
        ·
          refine ⟨45397024984848204880966927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242117466585857092698490277 45397024984848204880966927)
          ·
            refine ⟨68095537477272307321450391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45397024984848204880966927 68095537477272307321450391)
            ·
              refine ⟨102143306215908460982175587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68095537477272307321450391 102143306215908460982175587)
              ·
                refine ⟨153214959323862691473263381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102143306215908460982175587 153214959323862691473263381)
                ·
                  refine ⟨7181951218306063662809221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153214959323862691473263381 7181951218306063662809221)
                  ·
                    refine ⟨1346615853432386936776729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7181951218306063662809221 1346615853432386936776729)
                    ·
                      rfl

theorem cell23_7867575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_7867575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867575 prefixEnd_7867575 := by exact prefixLift 7867575
  have htrace : WordTrace (prefixWord ++ tailWord_7867575) baseStart_7867575 baseEnd_7867575 := by
    simpa [prefixWord, tailWord_7867575, baseEnd_7867575] using wordTrace_append hprefix tailTrace_7867575
  have hstable : (prefixWord ++ tailWord_7867575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867575).length < 2 ^ (prefixWord ++ tailWord_7867575).sum := by decide
  have hdescent : baseEnd_7867575 < baseStart_7867575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867602 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_7867602 : Nat := 118140960795 + 7867602 * 2 ^ 59
def prefixEnd_7867602 : Nat := 4983230072969 + 3 ^ 40 * 7867602 * 2
def baseEnd_7867602 : Nat := 4039861424274832204692563

theorem tailTrace_7867602 : CollatzResearch.WordTrace tailWord_7867602 prefixEnd_7867602 4039861424274832204692563 := by
  unfold tailWord_7867602
  simp only [CollatzResearch.WordTrace]
  refine ⟨71738754810757277072731265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191303346162019405527283373 71738754810757277072731265)
  ·
    refine ⟨53804066108067957804548449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71738754810757277072731265 53804066108067957804548449)
    ·
      refine ⟨40353049581050968353411337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53804066108067957804548449 40353049581050968353411337)
      ·
        refine ⟨30264787185788226265058503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40353049581050968353411337 30264787185788226265058503)
        ·
          refine ⟨45397180778682339397587755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30264787185788226265058503 45397180778682339397587755)
          ·
            refine ⟨68095771168023509096381633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45397180778682339397587755 68095771168023509096381633)
            ·
              refine ⟨51071828376017631822286225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68095771168023509096381633 51071828376017631822286225)
              ·
                refine ⟨38303871282013223866714669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51071828376017631822286225 38303871282013223866714669)
                ·
                  refine ⟨14363951730754958950018001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38303871282013223866714669 14363951730754958950018001)
                  ·
                    refine ⟨10772963798066219212513501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14363951730754958950018001 10772963798066219212513501)
                    ·
                      refine ⟨4039861424274832204692563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10772963798066219212513501 4039861424274832204692563)
                      ·
                        rfl

theorem cell23_7867602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_7867602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867602 prefixEnd_7867602 := by exact prefixLift 7867602
  have htrace : WordTrace (prefixWord ++ tailWord_7867602) baseStart_7867602 baseEnd_7867602 := by
    simpa [prefixWord, tailWord_7867602, baseEnd_7867602] using wordTrace_append hprefix tailTrace_7867602
  have hstable : (prefixWord ++ tailWord_7867602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867602).length < 2 ^ (prefixWord ++ tailWord_7867602).sum := by decide
  have hdescent : baseEnd_7867602 < baseStart_7867602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867605 : List Nat := [1, 3, 2, 4, 1, 1, 1, 10]
def baseStart_7867605 : Nat := 118140960795 + 7867605 * 2 ^ 59
def prefixEnd_7867605 : Nat := 4983230072969 + 3 ^ 40 * 7867605 * 2
def baseEnd_7867605 : Nat := 149624554248770210850187

theorem tailTrace_7867605 : CollatzResearch.WordTrace tailWord_7867605 prefixEnd_7867605 149624554248770210850187 := by
  unfold tailWord_7867605
  simp only [CollatzResearch.WordTrace]
  refine ⟨286955128662018239803284269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191303419108012159868856179 286955128662018239803284269)
  ·
    refine ⟨107608173248256839926231601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286955128662018239803284269 107608173248256839926231601)
    ·
      refine ⟨80706129936192629944673701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107608173248256839926231601 80706129936192629944673701)
      ·
        refine ⟨15132399363036118114626319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80706129936192629944673701 15132399363036118114626319)
        ·
          refine ⟨22698599044554177171939479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15132399363036118114626319 22698599044554177171939479)
          ·
            refine ⟨34047898566831265757909219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22698599044554177171939479 34047898566831265757909219)
            ·
              refine ⟨51071847850246898636863829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34047898566831265757909219 51071847850246898636863829)
              ·
                refine ⟨149624554248770210850187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51071847850246898636863829 149624554248770210850187)
                ·
                  rfl

theorem cell23_7867605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 10].length) (baseStart_7867605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867605 prefixEnd_7867605 := by exact prefixLift 7867605
  have htrace : WordTrace (prefixWord ++ tailWord_7867605) baseStart_7867605 baseEnd_7867605 := by
    simpa [prefixWord, tailWord_7867605, baseEnd_7867605] using wordTrace_append hprefix tailTrace_7867605
  have hstable : (prefixWord ++ tailWord_7867605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867605).length < 2 ^ (prefixWord ++ tailWord_7867605).sum := by decide
  have hdescent : baseEnd_7867605 < baseStart_7867605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867649 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_7867649 : Nat := 118140960795 + 7867649 * 2 ^ 59
def prefixEnd_7867649 : Nat := 4983230072969 + 3 ^ 40 * 7867649 * 2
def baseEnd_7867649 : Nat := 4039885557865593520804847

theorem tailTrace_7867649 : CollatzResearch.WordTrace tailWord_7867649 prefixEnd_7867649 4039885557865593520804847 := by
  unfold tailWord_7867649
  simp only [CollatzResearch.WordTrace]
  refine ⟨286956733473858835317886001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191304488982572556878590667 286956733473858835317886001)
  ·
    refine ⟨215217550105394126488414501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286956733473858835317886001 215217550105394126488414501)
    ·
      refine ⟨40353290644761398716577719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215217550105394126488414501 40353290644761398716577719)
      ·
        refine ⟨60529935967142098074866579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40353290644761398716577719 60529935967142098074866579)
        ·
          refine ⟨90794903950713147112299869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60529935967142098074866579 90794903950713147112299869)
          ·
            refine ⟨34048088981517430167112451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90794903950713147112299869 34048088981517430167112451)
            ·
              refine ⟨51072133472276145250668677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34048088981517430167112451 51072133472276145250668677)
              ·
                refine ⟨9576025026051777234500377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51072133472276145250668677 9576025026051777234500377)
                ·
                  refine ⟨7182018769538832925875283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9576025026051777234500377 7182018769538832925875283)
                  ·
                    refine ⟨10773028154308249388812925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7182018769538832925875283 10773028154308249388812925)
                    ·
                      refine ⟨4039885557865593520804847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10773028154308249388812925 4039885557865593520804847)
                      ·
                        rfl

theorem cell23_7867649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_7867649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867649 prefixEnd_7867649 := by exact prefixLift 7867649
  have htrace : WordTrace (prefixWord ++ tailWord_7867649) baseStart_7867649 baseEnd_7867649 := by
    simpa [prefixWord, tailWord_7867649, baseEnd_7867649] using wordTrace_append hprefix tailTrace_7867649
  have hstable : (prefixWord ++ tailWord_7867649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867649).length < 2 ^ (prefixWord ++ tailWord_7867649).sum := by decide
  have hdescent : baseEnd_7867649 < baseStart_7867649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867650 : List Nat := [3, 4, 1, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_7867650 : Nat := 118140960795 + 7867650 * 2 ^ 59
def prefixEnd_7867650 : Nat := 4983230072969 + 3 ^ 40 * 7867650 * 2
def baseEnd_7867650 : Nat := 4039886071346248016892343

theorem tailTrace_7867650 : CollatzResearch.WordTrace tailWord_7867650 prefixEnd_7867650 4039886071346248016892343 := by
  unfold tailWord_7867650
  simp only [CollatzResearch.WordTrace]
  refine ⟨71739192486713803122168101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191304513297903474992448269 71739192486713803122168101)
  ·
    refine ⟨13451098591258838085406519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71739192486713803122168101 13451098591258838085406519)
    ·
      refine ⟨20176647886888257128109779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451098591258838085406519 20176647886888257128109779)
      ·
        refine ⟨30264971830332385692164669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20176647886888257128109779 30264971830332385692164669)
        ·
          refine ⟨11349364436374644634561751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30264971830332385692164669 11349364436374644634561751)
          ·
            refine ⟨17024046654561966951842627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11349364436374644634561751 17024046654561966951842627)
            ·
              refine ⟨25536069981842950427763941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17024046654561966951842627 25536069981842950427763941)
              ·
                refine ⟨4788013121595553205205739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25536069981842950427763941 4788013121595553205205739)
                ·
                  refine ⟨7182019682393329807808609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788013121595553205205739 7182019682393329807808609)
                  ·
                    refine ⟨5386514761794997355856457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7182019682393329807808609 5386514761794997355856457)
                    ·
                      refine ⟨4039886071346248016892343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386514761794997355856457 4039886071346248016892343)
                      ·
                        rfl

theorem cell23_7867650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_7867650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867650 prefixEnd_7867650 := by exact prefixLift 7867650
  have htrace : WordTrace (prefixWord ++ tailWord_7867650) baseStart_7867650 baseEnd_7867650 := by
    simpa [prefixWord, tailWord_7867650, baseEnd_7867650] using wordTrace_append hprefix tailTrace_7867650
  have hstable : (prefixWord ++ tailWord_7867650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867650).length < 2 ^ (prefixWord ++ tailWord_7867650).sum := by decide
  have hdescent : baseEnd_7867650 < baseStart_7867650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867665 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 2, 6]
def baseStart_7867665 : Nat := 118140960795 + 7867665 * 2 ^ 59
def prefixEnd_7867665 : Nat := 4983230072969 + 3 ^ 40 * 7867665 * 2
def baseEnd_7867665 : Nat := 1346631257852021819401591

theorem tailTrace_7867665 : CollatzResearch.WordTrace tailWord_7867665 prefixEnd_7867665 1346631257852021819401591 := by
  unfold tailWord_7867665
  simp only [CollatzResearch.WordTrace]
  refine ⟨286957317041800870050468449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191304878027867246700312299 286957317041800870050468449)
  ·
    refine ⟨215217987781350652537851337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286957317041800870050468449 215217987781350652537851337)
    ·
      refine ⟨161413490836012989403388503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215217987781350652537851337 161413490836012989403388503)
      ·
        refine ⟨242120236254019484105082755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161413490836012989403388503 242120236254019484105082755)
        ·
          refine ⟨363180354381029226157624133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242120236254019484105082755 363180354381029226157624133)
          ·
            refine ⟨68096316446442979904554525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363180354381029226157624133 68096316446442979904554525)
            ·
              refine ⟨25536118667416117464207947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68096316446442979904554525 25536118667416117464207947)
              ·
                refine ⟨38304178001124176196311921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25536118667416117464207947 38304178001124176196311921)
                ·
                  refine ⟨28728133500843132147233941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38304178001124176196311921 28728133500843132147233941)
                  ·
                    refine ⟨1346631257852021819401591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28728133500843132147233941 1346631257852021819401591)
                    ·
                      rfl

theorem cell23_7867665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_7867665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867665 prefixEnd_7867665 := by exact prefixLift 7867665
  have htrace : WordTrace (prefixWord ++ tailWord_7867665) baseStart_7867665 baseEnd_7867665 := by
    simpa [prefixWord, tailWord_7867665, baseEnd_7867665] using wordTrace_append hprefix tailTrace_7867665
  have hstable : (prefixWord ++ tailWord_7867665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867665).length < 2 ^ (prefixWord ++ tailWord_7867665).sum := by decide
  have hdescent : baseEnd_7867665 < baseStart_7867665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867675 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 3]
def baseStart_7867675 : Nat := 118140960795 + 7867675 * 2 ^ 59
def prefixEnd_7867675 : Nat := 4983230072969 + 3 ^ 40 * 7867675 * 2
def baseEnd_7867675 : Nat := 4039898908362610419079727

theorem tailTrace_7867675 : CollatzResearch.WordTrace tailWord_7867675 prefixEnd_7867675 4039898908362610419079727 := by
  unfold tailWord_7867675
  simp only [CollatzResearch.WordTrace]
  refine ⟨286957681771764641758332479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191305121181176427838888319 286957681771764641758332479)
  ·
    refine ⟨430436522657646962637498719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286957681771764641758332479 430436522657646962637498719)
    ·
      refine ⟨645654783986470443956248079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430436522657646962637498719 645654783986470443956248079)
      ·
        refine ⟨968482175979705665934372119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645654783986470443956248079 968482175979705665934372119)
        ·
          refine ⟨1452723263969558498901558179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968482175979705665934372119 1452723263969558498901558179)
          ·
            refine ⟨2179084895954337748352337269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452723263969558498901558179 2179084895954337748352337269)
            ·
              refine ⟨204289208995719163908031619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2179084895954337748352337269 204289208995719163908031619)
              ·
                refine ⟨306433813493578745862047429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204289208995719163908031619 306433813493578745862047429)
                ·
                  refine ⟨57456340030046014849133893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306433813493578745862047429 57456340030046014849133893)
                  ·
                    refine ⟨10773063755633627784212605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57456340030046014849133893 10773063755633627784212605)
                    ·
                      refine ⟨4039898908362610419079727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10773063755633627784212605 4039898908362610419079727)
                      ·
                        rfl

theorem cell23_7867675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 3].length) (baseStart_7867675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867675 prefixEnd_7867675 := by exact prefixLift 7867675
  have htrace : WordTrace (prefixWord ++ tailWord_7867675) baseStart_7867675 baseEnd_7867675 := by
    simpa [prefixWord, tailWord_7867675, baseEnd_7867675] using wordTrace_append hprefix tailTrace_7867675
  have hstable : (prefixWord ++ tailWord_7867675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867675).length < 2 ^ (prefixWord ++ tailWord_7867675).sum := by decide
  have hdescent : baseEnd_7867675 < baseStart_7867675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867693 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7867693 : Nat := 118140960795 + 7867693 * 2 ^ 59
def prefixEnd_7867693 : Nat := 4983230072969 + 3 ^ 40 * 7867693 * 2
def baseEnd_7867693 : Nat := 4039908151014391348654645

theorem tailTrace_7867693 : CollatzResearch.WordTrace tailWord_7867693 prefixEnd_7867693 4039908151014391348654645 := by
  unfold tailWord_7867693
  simp only [CollatzResearch.WordTrace]
  refine ⟨286958338285699430832487733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191305558857132953888325155 286958338285699430832487733)
  ·
    refine ⟨26902344214284321640545725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286958338285699430832487733 26902344214284321640545725)
    ·
      refine ⟨10088379080356620615204647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26902344214284321640545725 10088379080356620615204647)
      ·
        refine ⟨15132568620534930922806971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10088379080356620615204647 15132568620534930922806971)
        ·
          refine ⟨22698852930802396384210457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15132568620534930922806971 22698852930802396384210457)
          ·
            refine ⟨17024139698101797288157843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22698852930802396384210457 17024139698101797288157843)
            ·
              refine ⟨25536209547152695932236765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17024139698101797288157843 25536209547152695932236765)
              ·
                refine ⟨9576078580182260974588787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25536209547152695932236765 9576078580182260974588787)
                ·
                  refine ⟨14364117870273391461883181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9576078580182260974588787 14364117870273391461883181)
                  ·
                    refine ⟨5386544201352521798206193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14364117870273391461883181 5386544201352521798206193)
                    ·
                      refine ⟨4039908151014391348654645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386544201352521798206193 4039908151014391348654645)
                      ·
                        rfl

theorem cell23_7867693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7867693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867693 prefixEnd_7867693 := by exact prefixLift 7867693
  have htrace : WordTrace (prefixWord ++ tailWord_7867693) baseStart_7867693 baseEnd_7867693 := by
    simpa [prefixWord, tailWord_7867693, baseEnd_7867693] using wordTrace_append hprefix tailTrace_7867693
  have hstable : (prefixWord ++ tailWord_7867693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867693).length < 2 ^ (prefixWord ++ tailWord_7867693).sum := by decide
  have hdescent : baseEnd_7867693 < baseStart_7867693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867712 : List Nat := [2, 1, 1, 2, 2, 1, 3, 6, 5]
def baseStart_7867712 : Nat := 118140960795 + 7867712 * 2 ^ 59
def prefixEnd_7867712 : Nat := 4983230072969 + 3 ^ 40 * 7867712 * 2
def baseEnd_7867712 : Nat := 448879767460758530479673

theorem tailTrace_7867712 : CollatzResearch.WordTrace tailWord_7867712 prefixEnd_7867712 448879767460758530479673 := by
  unfold tailWord_7867712
  simp only [CollatzResearch.WordTrace]
  refine ⟨143479515636315298538714695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191306020848420398051619593 143479515636315298538714695)
  ·
    refine ⟨215219273454472947808072043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143479515636315298538714695 215219273454472947808072043)
    ·
      refine ⟨322828910181709421712108065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215219273454472947808072043 322828910181709421712108065)
      ·
        refine ⟨242121682636282066284081049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322828910181709421712108065 242121682636282066284081049)
        ·
          refine ⟨181591261977211549713060787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242121682636282066284081049 181591261977211549713060787)
          ·
            refine ⟨272386892965817324569591181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181591261977211549713060787 272386892965817324569591181)
            ·
              refine ⟨102145084862181496713596693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272386892965817324569591181 102145084862181496713596693)
              ·
                refine ⟨4788050852914757658449845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102145084862181496713596693 4788050852914757658449845)
                ·
                  refine ⟨448879767460758530479673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788050852914757658449845 448879767460758530479673)
                  ·
                    rfl

theorem cell23_7867712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 5].length) (baseStart_7867712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867712 prefixEnd_7867712 := by exact prefixLift 7867712
  have htrace : WordTrace (prefixWord ++ tailWord_7867712) baseStart_7867712 baseEnd_7867712 := by
    simpa [prefixWord, tailWord_7867712, baseEnd_7867712] using wordTrace_append hprefix tailTrace_7867712
  have hstable : (prefixWord ++ tailWord_7867712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867712).length < 2 ^ (prefixWord ++ tailWord_7867712).sum := by decide
  have hdescent : baseEnd_7867712 < baseStart_7867712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867774 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7867774 : Nat := 118140960795 + 7867774 * 2 ^ 59
def prefixEnd_7867774 : Nat := 4983230072969 + 3 ^ 40 * 7867774 * 2
def baseEnd_7867774 : Nat := 4039949742947405531741773

theorem tailTrace_7867774 : CollatzResearch.WordTrace tailWord_7867774 prefixEnd_7867774 4039949742947405531741773 := by
  unfold tailWord_7867774
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870161574800747708273297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191307528398937321110790917 35870161574800747708273297)
  ·
    refine ⟨26902621181100560781204973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35870161574800747708273297 26902621181100560781204973)
    ·
      refine ⟨10088482942912710292951865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26902621181100560781204973 10088482942912710292951865)
      ·
        refine ⟨7566362207184532719713899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10088482942912710292951865 7566362207184532719713899)
        ·
          refine ⟨11349543310776799079570849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7566362207184532719713899 11349543310776799079570849)
          ·
            refine ⟨8512157483082599309678137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11349543310776799079570849 8512157483082599309678137)
            ·
              refine ⟨6384118112311949482258603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8512157483082599309678137 6384118112311949482258603)
              ·
                refine ⟨9576177168467924223387905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384118112311949482258603 9576177168467924223387905)
                ·
                  refine ⟨7182132876350943167540929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9576177168467924223387905 7182132876350943167540929)
                  ·
                    refine ⟨5386599657263207375655697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7182132876350943167540929 5386599657263207375655697)
                    ·
                      refine ⟨4039949742947405531741773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386599657263207375655697 4039949742947405531741773)
                      ·
                        rfl

theorem cell23_7867774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7867774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867774 prefixEnd_7867774 := by exact prefixLift 7867774
  have htrace : WordTrace (prefixWord ++ tailWord_7867774) baseStart_7867774 baseEnd_7867774 := by
    simpa [prefixWord, tailWord_7867774, baseEnd_7867774] using wordTrace_append hprefix tailTrace_7867774
  have hstable : (prefixWord ++ tailWord_7867774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867774).length < 2 ^ (prefixWord ++ tailWord_7867774).sum := by decide
  have hdescent : baseEnd_7867774 < baseStart_7867774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867796 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_7867796 : Nat := 118140960795 + 7867796 * 2 ^ 59
def prefixEnd_7867796 : Nat := 4983230072969 + 3 ^ 40 * 7867796 * 2
def baseEnd_7867796 : Nat := 4039961039521804445666671

theorem tailTrace_7867796 : CollatzResearch.WordTrace tailWord_7867796 prefixEnd_7867796 4039961039521804445666671 := by
  unfold tailWord_7867796
  simp only [CollatzResearch.WordTrace]
  refine ⟨143481047502163139711743621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191308063336217519615658161 143481047502163139711743621)
  ·
    refine ⟨26902696406655588695951929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143481047502163139711743621 26902696406655588695951929)
    ·
      refine ⟨20177022304991691521963947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26902696406655588695951929 20177022304991691521963947)
      ·
        refine ⟨30265533457487537282945921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20177022304991691521963947 30265533457487537282945921)
        ·
          refine ⟨22699150093115652962209441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30265533457487537282945921 22699150093115652962209441)
          ·
            refine ⟨17024362569836739721657081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22699150093115652962209441 17024362569836739721657081)
            ·
              refine ⟨12768271927377554791242811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17024362569836739721657081 12768271927377554791242811)
              ·
                refine ⟨19152407891066332186864217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12768271927377554791242811 19152407891066332186864217)
                ·
                  refine ⟨14364305918299749140148163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19152407891066332186864217 14364305918299749140148163)
                  ·
                    refine ⟨21546458877449623710222245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14364305918299749140148163 21546458877449623710222245)
                    ·
                      refine ⟨4039961039521804445666671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21546458877449623710222245 4039961039521804445666671)
                      ·
                        rfl

theorem cell23_7867796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_7867796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867796 prefixEnd_7867796 := by exact prefixLift 7867796
  have htrace : WordTrace (prefixWord ++ tailWord_7867796) baseStart_7867796 baseEnd_7867796 := by
    simpa [prefixWord, tailWord_7867796, baseEnd_7867796] using wordTrace_append hprefix tailTrace_7867796
  have hstable : (prefixWord ++ tailWord_7867796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867796).length < 2 ^ (prefixWord ++ tailWord_7867796).sum := by decide
  have hdescent : baseEnd_7867796 < baseStart_7867796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867832 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 3, 5]
def baseStart_7867832 : Nat := 118140960795 + 7867832 * 2 ^ 59
def prefixEnd_7867832 : Nat := 4983230072969 + 3 ^ 40 * 7867832 * 2
def baseEnd_7867832 : Nat := 1346659841608455434938835

theorem tailTrace_7867832 : CollatzResearch.WordTrace tailWord_7867832 prefixEnd_7867832 1346659841608455434938835 := by
  unfold tailWord_7867832
  simp only [CollatzResearch.WordTrace]
  refine ⟨143481704016097928785898875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191308938688130571714531833 143481704016097928785898875)
  ·
    refine ⟨215222556024146893178848313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143481704016097928785898875 215222556024146893178848313)
    ·
      refine ⟨161416917018110169884136235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215222556024146893178848313 161416917018110169884136235)
      ·
        refine ⟨242125375527165254826204353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161416917018110169884136235 242125375527165254826204353)
        ·
          refine ⟨181594031645373941119653265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242125375527165254826204353 181594031645373941119653265)
          ·
            refine ⟨136195523734030455839739949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181594031645373941119653265 136195523734030455839739949)
            ·
              refine ⟨51073321400261420939902481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136195523734030455839739949 51073321400261420939902481)
              ·
                refine ⟨38304991050196065704926861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51073321400261420939902481 38304991050196065704926861)
                ·
                  refine ⟨14364371643823524639347573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38304991050196065704926861 14364371643823524639347573)
                  ·
                    refine ⟨1346659841608455434938835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14364371643823524639347573 1346659841608455434938835)
                    ·
                      rfl

theorem cell23_7867832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_7867832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867832 prefixEnd_7867832 := by exact prefixLift 7867832
  have htrace : WordTrace (prefixWord ++ tailWord_7867832) baseStart_7867832 baseEnd_7867832 := by
    simpa [prefixWord, tailWord_7867832, baseEnd_7867832] using wordTrace_append hprefix tailTrace_7867832
  have hstable : (prefixWord ++ tailWord_7867832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867832).length < 2 ^ (prefixWord ++ tailWord_7867832).sum := by decide
  have hdescent : baseEnd_7867832 < baseStart_7867832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867839 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 4, 3, 2]
def baseStart_7867839 : Nat := 118140960795 + 7867839 * 2 ^ 59
def prefixEnd_7867839 : Nat := 4983230072969 + 3 ^ 40 * 7867839 * 2
def baseEnd_7867839 : Nat := 4039983119189947777428973

theorem tailTrace_7867839 : CollatzResearch.WordTrace tailWord_7867839 prefixEnd_7867839 4039983119189947777428973 := by
  unfold tailWord_7867839
  simp only [CollatzResearch.WordTrace]
  refine ⟨286963663343170497767302571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191309108895446998511535047 286963663343170497767302571)
  ·
    refine ⟨430445495014755746650953857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286963663343170497767302571 430445495014755746650953857)
    ·
      refine ⟨322834121261066809988215393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430445495014755746650953857 322834121261066809988215393)
      ·
        refine ⟨242125590945800107491161545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322834121261066809988215393 242125590945800107491161545)
        ·
          refine ⟨181594193209350080618371159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242125590945800107491161545 181594193209350080618371159)
          ·
            refine ⟨272391289814025120927556739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181594193209350080618371159 272391289814025120927556739)
            ·
              refine ⟨408586934721037681391335109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272391289814025120927556739 408586934721037681391335109)
              ·
                refine ⟨76610050260194565260875333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408586934721037681391335109 76610050260194565260875333)
                ·
                  refine ⟨14364384423786480986414125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76610050260194565260875333 14364384423786480986414125)
                  ·
                    refine ⟨5386644158919930369905297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14364384423786480986414125 5386644158919930369905297)
                    ·
                      refine ⟨4039983119189947777428973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386644158919930369905297 4039983119189947777428973)
                      ·
                        rfl

theorem cell23_7867839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_7867839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867839 prefixEnd_7867839 := by exact prefixLift 7867839
  have htrace : WordTrace (prefixWord ++ tailWord_7867839) baseStart_7867839 baseEnd_7867839 := by
    simpa [prefixWord, tailWord_7867839, baseEnd_7867839] using wordTrace_append hprefix tailTrace_7867839
  have hstable : (prefixWord ++ tailWord_7867839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867839).length < 2 ^ (prefixWord ++ tailWord_7867839).sum := by decide
  have hdescent : baseEnd_7867839 < baseStart_7867839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867866 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_7867866 : Nat := 118140960795 + 7867866 * 2 ^ 59
def prefixEnd_7867866 : Nat := 4983230072969 + 3 ^ 40 * 7867866 * 2
def baseEnd_7867866 : Nat := 1346665661055873057263783

theorem tailTrace_7867866 : CollatzResearch.WordTrace tailWord_7867866 prefixEnd_7867866 1346665661055873057263783 := by
  unfold tailWord_7867866
  simp only [CollatzResearch.WordTrace]
  refine ⟨71741162028518170344633863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191309765409381787585690301 71741162028518170344633863)
  ·
    refine ⟨107611743042777255516950795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71741162028518170344633863 107611743042777255516950795)
    ·
      refine ⟨161417614564165883275426193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107611743042777255516950795 161417614564165883275426193)
      ·
        refine ⟨121063210923124412456569645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161417614564165883275426193 121063210923124412456569645)
        ·
          refine ⟨45398704096171654671213617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121063210923124412456569645 45398704096171654671213617)
          ·
            refine ⟨34049028072128741003410213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45398704096171654671213617 34049028072128741003410213)
            ·
              refine ⟨6384192763524138938139415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34049028072128741003410213 6384192763524138938139415)
              ·
                refine ⟨9576289145286208407209123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384192763524138938139415 9576289145286208407209123)
                ·
                  refine ⟨14364433717929312610813685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9576289145286208407209123 14364433717929312610813685)
                  ·
                    refine ⟨1346665661055873057263783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14364433717929312610813685 1346665661055873057263783)
                    ·
                      rfl

theorem cell23_7867866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_7867866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867866 prefixEnd_7867866 := by exact prefixLift 7867866
  have htrace : WordTrace (prefixWord ++ tailWord_7867866) baseStart_7867866 baseEnd_7867866 := by
    simpa [prefixWord, tailWord_7867866, baseEnd_7867866] using wordTrace_append hprefix tailTrace_7867866
  have hstable : (prefixWord ++ tailWord_7867866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867866).length < 2 ^ (prefixWord ++ tailWord_7867866).sum := by decide
  have hdescent : baseEnd_7867866 < baseStart_7867866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867889 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_7867889 : Nat := 118140960795 + 7867889 * 2 ^ 59
def prefixEnd_7867889 : Nat := 4983230072969 + 3 ^ 40 * 7867889 * 2
def baseEnd_7867889 : Nat := 4040008793222672581803743

theorem tailTrace_7867889 : CollatzResearch.WordTrace tailWord_7867889 prefixEnd_7867889 4040008793222672581803743 := by
  unfold tailWord_7867889
  simp only [CollatzResearch.WordTrace]
  refine ⟨286965486992989356306622721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191310324661992904204415147 286965486992989356306622721)
  ·
    refine ⟨215224115244742017229967041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286965486992989356306622721 215224115244742017229967041)
    ·
      refine ⟨161418086433556512922475281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215224115244742017229967041 161418086433556512922475281)
      ·
        refine ⟨121063564825167384691856461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161418086433556512922475281 121063564825167384691856461)
        ·
          refine ⟨45398836809437769259446173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121063564825167384691856461 45398836809437769259446173)
          ·
            refine ⟨17024563803539163472292315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45398836809437769259446173 17024563803539163472292315)
            ·
              refine ⟨25536845705308745208438473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17024563803539163472292315 25536845705308745208438473)
              ·
                refine ⟨19152634278981558906328855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25536845705308745208438473 19152634278981558906328855)
                ·
                  refine ⟨28728951418472338359493283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19152634278981558906328855 28728951418472338359493283)
                  ·
                    refine ⟨43093427127708507539239925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28728951418472338359493283 43093427127708507539239925)
                    ·
                      refine ⟨4040008793222672581803743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43093427127708507539239925 4040008793222672581803743)
                      ·
                        rfl

theorem cell23_7867889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_7867889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867889 prefixEnd_7867889 := by exact prefixLift 7867889
  have htrace : WordTrace (prefixWord ++ tailWord_7867889) baseStart_7867889 baseEnd_7867889 := by
    simpa [prefixWord, tailWord_7867889, baseEnd_7867889] using wordTrace_append hprefix tailTrace_7867889
  have hstable : (prefixWord ++ tailWord_7867889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867889).length < 2 ^ (prefixWord ++ tailWord_7867889).sum := by decide
  have hdescent : baseEnd_7867889 < baseStart_7867889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867937 : List Nat := [1, 2, 3, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_7867937 : Nat := 118140960795 + 7867937 * 2 ^ 59
def prefixEnd_7867937 : Nat := 4983230072969 + 3 ^ 40 * 7867937 * 2
def baseEnd_7867937 : Nat := 4040033440294088394003523

theorem tailTrace_7867937 : CollatzResearch.WordTrace tailWord_7867937 prefixEnd_7867937 4040033440294088394003523 := by
  unfold tailWord_7867937
  simp only [CollatzResearch.WordTrace]
  refine ⟨286967237696815460504370065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191311491797876973669580043 286967237696815460504370065)
  ·
    refine ⟨215225428272611595378277549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286967237696815460504370065 215225428272611595378277549)
    ·
      refine ⟨80709535602229348266854081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215225428272611595378277549 80709535602229348266854081)
      ·
        refine ⟨60532151701672011200140561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80709535602229348266854081 60532151701672011200140561)
        ·
          refine ⟨45399113776254008400105421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60532151701672011200140561 45399113776254008400105421)
          ·
            refine ⟨17024667666095253150039533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45399113776254008400105421 17024667666095253150039533)
            ·
              refine ⟨6384250374785719931264825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17024667666095253150039533 6384250374785719931264825)
              ·
                refine ⟨4788187781089289948448619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384250374785719931264825 4788187781089289948448619)
                ·
                  refine ⟨7182281671633934922672929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788187781089289948448619 7182281671633934922672929)
                  ·
                    refine ⟨5386711253725451192004697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7182281671633934922672929 5386711253725451192004697)
                    ·
                      refine ⟨4040033440294088394003523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386711253725451192004697 4040033440294088394003523)
                      ·
                        rfl

theorem cell23_7867937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_7867937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867937 prefixEnd_7867937 := by exact prefixLift 7867937
  have htrace : WordTrace (prefixWord ++ tailWord_7867937) baseStart_7867937 baseEnd_7867937 := by
    simpa [prefixWord, tailWord_7867937, baseEnd_7867937] using wordTrace_append hprefix tailTrace_7867937
  have hstable : (prefixWord ++ tailWord_7867937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867937).length < 2 ^ (prefixWord ++ tailWord_7867937).sum := by decide
  have hdescent : baseEnd_7867937 < baseStart_7867937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867952 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 1, 8]
def baseStart_7867952 : Nat := 118140960795 + 7867952 * 2 ^ 59
def prefixEnd_7867952 : Nat := 4983230072969 + 3 ^ 40 * 7867952 * 2
def baseEnd_7867952 : Nat := 1346680380834635278438651

theorem tailTrace_7867952 : CollatzResearch.WordTrace tailWord_7867952 prefixEnd_7867952 1346680380834635278438651 := by
  unfold tailWord_7867952
  simp only [CollatzResearch.WordTrace]
  refine ⟨143483892395880559033083055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191311856527840745377444073 143483892395880559033083055)
  ·
    refine ⟨215225838593820838549624583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143483892395880559033083055 215225838593820838549624583)
    ·
      refine ⟨322838757890731257824436875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215225838593820838549624583 322838757890731257824436875)
      ·
        refine ⟨484258136836096886736655313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322838757890731257824436875 484258136836096886736655313)
        ·
          refine ⟨363193602627072665052491485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484258136836096886736655313 363193602627072665052491485)
          ·
            refine ⟨136197600985152249394684307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363193602627072665052491485 136197600985152249394684307)
            ·
              refine ⟨204296401477728374092026461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136197600985152249394684307 204296401477728374092026461)
              ·
                refine ⟨76611150554148140284509923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204296401477728374092026461 76611150554148140284509923)
                ·
                  refine ⟨114916725831222210426764885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76611150554148140284509923 114916725831222210426764885)
                  ·
                    refine ⟨1346680380834635278438651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114916725831222210426764885 1346680380834635278438651)
                    ·
                      rfl

theorem cell23_7867952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_7867952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867952 prefixEnd_7867952 := by exact prefixLift 7867952
  have htrace : WordTrace (prefixWord ++ tailWord_7867952) baseStart_7867952 baseEnd_7867952 := by
    simpa [prefixWord, tailWord_7867952, baseEnd_7867952] using wordTrace_append hprefix tailTrace_7867952
  have hstable : (prefixWord ++ tailWord_7867952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867952).length < 2 ^ (prefixWord ++ tailWord_7867952).sum := by decide
  have hdescent : baseEnd_7867952 < baseStart_7867952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867980 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 1, 3, 2]
def baseStart_7867980 : Nat := 118140960795 + 7867980 * 2 ^ 59
def prefixEnd_7867980 : Nat := 4983230072969 + 3 ^ 40 * 7867980 * 2
def baseEnd_7867980 : Nat := 4040055519962231725765825

theorem tailTrace_7867980 : CollatzResearch.WordTrace tailWord_7867980 prefixEnd_7867980 4040055519962231725765825 := by
  unfold tailWord_7867980
  simp only [CollatzResearch.WordTrace]
  refine ⟨143484403017829839424092697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191312537357106452565456929 143484403017829839424092697)
  ·
    refine ⟨107613302263372379568069523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143484403017829839424092697 107613302263372379568069523)
    ·
      refine ⟨161419953395058569352104285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107613302263372379568069523 161419953395058569352104285)
      ·
        refine ⟨60532482523146963507039107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161419953395058569352104285 60532482523146963507039107)
        ·
          refine ⟨90798723784720445260558661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60532482523146963507039107 90798723784720445260558661)
          ·
            refine ⟨17024760709635083486354749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90798723784720445260558661 17024760709635083486354749)
            ·
              refine ⟨6384285266113156307383031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17024760709635083486354749 6384285266113156307383031)
              ·
                refine ⟨9576427899169734461074547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384285266113156307383031 9576427899169734461074547)
                ·
                  refine ⟨14364641848754601691611821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9576427899169734461074547 14364641848754601691611821)
                  ·
                    refine ⟨5386740693282975634354433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14364641848754601691611821 5386740693282975634354433)
                    ·
                      refine ⟨4040055519962231725765825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386740693282975634354433 4040055519962231725765825)
                      ·
                        rfl

theorem cell23_7867980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_7867980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867980 prefixEnd_7867980 := by exact prefixLift 7867980
  have htrace : WordTrace (prefixWord ++ tailWord_7867980) baseStart_7867980 baseEnd_7867980 := by
    simpa [prefixWord, tailWord_7867980, baseEnd_7867980] using wordTrace_append hprefix tailTrace_7867980
  have hstable : (prefixWord ++ tailWord_7867980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867980).length < 2 ^ (prefixWord ++ tailWord_7867980).sum := by decide
  have hdescent : baseEnd_7867980 < baseStart_7867980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867989 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7867989 : Nat := 118140960795 + 7867989 * 2 ^ 59
def prefixEnd_7867989 : Nat := 4983230072969 + 3 ^ 40 * 7867989 * 2
def baseEnd_7867989 : Nat := 4040060141288122190553283

theorem tailTrace_7867989 : CollatzResearch.WordTrace tailWord_7867989 prefixEnd_7867989 4040060141288122190553283 := by
  unfold tailWord_7867989
  simp only [CollatzResearch.WordTrace]
  refine ⟨286969134292627073385263021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191312756195084715590175347 286969134292627073385263021)
  ·
    refine ⟨107613425359735152519473633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286969134292627073385263021 107613425359735152519473633)
    ·
      refine ⟨80710069019801364389605225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107613425359735152519473633 80710069019801364389605225)
      ·
        refine ⟨60532551764851023292203919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80710069019801364389605225 60532551764851023292203919)
        ·
          refine ⟨90798827647276534938305879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60532551764851023292203919 90798827647276534938305879)
          ·
            refine ⟨136198241470914802407458819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90798827647276534938305879 136198241470914802407458819)
            ·
              refine ⟨204297362206372203611188229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136198241470914802407458819 204297362206372203611188229)
              ·
                refine ⟨38305755413694788177097793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204297362206372203611188229 38305755413694788177097793)
                ·
                  refine ⟨28729316560271091132823345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38305755413694788177097793 28729316560271091132823345)
                  ·
                    refine ⟨21546987420203318349617509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28729316560271091132823345 21546987420203318349617509)
                    ·
                      refine ⟨4040060141288122190553283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21546987420203318349617509 4040060141288122190553283)
                      ·
                        rfl

theorem cell23_7867989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7867989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867989 prefixEnd_7867989 := by exact prefixLift 7867989
  have htrace : WordTrace (prefixWord ++ tailWord_7867989) baseStart_7867989 baseEnd_7867989 := by
    simpa [prefixWord, tailWord_7867989, baseEnd_7867989] using wordTrace_append hprefix tailTrace_7867989
  have hstable : (prefixWord ++ tailWord_7867989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867989).length < 2 ^ (prefixWord ++ tailWord_7867989).sum := by decide
  have hdescent : baseEnd_7867989 < baseStart_7867989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7867996 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_7867996 : Nat := 118140960795 + 7867996 * 2 ^ 59
def prefixEnd_7867996 : Nat := 4983230072969 + 3 ^ 40 * 7867996 * 2
def baseEnd_7867996 : Nat := 4040063735652703663165751

theorem tailTrace_7867996 : CollatzResearch.WordTrace tailWord_7867996 prefixEnd_7867996 4040063735652703663165751 := by
  unfold tailWord_7867996
  simp only [CollatzResearch.WordTrace]
  refine ⟨143484694801800856790383921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191312926402401142387178561 143484694801800856790383921)
  ·
    refine ⟨107613521101350642592787941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143484694801800856790383921 107613521101350642592787941)
    ·
      refine ⟨20177535206503245486147739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107613521101350642592787941 20177535206503245486147739)
      ·
        refine ⟨30266302809754868229221609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20177535206503245486147739 30266302809754868229221609)
        ·
          refine ⟨22699727107316151171916207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30266302809754868229221609 22699727107316151171916207)
          ·
            refine ⟨34049590660974226757874311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22699727107316151171916207 34049590660974226757874311)
            ·
              refine ⟨51074385991461340136811467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34049590660974226757874311 51074385991461340136811467)
              ·
                refine ⟨76611578987192010205217201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51074385991461340136811467 76611578987192010205217201)
                ·
                  refine ⟨57458684240394007653912901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76611578987192010205217201 57458684240394007653912901)
                  ·
                    refine ⟨10773503295073876435108669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57458684240394007653912901 10773503295073876435108669)
                    ·
                      refine ⟨4040063735652703663165751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10773503295073876435108669 4040063735652703663165751)
                      ·
                        rfl

theorem cell23_7867996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_7867996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7867996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7867996 prefixEnd_7867996 := by exact prefixLift 7867996
  have htrace : WordTrace (prefixWord ++ tailWord_7867996) baseStart_7867996 baseEnd_7867996 := by
    simpa [prefixWord, tailWord_7867996, baseEnd_7867996] using wordTrace_append hprefix tailTrace_7867996
  have hstable : (prefixWord ++ tailWord_7867996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7867996).length < 2 ^ (prefixWord ++ tailWord_7867996).sum := by decide
  have hdescent : baseEnd_7867996 < baseStart_7867996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7867996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868009 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 3]
def baseStart_7868009 : Nat := 118140960795 + 7868009 * 2 ^ 59
def prefixEnd_7868009 : Nat := 4983230072969 + 3 ^ 40 * 7868009 * 2
def baseEnd_7868009 : Nat := 4040070410901212112303191

theorem tailTrace_7868009 : CollatzResearch.WordTrace tailWord_7868009 prefixEnd_7868009 4040070410901212112303191 := by
  unfold tailWord_7868009
  simp only [CollatzResearch.WordTrace]
  refine ⟨286969863752554616800991081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191313242501703077867327387 286969863752554616800991081)
  ·
    refine ⟨215227397814415962600743311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286969863752554616800991081 215227397814415962600743311)
    ·
      refine ⟨322841096721623943901114967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215227397814415962600743311 322841096721623943901114967)
      ·
        refine ⟨484261645082435915851672451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322841096721623943901114967 484261645082435915851672451)
        ·
          refine ⟨726392467623653873777508677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484261645082435915851672451 726392467623653873777508677)
          ·
            refine ⟨136198587679435101333282877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 726392467623653873777508677 136198587679435101333282877)
            ·
              refine ⟨51074470379788162999981079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136198587679435101333282877 51074470379788162999981079)
              ·
                refine ⟨76611705569682244499971619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51074470379788162999981079 76611705569682244499971619)
                ·
                  refine ⟨114917558354523366749957429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76611705569682244499971619 114917558354523366749957429)
                  ·
                    refine ⟨10773521095736565632808509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114917558354523366749957429 10773521095736565632808509)
                    ·
                      refine ⟨4040070410901212112303191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10773521095736565632808509 4040070410901212112303191)
                      ·
                        rfl

theorem cell23_7868009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_7868009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868009 prefixEnd_7868009 := by exact prefixLift 7868009
  have htrace : WordTrace (prefixWord ++ tailWord_7868009) baseStart_7868009 baseEnd_7868009 := by
    simpa [prefixWord, tailWord_7868009, baseEnd_7868009] using wordTrace_append hprefix tailTrace_7868009
  have hstable : (prefixWord ++ tailWord_7868009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868009).length < 2 ^ (prefixWord ++ tailWord_7868009).sum := by decide
  have hdescent : baseEnd_7868009 < baseStart_7868009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868010 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_7868010 : Nat := 118140960795 + 7868010 * 2 ^ 59
def prefixEnd_7868010 : Nat := 4983230072969 + 3 ^ 40 * 7868010 * 2
def baseEnd_7868010 : Nat := 4040070924381866608390687

theorem tailTrace_7868010 : CollatzResearch.WordTrace tailWord_7868010 prefixEnd_7868010 4040070924381866608390687 := by
  unfold tailWord_7868010
  simp only [CollatzResearch.WordTrace]
  refine ⟨71742475056387748492944371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191313266817033995981184989 71742475056387748492944371)
  ·
    refine ⟨107613712584581622739416557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71742475056387748492944371 107613712584581622739416557)
    ·
      refine ⟨40355142219218108527281209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107613712584581622739416557 40355142219218108527281209)
      ·
        refine ⟨30266356664413581395460907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40355142219218108527281209 30266356664413581395460907)
        ·
          refine ⟨45399534996620372093191361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266356664413581395460907 45399534996620372093191361)
          ·
            refine ⟨34049651247465279069893521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45399534996620372093191361 34049651247465279069893521)
            ·
              refine ⟨25537238435598959302420141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34049651247465279069893521 25537238435598959302420141)
              ·
                refine ⟨9576464413349609738407553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25537238435598959302420141 9576464413349609738407553)
                ·
                  refine ⟨7182348310012207303805665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9576464413349609738407553 7182348310012207303805665)
                  ·
                    refine ⟨5386761232509155477854249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7182348310012207303805665 5386761232509155477854249)
                    ·
                      refine ⟨4040070924381866608390687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386761232509155477854249 4040070924381866608390687)
                      ·
                        rfl

theorem cell23_7868010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_7868010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868010 prefixEnd_7868010 := by exact prefixLift 7868010
  have htrace : WordTrace (prefixWord ++ tailWord_7868010) baseStart_7868010 baseEnd_7868010 := by
    simpa [prefixWord, tailWord_7868010, baseEnd_7868010] using wordTrace_append hprefix tailTrace_7868010
  have hstable : (prefixWord ++ tailWord_7868010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868010).length < 2 ^ (prefixWord ++ tailWord_7868010).sum := by decide
  have hdescent : baseEnd_7868010 < baseStart_7868010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868033 : List Nat := [1, 2, 4, 2, 1, 3, 2, 3, 5]
def baseStart_7868033 : Nat := 118140960795 + 7868033 * 2 ^ 59
def prefixEnd_7868033 : Nat := 4983230072969 + 3 ^ 40 * 7868033 * 2
def baseEnd_7868033 : Nat := 448898081604102224267009

theorem tailTrace_7868033 : CollatzResearch.WordTrace tailWord_7868033 prefixEnd_7868033 448898081604102224267009 := by
  unfold tailWord_7868033
  simp only [CollatzResearch.WordTrace]
  refine ⟨286970739104467668899864753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191313826069645112599909835 286970739104467668899864753)
  ·
    refine ⟨215228054328350751674898565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286970739104467668899864753 215228054328350751674898565)
    ·
      refine ⟨40355260186565765939043481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215228054328350751674898565 40355260186565765939043481)
      ·
        refine ⟨30266445139924324454282611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40355260186565765939043481 30266445139924324454282611)
        ·
          refine ⟨45399667709886486681423917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266445139924324454282611 45399667709886486681423917)
          ·
            refine ⟨17024875391207432505533969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45399667709886486681423917 17024875391207432505533969)
            ·
              refine ⟨12768656543405574379150477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17024875391207432505533969 12768656543405574379150477)
              ·
                refine ⟨4788246203777090392181429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12768656543405574379150477 4788246203777090392181429)
                ·
                  refine ⟨448898081604102224267009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788246203777090392181429 448898081604102224267009)
                  ·
                    rfl

theorem cell23_7868033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 5].length) (baseStart_7868033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868033 prefixEnd_7868033 := by exact prefixLift 7868033
  have htrace : WordTrace (prefixWord ++ tailWord_7868033) baseStart_7868033 baseEnd_7868033 := by
    simpa [prefixWord, tailWord_7868033, baseEnd_7868033] using wordTrace_append hprefix tailTrace_7868033
  have hstable : (prefixWord ++ tailWord_7868033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868033).length < 2 ^ (prefixWord ++ tailWord_7868033).sum := by decide
  have hdescent : baseEnd_7868033 < baseStart_7868033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868079 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_7868079 : Nat := 118140960795 + 7868079 * 2 ^ 59
def prefixEnd_7868079 : Nat := 4983230072969 + 3 ^ 40 * 7868079 * 2
def baseEnd_7868079 : Nat := 4040106354547026838427869

theorem tailTrace_7868079 : CollatzResearch.WordTrace tailWord_7868079 prefixEnd_7868079 4040106354547026838427869 := by
  unfold tailWord_7868079
  simp only [CollatzResearch.WordTrace]
  refine ⟨286972416862301018756039291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191314944574867345837359527 286972416862301018756039291)
  ·
    refine ⟨430458625293451528134058937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286972416862301018756039291 430458625293451528134058937)
    ·
      refine ⟨322843968970088646100544203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430458625293451528134058937 322843968970088646100544203)
      ·
        refine ⟨484265953455132969150816305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322843968970088646100544203 484265953455132969150816305)
        ·
          refine ⟨363199465091349726863112229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484265953455132969150816305 363199465091349726863112229)
          ·
            refine ⟨68099899704628073786833543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363199465091349726863112229 68099899704628073786833543)
            ·
              refine ⟨102149849556942110680250315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68099899704628073786833543 102149849556942110680250315)
              ·
                refine ⟨153224774335413166020375473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102149849556942110680250315 153224774335413166020375473)
                ·
                  refine ⟨114918580751559874515281605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153224774335413166020375473 114918580751559874515281605)
                  ·
                    refine ⟨21547233890917476471615301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114918580751559874515281605 21547233890917476471615301)
                    ·
                      refine ⟨4040106354547026838427869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21547233890917476471615301 4040106354547026838427869)
                      ·
                        rfl

theorem cell23_7868079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_7868079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868079 prefixEnd_7868079 := by exact prefixLift 7868079
  have htrace : WordTrace (prefixWord ++ tailWord_7868079) baseStart_7868079 baseEnd_7868079 := by
    simpa [prefixWord, tailWord_7868079, baseEnd_7868079] using wordTrace_append hprefix tailTrace_7868079
  have hstable : (prefixWord ++ tailWord_7868079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868079).length < 2 ^ (prefixWord ++ tailWord_7868079).sum := by decide
  have hdescent : baseEnd_7868079 < baseStart_7868079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868089 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 8]
def baseStart_7868089 : Nat := 118140960795 + 7868089 * 2 ^ 59
def prefixEnd_7868089 : Nat := 4983230072969 + 3 ^ 40 * 7868089 * 2
def baseEnd_7868089 : Nat := 448901276594841311033647

theorem tailTrace_7868089 : CollatzResearch.WordTrace tailWord_7868089 prefixEnd_7868089 448901276594841311033647 := by
  unfold tailWord_7868089
  simp only [CollatzResearch.WordTrace]
  refine ⟨286972781592264790463903321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191315187728176526975935547 286972781592264790463903321)
  ·
    refine ⟨215229586194198592847927491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286972781592264790463903321 215229586194198592847927491)
    ·
      refine ⟨322844379291297889271891237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215229586194198592847927491 322844379291297889271891237)
      ·
        refine ⟨60533321117118354238479607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322844379291297889271891237 60533321117118354238479607)
        ·
          refine ⟨90799981675677531357719411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60533321117118354238479607 90799981675677531357719411)
          ·
            refine ⟨136199972513516297036579117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90799981675677531357719411 136199972513516297036579117)
            ·
              refine ⟨51074989692568611388717169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136199972513516297036579117 51074989692568611388717169)
              ·
                refine ⟨38306242269426458541537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51074989692568611388717169 38306242269426458541537877)
                ·
                  refine ⟨448901276594841311033647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38306242269426458541537877 448901276594841311033647)
                  ·
                    rfl

theorem cell23_7868089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_7868089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868089 prefixEnd_7868089 := by exact prefixLift 7868089
  have htrace : WordTrace (prefixWord ++ tailWord_7868089) baseStart_7868089 baseEnd_7868089 := by
    simpa [prefixWord, tailWord_7868089, baseEnd_7868089] using wordTrace_append hprefix tailTrace_7868089
  have hstable : (prefixWord ++ tailWord_7868089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868089).length < 2 ^ (prefixWord ++ tailWord_7868089).sum := by decide
  have hdescent : baseEnd_7868089 < baseStart_7868089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868133 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_7868133 : Nat := 118140960795 + 7868133 * 2 ^ 59
def prefixEnd_7868133 : Nat := 4983230072969 + 3 ^ 40 * 7868133 * 2
def baseEnd_7868133 : Nat := 4040134082502369627152621

theorem tailTrace_7868133 : CollatzResearch.WordTrace tailWord_7868133 prefixEnd_7868133 4040134082502369627152621 := by
  unfold tailWord_7868133
  simp only [CollatzResearch.WordTrace]
  refine ⟨286974386404105385978505053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191316257602736923985670035 286974386404105385978505053)
  ·
    refine ⟨107615394901539519741939395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286974386404105385978505053 107615394901539519741939395)
    ·
      refine ⟨161423092352309279612909093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107615394901539519741939395 161423092352309279612909093)
      ·
        refine ⟨30266829816057989927420455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161423092352309279612909093 30266829816057989927420455)
        ·
          refine ⟨45400244724086984891130683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266829816057989927420455 45400244724086984891130683)
          ·
            refine ⟨68100367086130477336696025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45400244724086984891130683 68100367086130477336696025)
            ·
              refine ⟨51075275314597858002522019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68100367086130477336696025 51075275314597858002522019)
              ·
                refine ⟨76612912971896787003783029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51075275314597858002522019 76612912971896787003783029)
                ·
                  refine ⟨7182460591115323781604659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76612912971896787003783029 7182460591115323781604659)
                  ·
                    refine ⟨10773690886672985672406989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7182460591115323781604659 10773690886672985672406989)
                    ·
                      refine ⟨4040134082502369627152621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10773690886672985672406989 4040134082502369627152621)
                      ·
                        rfl

theorem cell23_7868133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_7868133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868133 prefixEnd_7868133 := by exact prefixLift 7868133
  have htrace : WordTrace (prefixWord ++ tailWord_7868133) baseStart_7868133 baseEnd_7868133 := by
    simpa [prefixWord, tailWord_7868133, baseEnd_7868133] using wordTrace_append hprefix tailTrace_7868133
  have hstable : (prefixWord ++ tailWord_7868133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868133).length < 2 ^ (prefixWord ++ tailWord_7868133).sum := by decide
  have hdescent : baseEnd_7868133 < baseStart_7868133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868179 : List Nat := [1, 1, 1, 2, 1, 3, 2, 12]
def baseStart_7868179 : Nat := 118140960795 + 7868179 * 2 ^ 59
def prefixEnd_7868179 : Nat := 4983230072969 + 3 ^ 40 * 7868179 * 2
def baseEnd_7868179 : Nat := 149635470467128757302867

theorem tailTrace_7868179 : CollatzResearch.WordTrace tailWord_7868179 prefixEnd_7868179 149635470467128757302867 := by
  unfold tailWord_7868179
  simp only [CollatzResearch.WordTrace]
  refine ⟨286976064161938735834679591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191317376107959157223119727 286976064161938735834679591)
  ·
    refine ⟨430464096242908103752019387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286976064161938735834679591 430464096242908103752019387)
    ·
      refine ⟨645696144364362155628029081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430464096242908103752019387 645696144364362155628029081)
      ·
        refine ⟨484272108273271616721021811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645696144364362155628029081 484272108273271616721021811)
        ·
          refine ⟨726408162409907425081532717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484272108273271616721021811 726408162409907425081532717)
          ·
            refine ⟨272403060903715284405574769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726408162409907425081532717 272403060903715284405574769)
            ·
              refine ⟨204302295677786463304181077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272403060903715284405574769 204302295677786463304181077)
              ·
                refine ⟨149635470467128757302867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 204302295677786463304181077 149635470467128757302867)
                ·
                  rfl

theorem cell23_7868179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 12].length) (baseStart_7868179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868179 prefixEnd_7868179 := by exact prefixLift 7868179
  have htrace : WordTrace (prefixWord ++ tailWord_7868179) baseStart_7868179 baseEnd_7868179 := by
    simpa [prefixWord, tailWord_7868179, baseEnd_7868179] using wordTrace_append hprefix tailTrace_7868179
  have hstable : (prefixWord ++ tailWord_7868179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868179).length < 2 ^ (prefixWord ++ tailWord_7868179).sum := by decide
  have hdescent : baseEnd_7868179 < baseStart_7868179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868183 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 1, 6]
def baseStart_7868183 : Nat := 118140960795 + 7868183 * 2 ^ 59
def prefixEnd_7868183 : Nat := 4983230072969 + 3 ^ 40 * 7868183 * 2
def baseEnd_7868183 : Nat := 1346719918845031477175797

theorem tailTrace_7868183 : CollatzResearch.WordTrace tailWord_7868183 prefixEnd_7868183 1346719918845031477175797 := by
  unfold tailWord_7868183
  simp only [CollatzResearch.WordTrace]
  refine ⟨286976210053924244517825203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191317473369282829678550135 286976210053924244517825203)
  ·
    refine ⟨430464315080886366776737805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286976210053924244517825203 430464315080886366776737805)
    ·
      refine ⟨161424118155332387541276677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430464315080886366776737805 161424118155332387541276677)
      ·
        refine ⟨30267022154124822663989377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161424118155332387541276677 30267022154124822663989377)
        ·
          refine ⟨22700266615593616997992033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30267022154124822663989377 22700266615593616997992033)
          ·
            refine ⟨17025199961695212748494025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22700266615593616997992033 17025199961695212748494025)
            ·
              refine ⟨12768899971271409561370519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17025199961695212748494025 12768899971271409561370519)
              ·
                refine ⟨19153349956907114342055779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12768899971271409561370519 19153349956907114342055779)
                ·
                  refine ⟨28730024935360671513083669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19153349956907114342055779 28730024935360671513083669)
                  ·
                    refine ⟨1346719918845031477175797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28730024935360671513083669 1346719918845031477175797)
                    ·
                      rfl

theorem cell23_7868183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_7868183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868183 prefixEnd_7868183 := by exact prefixLift 7868183
  have htrace : WordTrace (prefixWord ++ tailWord_7868183) baseStart_7868183 baseEnd_7868183 := by
    simpa [prefixWord, tailWord_7868183, baseEnd_7868183] using wordTrace_append hprefix tailTrace_7868183
  have hstable : (prefixWord ++ tailWord_7868183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868183).length < 2 ^ (prefixWord ++ tailWord_7868183).sum := by decide
  have hdescent : baseEnd_7868183 < baseStart_7868183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868193 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_7868193 : Nat := 118140960795 + 7868193 * 2 ^ 59
def prefixEnd_7868193 : Nat := 4983230072969 + 3 ^ 40 * 7868193 * 2
def baseEnd_7868193 : Nat := 4040164891341639392402345

theorem tailTrace_7868193 : CollatzResearch.WordTrace tailWord_7868193 prefixEnd_7868193 4040164891341639392402345 := by
  unfold tailWord_7868193
  simp only [CollatzResearch.WordTrace]
  refine ⟨286976574783888016225689233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191317716522592010817126155 286976574783888016225689233)
  ·
    refine ⟨215232431087916012169266925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286976574783888016225689233 215232431087916012169266925)
    ·
      refine ⟨80712161657968504563475097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215232431087916012169266925 80712161657968504563475097)
      ·
        refine ⟨60534121243476378422606323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80712161657968504563475097 60534121243476378422606323)
        ·
          refine ⟨90801181865214567633909485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60534121243476378422606323 90801181865214567633909485)
          ·
            refine ⟨34050443199455462862716057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90801181865214567633909485 34050443199455462862716057)
            ·
              refine ⟨25537832399591597147037043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34050443199455462862716057 25537832399591597147037043)
              ·
                refine ⟨38306748599387395720555565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25537832399591597147037043 38306748599387395720555565)
                ·
                  refine ⟨14365030724770273395208337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38306748599387395720555565 14365030724770273395208337)
                  ·
                    refine ⟨10773773043577705046406253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14365030724770273395208337 10773773043577705046406253)
                    ·
                      refine ⟨4040164891341639392402345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10773773043577705046406253 4040164891341639392402345)
                      ·
                        rfl

theorem cell23_7868193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_7868193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868193 prefixEnd_7868193 := by exact prefixLift 7868193
  have htrace : WordTrace (prefixWord ++ tailWord_7868193) baseStart_7868193 baseEnd_7868193 := by
    simpa [prefixWord, tailWord_7868193, baseEnd_7868193] using wordTrace_append hprefix tailTrace_7868193
  have hstable : (prefixWord ++ tailWord_7868193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868193).length < 2 ^ (prefixWord ++ tailWord_7868193).sum := by decide
  have hdescent : baseEnd_7868193 < baseStart_7868193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868210 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_7868210 : Nat := 118140960795 + 7868210 * 2 ^ 59
def prefixEnd_7868210 : Nat := 4983230072969 + 3 ^ 40 * 7868210 * 2
def baseEnd_7868210 : Nat := 4040173620512765825889767

theorem tailTrace_7868210 : CollatzResearch.WordTrace tailWord_7868210 prefixEnd_7868210 4040173620512765825889767 := by
  unfold tailWord_7868210
  simp only [CollatzResearch.WordTrace]
  refine ⟨71744298706206607032264521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191318129883217618752705389 71744298706206607032264521)
  ·
    refine ⟨53808224029654955274198391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71744298706206607032264521 53808224029654955274198391)
    ·
      refine ⟨80712336044482432911297587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53808224029654955274198391 80712336044482432911297587)
      ·
        refine ⟨121068504066723649366946381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80712336044482432911297587 121068504066723649366946381)
        ·
          refine ⟨45400689025021368512604893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121068504066723649366946381 45400689025021368512604893)
          ·
            refine ⟨17025258384383013192226835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45400689025021368512604893 17025258384383013192226835)
            ·
              refine ⟨25537887576574519788340253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17025258384383013192226835 25537887576574519788340253)
              ·
                refine ⟨9576707841215444920627595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25537887576574519788340253 9576707841215444920627595)
                ·
                  refine ⟨14365061761823167380941393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9576707841215444920627595 14365061761823167380941393)
                  ·
                    refine ⟨10773796321367375535706045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14365061761823167380941393 10773796321367375535706045)
                    ·
                      refine ⟨4040173620512765825889767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10773796321367375535706045 4040173620512765825889767)
                      ·
                        rfl

theorem cell23_7868210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_7868210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868210 prefixEnd_7868210 := by exact prefixLift 7868210
  have htrace : WordTrace (prefixWord ++ tailWord_7868210) baseStart_7868210 baseEnd_7868210 := by
    simpa [prefixWord, tailWord_7868210, baseEnd_7868210] using wordTrace_append hprefix tailTrace_7868210
  have hstable : (prefixWord ++ tailWord_7868210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868210).length < 2 ^ (prefixWord ++ tailWord_7868210).sum := by decide
  have hdescent : baseEnd_7868210 < baseStart_7868210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868237 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_7868237 : Nat := 118140960795 + 7868237 * 2 ^ 59
def prefixEnd_7868237 : Nat := 4983230072969 + 3 ^ 40 * 7868237 * 2
def baseEnd_7868237 : Nat := 4040187484490437220252143

theorem tailTrace_7868237 : CollatzResearch.WordTrace tailWord_7868237 prefixEnd_7868237 4040187484490437220252143 := by
  unfold tailWord_7868237
  simp only [CollatzResearch.WordTrace]
  refine ⟨286978179595728611740290965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191318786397152407826860643 286978179595728611740290965)
  ·
    refine ⟨13452102168549778675326139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 286978179595728611740290965 13452102168549778675326139)
    ·
      refine ⟨20178153252824668012989209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13452102168549778675326139 20178153252824668012989209)
      ·
        refine ⟨15133614939618501009741907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20178153252824668012989209 15133614939618501009741907)
        ·
          refine ⟨22700422409427751514612861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15133614939618501009741907 22700422409427751514612861)
          ·
            refine ⟨8512658403535406817979823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22700422409427751514612861 8512658403535406817979823)
            ·
              refine ⟨12768987605303110226969735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512658403535406817979823 12768987605303110226969735)
              ·
                refine ⟨19153481407954665340454603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12768987605303110226969735 19153481407954665340454603)
                ·
                  refine ⟨28730222111931998010681905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19153481407954665340454603 28730222111931998010681905)
                  ·
                    refine ⟨21547666583948998508011429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28730222111931998010681905 21547666583948998508011429)
                    ·
                      refine ⟨4040187484490437220252143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21547666583948998508011429 4040187484490437220252143)
                      ·
                        rfl

theorem cell23_7868237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_7868237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868237 prefixEnd_7868237 := by exact prefixLift 7868237
  have htrace : WordTrace (prefixWord ++ tailWord_7868237) baseStart_7868237 baseEnd_7868237 := by
    simpa [prefixWord, tailWord_7868237, baseEnd_7868237] using wordTrace_append hprefix tailTrace_7868237
  have hstable : (prefixWord ++ tailWord_7868237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868237).length < 2 ^ (prefixWord ++ tailWord_7868237).sum := by decide
  have hdescent : baseEnd_7868237 < baseStart_7868237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868297 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 2, 2, 2]
def baseStart_7868297 : Nat := 118140960795 + 7868297 * 2 ^ 59
def prefixEnd_7868297 : Nat := 4983230072969 + 3 ^ 40 * 7868297 * 2
def baseEnd_7868297 : Nat := 4040218293329706985501867

theorem tailTrace_7868297 : CollatzResearch.WordTrace tailWord_7868297 prefixEnd_7868297 4040218293329706985501867 := by
  unfold tailWord_7868297
  simp only [CollatzResearch.WordTrace]
  refine ⟨286980367975511241987475145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191320245317007494658316763 286980367975511241987475145)
  ·
    refine ⟨215235275981633431490606359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286980367975511241987475145 215235275981633431490606359)
    ·
      refine ⟨322852913972450147235909539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215235275981633431490606359 322852913972450147235909539)
      ·
        refine ⟨484279370958675220853864309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322852913972450147235909539 484279370958675220853864309)
        ·
          refine ⟨45401191027375801955049779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484279370958675220853864309 45401191027375801955049779)
          ·
            refine ⟨68101786541063702932574669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45401191027375801955049779 68101786541063702932574669)
            ·
              refine ⟨25538169952898888599715501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68101786541063702932574669 25538169952898888599715501)
              ·
                refine ⟨9576813732337083224893313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25538169952898888599715501 9576813732337083224893313)
                ·
                  refine ⟨7182610299252812418669985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9576813732337083224893313 7182610299252812418669985)
                  ·
                    refine ⟨5386957724439609314002489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7182610299252812418669985 5386957724439609314002489)
                    ·
                      refine ⟨4040218293329706985501867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386957724439609314002489 4040218293329706985501867)
                      ·
                        rfl

theorem cell23_7868297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 2, 2].length) (baseStart_7868297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868297 prefixEnd_7868297 := by exact prefixLift 7868297
  have htrace : WordTrace (prefixWord ++ tailWord_7868297) baseStart_7868297 baseEnd_7868297 := by
    simpa [prefixWord, tailWord_7868297, baseEnd_7868297] using wordTrace_append hprefix tailTrace_7868297
  have hstable : (prefixWord ++ tailWord_7868297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868297).length < 2 ^ (prefixWord ++ tailWord_7868297).sum := by decide
  have hdescent : baseEnd_7868297 < baseStart_7868297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868318 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7868318 : Nat := 118140960795 + 7868318 * 2 ^ 59
def prefixEnd_7868318 : Nat := 4983230072969 + 3 ^ 40 * 7868318 * 2
def baseEnd_7868318 : Nat := 4040229076423451403339271

theorem tailTrace_7868318 : CollatzResearch.WordTrace tailWord_7868318 prefixEnd_7868318 4040229076423451403339271 := by
  unfold tailWord_7868318
  simp only [CollatzResearch.WordTrace]
  refine ⟨35872641738554395321748701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191320755938956775049326405 35872641738554395321748701)
  ·
    refine ⟨13452240651957898245655763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35872641738554395321748701 13452240651957898245655763)
    ·
      refine ⟨20178360977936847368483645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13452240651957898245655763 20178360977936847368483645)
      ·
        refine ⟨7566885366726317763181367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20178360977936847368483645 7566885366726317763181367)
        ·
          refine ⟨11350328050089476644772051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7566885366726317763181367 11350328050089476644772051)
          ·
            refine ⟨17025492075134214967158077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11350328050089476644772051 17025492075134214967158077)
            ·
              refine ⟨6384559528175330612684279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17025492075134214967158077 6384559528175330612684279)
              ·
                refine ⟨9576839292262995919026419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384559528175330612684279 9576839292262995919026419)
                ·
                  refine ⟨14365258938394493878539629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9576839292262995919026419 14365258938394493878539629)
                  ·
                    refine ⟨5386972101897935204452361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14365258938394493878539629 5386972101897935204452361)
                    ·
                      refine ⟨4040229076423451403339271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5386972101897935204452361 4040229076423451403339271)
                      ·
                        rfl

theorem cell23_7868318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7868318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868318 prefixEnd_7868318 := by exact prefixLift 7868318
  have htrace : WordTrace (prefixWord ++ tailWord_7868318) baseStart_7868318 baseEnd_7868318 := by
    simpa [prefixWord, tailWord_7868318, baseEnd_7868318] using wordTrace_append hprefix tailTrace_7868318
  have hstable : (prefixWord ++ tailWord_7868318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868318).length < 2 ^ (prefixWord ++ tailWord_7868318).sum := by decide
  have hdescent : baseEnd_7868318 < baseStart_7868318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868337 : List Nat := [1, 2, 2, 4, 2, 1, 4, 2, 5]
def baseStart_7868337 : Nat := 118140960795 + 7868337 * 2 ^ 59
def prefixEnd_7868337 : Nat := 4983230072969 + 3 ^ 40 * 7868337 * 2
def baseEnd_7868337 : Nat := 448915425839542981000187

theorem tailTrace_7868337 : CollatzResearch.WordTrace tailWord_7868337 prefixEnd_7868337 448915425839542981000187 := by
  unfold tailWord_7868337
  simp only [CollatzResearch.WordTrace]
  refine ⟨286981826895366328818931265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191321217930244219212620843 286981826895366328818931265)
  ·
    refine ⟨215236370171524746614198449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286981826895366328818931265 215236370171524746614198449)
    ·
      refine ⟨161427277628643559960648837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215236370171524746614198449 161427277628643559960648837)
      ·
        refine ⟨30267614555370667492621657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161427277628643559960648837 30267614555370667492621657)
        ·
          refine ⟨22700710916528000619466243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30267614555370667492621657 22700710916528000619466243)
          ·
            refine ⟨34051066374792000929199365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22700710916528000619466243 34051066374792000929199365)
            ·
              refine ⟨6384574945273500174224881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34051066374792000929199365 6384574945273500174224881)
              ·
                refine ⟨4788431208955125130668661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384574945273500174224881 4788431208955125130668661)
                ·
                  refine ⟨448915425839542981000187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788431208955125130668661 448915425839542981000187)
                  ·
                    rfl

theorem cell23_7868337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 5].length) (baseStart_7868337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868337 prefixEnd_7868337 := by exact prefixLift 7868337
  have htrace : WordTrace (prefixWord ++ tailWord_7868337) baseStart_7868337 baseEnd_7868337 := by
    simpa [prefixWord, tailWord_7868337, baseEnd_7868337] using wordTrace_append hprefix tailTrace_7868337
  have hstable : (prefixWord ++ tailWord_7868337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868337).length < 2 ^ (prefixWord ++ tailWord_7868337).sum := by decide
  have hdescent : baseEnd_7868337 < baseStart_7868337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868383 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_7868383 : Nat := 118140960795 + 7868383 * 2 ^ 59
def prefixEnd_7868383 : Nat := 4983230072969 + 3 ^ 40 * 7868383 * 2
def baseEnd_7868383 : Nat := 4040262452665993649026471

theorem tailTrace_7868383 : CollatzResearch.WordTrace tailWord_7868383 prefixEnd_7868383 4040262452665993649026471 := by
  unfold tailWord_7868383
  simp only [CollatzResearch.WordTrace]
  refine ⟨286983504653199678675105803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191322336435466452450070535 286983504653199678675105803)
  ·
    refine ⟨430475256979799518012658705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286983504653199678675105803 430475256979799518012658705)
    ·
      refine ⟨322856442734849638509494029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430475256979799518012658705 322856442734849638509494029)
      ·
        refine ⟨121071166025568614441060261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322856442734849638509494029 121071166025568614441060261)
        ·
          refine ⟨22700843629794115207698799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121071166025568614441060261 22700843629794115207698799)
          ·
            refine ⟨34051265444691172811548199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22700843629794115207698799 34051265444691172811548199)
            ·
              refine ⟨51076898167036759217322299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34051265444691172811548199 51076898167036759217322299)
              ·
                refine ⟨76615347250555138825983449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51076898167036759217322299 76615347250555138825983449)
                ·
                  refine ⟨57461510437916354119487587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76615347250555138825983449 57461510437916354119487587)
                  ·
                    refine ⟨86192265656874531179231381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57461510437916354119487587 86192265656874531179231381)
                    ·
                      refine ⟨4040262452665993649026471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86192265656874531179231381 4040262452665993649026471)
                      ·
                        rfl

theorem cell23_7868383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_7868383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868383 prefixEnd_7868383 := by exact prefixLift 7868383
  have htrace : WordTrace (prefixWord ++ tailWord_7868383) baseStart_7868383 baseEnd_7868383 := by
    simpa [prefixWord, tailWord_7868383, baseEnd_7868383] using wordTrace_append hprefix tailTrace_7868383
  have hstable : (prefixWord ++ tailWord_7868383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868383).length < 2 ^ (prefixWord ++ tailWord_7868383).sum := by decide
  have hdescent : baseEnd_7868383 < baseStart_7868383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868440 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 1, 5]
def baseStart_7868440 : Nat := 118140960795 + 7868440 * 2 ^ 59
def prefixEnd_7868440 : Nat := 4983230072969 + 3 ^ 40 * 7868440 * 2
def baseEnd_7868440 : Nat := 1346763907021099975337903

theorem tailTrace_7868440 : CollatzResearch.WordTrace tailWord_7868440 prefixEnd_7868440 1346763907021099975337903 := by
  unfold tailWord_7868440
  simp only [CollatzResearch.WordTrace]
  refine ⟨143492791806996588704965387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191323722409328784939953849 143492791806996588704965387)
  ·
    refine ⟨215239187710494883057448081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143492791806996588704965387 215239187710494883057448081)
    ·
      refine ⟨161429390782871162293086061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215239187710494883057448081 161429390782871162293086061)
      ·
        refine ⟨60536021543576685859907273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161429390782871162293086061 60536021543576685859907273)
        ·
          refine ⟨45402016157682514394930455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60536021543576685859907273 45402016157682514394930455)
          ·
            refine ⟨68103024236523771592395683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45402016157682514394930455 68103024236523771592395683)
            ·
              refine ⟨102154536354785657388593525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68103024236523771592395683 102154536354785657388593525)
              ·
                refine ⟨9576987783261155380180643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102154536354785657388593525 9576987783261155380180643)
                ·
                  refine ⟨14365481674891733070270965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9576987783261155380180643 14365481674891733070270965)
                  ·
                    refine ⟨1346763907021099975337903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14365481674891733070270965 1346763907021099975337903)
                    ·
                      rfl

theorem cell23_7868440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_7868440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868440 prefixEnd_7868440 := by exact prefixLift 7868440
  have htrace : WordTrace (prefixWord ++ tailWord_7868440) baseStart_7868440 baseEnd_7868440 := by
    simpa [prefixWord, tailWord_7868440, baseEnd_7868440] using wordTrace_append hprefix tailTrace_7868440
  have hstable : (prefixWord ++ tailWord_7868440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868440).length < 2 ^ (prefixWord ++ tailWord_7868440).sum := by decide
  have hdescent : baseEnd_7868440 < baseStart_7868440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868447 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 2, 3, 2]
def baseStart_7868447 : Nat := 118140960795 + 7868447 * 2 ^ 59
def prefixEnd_7868447 : Nat := 4983230072969 + 3 ^ 40 * 7868447 * 2
def baseEnd_7868447 : Nat := 4040295315427881398626177

theorem tailTrace_7868447 : CollatzResearch.WordTrace tailWord_7868447 prefixEnd_7868447 4040295315427881398626177 := by
  unfold tailWord_7868447
  simp only [CollatzResearch.WordTrace]
  refine ⟨286985838924967817605435595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191323892616645211736957063 286985838924967817605435595)
  ·
    refine ⟨430478758387451726408153393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286985838924967817605435595 430478758387451726408153393)
    ·
      refine ⟨322859068790588794806115045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430478758387451726408153393 322859068790588794806115045)
      ·
        refine ⟨60536075398235399026146571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322859068790588794806115045 60536075398235399026146571)
        ·
          refine ⟨90804113097353098539219857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60536075398235399026146571 90804113097353098539219857)
          ·
            refine ⟨68103084823014823904414893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90804113097353098539219857 68103084823014823904414893)
            ·
              refine ⟨25538656808630558964155585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68103084823014823904414893 25538656808630558964155585)
              ·
                refine ⟨19153992606472919223116689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25538656808630558964155585 19153992606472919223116689)
                ·
                  refine ⟨14365494454854689417337517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19153992606472919223116689 14365494454854689417337517)
                  ·
                    refine ⟨5387060420570508531501569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14365494454854689417337517 5387060420570508531501569)
                    ·
                      refine ⟨4040295315427881398626177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387060420570508531501569 4040295315427881398626177)
                      ·
                        rfl

theorem cell23_7868447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_7868447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868447 prefixEnd_7868447 := by exact prefixLift 7868447
  have htrace : WordTrace (prefixWord ++ tailWord_7868447) baseStart_7868447 baseEnd_7868447 := by
    simpa [prefixWord, tailWord_7868447, baseEnd_7868447] using wordTrace_append hprefix tailTrace_7868447
  have hstable : (prefixWord ++ tailWord_7868447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868447).length < 2 ^ (prefixWord ++ tailWord_7868447).sum := by decide
  have hdescent : baseEnd_7868447 < baseStart_7868447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868460 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 2, 6, 2]
def baseStart_7868460 : Nat := 118140960795 + 7868460 * 2 ^ 59
def prefixEnd_7868460 : Nat := 4983230072969 + 3 ^ 40 * 7868460 * 2
def baseEnd_7868460 : Nat := 4040301990676389847763617

theorem tailTrace_7868460 : CollatzResearch.WordTrace tailWord_7868460 prefixEnd_7868460 4040301990676389847763617 := by
  unfold tailWord_7868460
  simp only [CollatzResearch.WordTrace]
  refine ⟨143493156536960360412829417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191324208715947147217105889 143493156536960360412829417)
  ·
    refine ⟨107619867402720270309622063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143493156536960360412829417 107619867402720270309622063)
    ·
      refine ⟨161429801104080405464433095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107619867402720270309622063 161429801104080405464433095)
      ·
        refine ⟨242144701656120608196649643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161429801104080405464433095 242144701656120608196649643)
        ·
          refine ⟨363217052484180912294974465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242144701656120608196649643 363217052484180912294974465)
          ·
            refine ⟨272412789363135684221230849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363217052484180912294974465 272412789363135684221230849)
            ·
              refine ⟨204309592022351763165923137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272412789363135684221230849 204309592022351763165923137)
              ·
                refine ⟨153232194016763822374442353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204309592022351763165923137 153232194016763822374442353)
                ·
                  refine ⟨114924145512572866780831765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153232194016763822374442353 114924145512572866780831765)
                  ·
                    refine ⟨5387069320901853130351489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114924145512572866780831765 5387069320901853130351489)
                    ·
                      refine ⟨4040301990676389847763617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387069320901853130351489 4040301990676389847763617)
                      ·
                        rfl

theorem cell23_7868460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_7868460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868460 prefixEnd_7868460 := by exact prefixLift 7868460
  have htrace : WordTrace (prefixWord ++ tailWord_7868460) baseStart_7868460 baseEnd_7868460 := by
    simpa [prefixWord, tailWord_7868460, baseEnd_7868460] using wordTrace_append hprefix tailTrace_7868460
  have hstable : (prefixWord ++ tailWord_7868460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868460).length < 2 ^ (prefixWord ++ tailWord_7868460).sum := by decide
  have hdescent : baseEnd_7868460 < baseStart_7868460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868463 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_7868463 : Nat := 118140960795 + 7868463 * 2 ^ 59
def prefixEnd_7868463 : Nat := 4983230072969 + 3 ^ 40 * 7868463 * 2
def baseEnd_7868463 : Nat := 4040303531118353336026103

theorem tailTrace_7868463 : CollatzResearch.WordTrace tailWord_7868463 prefixEnd_7868463 4040303531118353336026103 := by
  unfold tailWord_7868463
  simp only [CollatzResearch.WordTrace]
  refine ⟨286986422492909852338018043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191324281661939901558678695 286986422492909852338018043)
  ·
    refine ⟨430479633739364778507027065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286986422492909852338018043 430479633739364778507027065)
    ·
      refine ⟨322859725304523583880270299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430479633739364778507027065 322859725304523583880270299)
      ·
        refine ⟨484289587956785375820405449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322859725304523583880270299 484289587956785375820405449)
        ·
          refine ⟨363217190967589031865304087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484289587956785375820405449 363217190967589031865304087)
          ·
            refine ⟨544825786451383547797956131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363217190967589031865304087 544825786451383547797956131)
            ·
              refine ⟨817238679677075321696934197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544825786451383547797956131 817238679677075321696934197)
              ·
                refine ⟨76616126219725811409087581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 817238679677075321696934197 76616126219725811409087581)
                ·
                  refine ⟨28731047332397179278407843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76616126219725811409087581 28731047332397179278407843)
                  ·
                    refine ⟨43096570998595768917611765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28731047332397179278407843 43096570998595768917611765)
                    ·
                      refine ⟨4040303531118353336026103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43096570998595768917611765 4040303531118353336026103)
                      ·
                        rfl

theorem cell23_7868463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_7868463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868463 prefixEnd_7868463 := by exact prefixLift 7868463
  have htrace : WordTrace (prefixWord ++ tailWord_7868463) baseStart_7868463 baseEnd_7868463 := by
    simpa [prefixWord, tailWord_7868463, baseEnd_7868463] using wordTrace_append hprefix tailTrace_7868463
  have hstable : (prefixWord ++ tailWord_7868463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868463).length < 2 ^ (prefixWord ++ tailWord_7868463).sum := by decide
  have hdescent : baseEnd_7868463 < baseStart_7868463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868494 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_7868494 : Nat := 118140960795 + 7868494 * 2 ^ 59
def prefixEnd_7868494 : Nat := 4983230072969 + 3 ^ 40 * 7868494 * 2
def baseEnd_7868494 : Nat := 4040319449018642714738461

theorem tailTrace_7868494 : CollatzResearch.WordTrace tailWord_7868494 prefixEnd_7868494 4040319449018642714738461 := by
  unfold tailWord_7868494
  simp only [CollatzResearch.WordTrace]
  refine ⟨35873444144474693079049567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191325035437198363088264357 35873444144474693079049567)
  ·
    refine ⟨53810166216712039618574351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35873444144474693079049567 53810166216712039618574351)
    ·
      refine ⟨80715249325068059427861527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53810166216712039618574351 80715249325068059427861527)
      ·
        refine ⟨121072873987602089141792291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80715249325068059427861527 121072873987602089141792291)
        ·
          refine ⟨181609310981403133712688437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121072873987602089141792291 181609310981403133712688437)
          ·
            refine ⟨17025872904506543785564541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181609310981403133712688437 17025872904506543785564541)
            ·
              refine ⟨6384702339189953919586703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17025872904506543785564541 6384702339189953919586703)
              ·
                refine ⟨9577053508784930879380055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384702339189953919586703 9577053508784930879380055)
                ·
                  refine ⟨14365580263177396319070083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9577053508784930879380055 14365580263177396319070083)
                  ·
                    refine ⟨21548370394766094478605125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14365580263177396319070083 21548370394766094478605125)
                    ·
                      refine ⟨4040319449018642714738461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21548370394766094478605125 4040319449018642714738461)
                      ·
                        rfl

theorem cell23_7868494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_7868494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868494 prefixEnd_7868494 := by exact prefixLift 7868494
  have htrace : WordTrace (prefixWord ++ tailWord_7868494) baseStart_7868494 baseEnd_7868494 := by
    simpa [prefixWord, tailWord_7868494, baseEnd_7868494] using wordTrace_append hprefix tailTrace_7868494
  have hstable : (prefixWord ++ tailWord_7868494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868494).length < 2 ^ (prefixWord ++ tailWord_7868494).sum := by decide
  have hdescent : baseEnd_7868494 < baseStart_7868494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868527 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 3]
def baseStart_7868527 : Nat := 118140960795 + 7868527 * 2 ^ 59
def prefixEnd_7868527 : Nat := 4983230072969 + 3 ^ 40 * 7868527 * 2
def baseEnd_7868527 : Nat := 4040336393880241085625809

theorem tailTrace_7868527 : CollatzResearch.WordTrace tailWord_7868527 prefixEnd_7868527 4040336393880241085625809 := by
  unfold tailWord_7868527
  simp only [CollatzResearch.WordTrace]
  refine ⟨286988756764677991268347835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191325837843118660845565223 286988756764677991268347835)
  ·
    refine ⟨430483135147016986902521753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286988756764677991268347835 430483135147016986902521753)
    ·
      refine ⟨322862351360262740176891315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430483135147016986902521753 322862351360262740176891315)
      ·
        refine ⟨484293527040394110265336973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322862351360262740176891315 484293527040394110265336973)
        ·
          refine ⟨181610072640147791349501365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484293527040394110265336973 181610072640147791349501365)
          ·
            refine ⟨17025944310013855439015753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181610072640147791349501365 17025944310013855439015753)
            ·
              refine ⟨12769458232510391579261815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17025944310013855439015753 12769458232510391579261815)
              ·
                refine ⟨19154187348765587368892723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12769458232510391579261815 19154187348765587368892723)
                ·
                  refine ⟨28731281023148381053339085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19154187348765587368892723 28731281023148381053339085)
                  ·
                    refine ⟨10774230383680642895002157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28731281023148381053339085 10774230383680642895002157)
                    ·
                      refine ⟨4040336393880241085625809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10774230383680642895002157 4040336393880241085625809)
                      ·
                        rfl

theorem cell23_7868527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_7868527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868527 prefixEnd_7868527 := by exact prefixLift 7868527
  have htrace : WordTrace (prefixWord ++ tailWord_7868527) baseStart_7868527 baseEnd_7868527 := by
    simpa [prefixWord, tailWord_7868527, baseEnd_7868527] using wordTrace_append hprefix tailTrace_7868527
  have hstable : (prefixWord ++ tailWord_7868527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868527).length < 2 ^ (prefixWord ++ tailWord_7868527).sum := by decide
  have hdescent : baseEnd_7868527 < baseStart_7868527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868578 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7868578 : Nat := 118140960795 + 7868578 * 2 ^ 59
def prefixEnd_7868578 : Nat := 4983230072969 + 3 ^ 40 * 7868578 * 2
def baseEnd_7868578 : Nat := 4040362581393620386088075

theorem tailTrace_7868578 : CollatzResearch.WordTrace tailWord_7868578 prefixEnd_7868578 4040362581393620386088075 := by
  unfold tailWord_7868578
  simp only [CollatzResearch.WordTrace]
  refine ⟨71747654221873306744613597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191327077924995484652302925 71747654221873306744613597)
  ·
    refine ⟨26905370333202490029230099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71747654221873306744613597 26905370333202490029230099)
    ·
      refine ⟨40358055499803735043845149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26905370333202490029230099 40358055499803735043845149)
      ·
        refine ⟨15134270812426400641441931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40358055499803735043845149 15134270812426400641441931)
        ·
          refine ⟨22701406218639600962162897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15134270812426400641441931 22701406218639600962162897)
          ·
            refine ⟨17026054663979700721622173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22701406218639600962162897 17026054663979700721622173)
            ·
              refine ⟨6384770498992387770608315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17026054663979700721622173 6384770498992387770608315)
              ·
                refine ⟨9577155748488581655912473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384770498992387770608315 9577155748488581655912473)
                ·
                  refine ⟨7182866811366436241934355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9577155748488581655912473 7182866811366436241934355)
                  ·
                    refine ⟨10774300217049654362901533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7182866811366436241934355 10774300217049654362901533)
                    ·
                      refine ⟨4040362581393620386088075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10774300217049654362901533 4040362581393620386088075)
                      ·
                        rfl

theorem cell23_7868578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7868578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868578 prefixEnd_7868578 := by exact prefixLift 7868578
  have htrace : WordTrace (prefixWord ++ tailWord_7868578) baseStart_7868578 baseEnd_7868578 := by
    simpa [prefixWord, tailWord_7868578, baseEnd_7868578] using wordTrace_append hprefix tailTrace_7868578
  have hstable : (prefixWord ++ tailWord_7868578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868578).length < 2 ^ (prefixWord ++ tailWord_7868578).sum := by decide
  have hdescent : baseEnd_7868578 < baseStart_7868578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868596 : List Nat := [2, 5, 3, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7868596 : Nat := 118140960795 + 7868596 * 2 ^ 59
def prefixEnd_7868596 : Nat := 4983230072969 + 3 ^ 40 * 7868596 * 2
def baseEnd_7868596 : Nat := 4040371824045401315662993

theorem tailTrace_7868596 : CollatzResearch.WordTrace tailWord_7868596 prefixEnd_7868596 4040371824045401315662993 := by
  unfold tailWord_7868596
  simp only [CollatzResearch.WordTrace]
  refine ⟨143495636700714008026304821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191327515600952010701739761 143495636700714008026304821)
  ·
    refine ⟨13452715940691938252466077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143495636700714008026304821 13452715940691938252466077)
    ·
      refine ⟨5044768477759476844674779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13452715940691938252466077 5044768477759476844674779)
      ·
        refine ⟨7567152716639215267012169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5044768477759476844674779 7567152716639215267012169)
        ·
          refine ⟨5675364537479411450259127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7567152716639215267012169 5675364537479411450259127)
          ·
            refine ⟨8513046806219117175388691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675364537479411450259127 8513046806219117175388691)
            ·
              refine ⟨12769570209328675763083037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513046806219117175388691 12769570209328675763083037)
              ·
                refine ⟨4788588828498253411156139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12769570209328675763083037 4788588828498253411156139)
                ·
                  refine ⟨7182883242747380116734209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788588828498253411156139 7182883242747380116734209)
                  ·
                    refine ⟨5387162432060535087550657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7182883242747380116734209 5387162432060535087550657)
                    ·
                      refine ⟨4040371824045401315662993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387162432060535087550657 4040371824045401315662993)
                      ·
                        rfl

theorem cell23_7868596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7868596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868596 prefixEnd_7868596 := by exact prefixLift 7868596
  have htrace : WordTrace (prefixWord ++ tailWord_7868596) baseStart_7868596 baseEnd_7868596 := by
    simpa [prefixWord, tailWord_7868596, baseEnd_7868596] using wordTrace_append hprefix tailTrace_7868596
  have hstable : (prefixWord ++ tailWord_7868596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868596).length < 2 ^ (prefixWord ++ tailWord_7868596).sum := by decide
  have hdescent : baseEnd_7868596 < baseStart_7868596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868657 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_7868657 : Nat := 118140960795 + 7868657 * 2 ^ 59
def prefixEnd_7868657 : Nat := 4983230072969 + 3 ^ 40 * 7868657 * 2
def baseEnd_7868657 : Nat := 4040403146365325577000211

theorem tailTrace_7868657 : CollatzResearch.WordTrace tailWord_7868657 prefixEnd_7868657 4040403146365325577000211 := by
  unfold tailWord_7868657
  simp only [CollatzResearch.WordTrace]
  refine ⟨286993498254207023470580225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191328998836138015647053483 286993498254207023470580225)
  ·
    refine ⟨215245123690655267602935169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286993498254207023470580225 215245123690655267602935169)
    ·
      refine ⟨161433842767991450702201377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215245123690655267602935169 161433842767991450702201377)
      ·
        refine ⟨121075382075993588026651033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161433842767991450702201377 121075382075993588026651033)
        ·
          refine ⟨90806536556995191019988275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121075382075993588026651033 90806536556995191019988275)
          ·
            refine ⟨136209804835492786529982413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90806536556995191019988275 136209804835492786529982413)
            ·
              refine ⟨51078676813309794948743405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136209804835492786529982413 51078676813309794948743405)
              ·
                refine ⟨19154503804991173105778777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51078676813309794948743405 19154503804991173105778777)
                ·
                  refine ⟨14365877853743379829334083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19154503804991173105778777 14365877853743379829334083)
                  ·
                    refine ⟨21548816780615069744001125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14365877853743379829334083 21548816780615069744001125)
                    ·
                      refine ⟨4040403146365325577000211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21548816780615069744001125 4040403146365325577000211)
                      ·
                        rfl

theorem cell23_7868657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_7868657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868657 prefixEnd_7868657 := by exact prefixLift 7868657
  have htrace : WordTrace (prefixWord ++ tailWord_7868657) baseStart_7868657 baseEnd_7868657 := by
    simpa [prefixWord, tailWord_7868657, baseEnd_7868657] using wordTrace_append hprefix tailTrace_7868657
  have hstable : (prefixWord ++ tailWord_7868657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868657).length < 2 ^ (prefixWord ++ tailWord_7868657).sum := by decide
  have hdescent : baseEnd_7868657 < baseStart_7868657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868677 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_7868677 : Nat := 118140960795 + 7868677 * 2 ^ 59
def prefixEnd_7868677 : Nat := 4983230072969 + 3 ^ 40 * 7868677 * 2
def baseEnd_7868677 : Nat := 4040413415978415498750119

theorem tailTrace_7868677 : CollatzResearch.WordTrace tailWord_7868677 prefixEnd_7868677 4040413415978415498750119 := by
  unfold tailWord_7868677
  simp only [CollatzResearch.WordTrace]
  refine ⟨286994227714134566886308285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191329485142756377924205523 286994227714134566886308285)
  ·
    refine ⟨107622835392800462582365607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286994227714134566886308285 107622835392800462582365607)
    ·
      refine ⟨161434253089200693873548411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107622835392800462582365607 161434253089200693873548411)
      ·
        refine ⟨242151379633801040810322617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161434253089200693873548411 242151379633801040810322617)
        ·
          refine ⟨181613534725350780607741963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242151379633801040810322617 181613534725350780607741963)
          ·
            refine ⟨272420302088026170911612945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181613534725350780607741963 272420302088026170911612945)
            ·
              refine ⟨204315226566019628183709709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272420302088026170911612945 204315226566019628183709709)
              ·
                refine ⟨76618209962257360568891141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204315226566019628183709709 76618209962257360568891141)
                ·
                  refine ⟨14365914367923255106667089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76618209962257360568891141 14365914367923255106667089)
                  ·
                    refine ⟨10774435775942441330000317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14365914367923255106667089 10774435775942441330000317)
                    ·
                      refine ⟨4040413415978415498750119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10774435775942441330000317 4040413415978415498750119)
                      ·
                        rfl

theorem cell23_7868677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_7868677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868677 prefixEnd_7868677 := by exact prefixLift 7868677
  have htrace : WordTrace (prefixWord ++ tailWord_7868677) baseStart_7868677 baseEnd_7868677 := by
    simpa [prefixWord, tailWord_7868677, baseEnd_7868677] using wordTrace_append hprefix tailTrace_7868677
  have hstable : (prefixWord ++ tailWord_7868677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868677).length < 2 ^ (prefixWord ++ tailWord_7868677).sum := by decide
  have hdescent : baseEnd_7868677 < baseStart_7868677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868701 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_7868701 : Nat := 118140960795 + 7868701 * 2 ^ 59
def prefixEnd_7868701 : Nat := 4983230072969 + 3 ^ 40 * 7868701 * 2
def baseEnd_7868701 : Nat := 1346808579838041134950003

theorem tailTrace_7868701 : CollatzResearch.WordTrace tailWord_7868701 prefixEnd_7868701 1346808579838041134950003 := by
  unfold tailWord_7868701
  simp only [CollatzResearch.WordTrace]
  refine ⟨286995103066047618985181957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191330068710698412656787971 286995103066047618985181957)
  ·
    refine ⟨53811581824883928559721617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286995103066047618985181957 53811581824883928559721617)
    ·
      refine ⟨40358686368662946419791213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53811581824883928559721617 40358686368662946419791213)
      ·
        refine ⟨15134507388248604907421705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40358686368662946419791213 15134507388248604907421705)
        ·
          refine ⟨11350880541186453680566279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15134507388248604907421705 11350880541186453680566279)
          ·
            refine ⟨17026320811779680520849419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11350880541186453680566279 17026320811779680520849419)
            ·
              refine ⟨25539481217669520781274129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17026320811779680520849419 25539481217669520781274129)
              ·
                refine ⟨19154610913252140585955597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25539481217669520781274129 19154610913252140585955597)
                ·
                  refine ⟨7182979092469552719733349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19154610913252140585955597 7182979092469552719733349)
                  ·
                    refine ⟨1346808579838041134950003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7182979092469552719733349 1346808579838041134950003)
                    ·
                      rfl

theorem cell23_7868701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_7868701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868701 prefixEnd_7868701 := by exact prefixLift 7868701
  have htrace : WordTrace (prefixWord ++ tailWord_7868701) baseStart_7868701 baseEnd_7868701 := by
    simpa [prefixWord, tailWord_7868701, baseEnd_7868701] using wordTrace_append hprefix tailTrace_7868701
  have hstable : (prefixWord ++ tailWord_7868701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868701).length < 2 ^ (prefixWord ++ tailWord_7868701).sum := by decide
  have hdescent : baseEnd_7868701 < baseStart_7868701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868747 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 4]
def baseStart_7868747 : Nat := 118140960795 + 7868747 * 2 ^ 59
def prefixEnd_7868747 : Nat := 4983230072969 + 3 ^ 40 * 7868747 * 2
def baseEnd_7868747 : Nat := 4040449359624230224874797

theorem tailTrace_7868747 : CollatzResearch.WordTrace tailWord_7868747 prefixEnd_7868747 4040449359624230224874797 := by
  unfold tailWord_7868747
  simp only [CollatzResearch.WordTrace]
  refine ⟨286996780823880968841356495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191331187215920645894237663 286996780823880968841356495)
  ·
    refine ⟨430495171235821453262034743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286996780823880968841356495 430495171235821453262034743)
    ·
      refine ⟨645742756853732179893052115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430495171235821453262034743 645742756853732179893052115)
      ·
        refine ⟨968614135280598269839578173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645742756853732179893052115 968614135280598269839578173)
        ·
          refine ⟨363230300730224351189841815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968614135280598269839578173 363230300730224351189841815)
          ·
            refine ⟨544845451095336526784762723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363230300730224351189841815 544845451095336526784762723)
            ·
              refine ⟨817268176643004790177144085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544845451095336526784762723 817268176643004790177144085)
              ·
                refine ⟨38309445780140849539553629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 817268176643004790177144085 38309445780140849539553629)
                ·
                  refine ⟨14366042167552818577332611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38309445780140849539553629 14366042167552818577332611)
                  ·
                    refine ⟨21549063251329227865998917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14366042167552818577332611 21549063251329227865998917)
                    ·
                      refine ⟨4040449359624230224874797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21549063251329227865998917 4040449359624230224874797)
                      ·
                        rfl

theorem cell23_7868747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 4].length) (baseStart_7868747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868747 prefixEnd_7868747 := by exact prefixLift 7868747
  have htrace : WordTrace (prefixWord ++ tailWord_7868747) baseStart_7868747 baseEnd_7868747 := by
    simpa [prefixWord, tailWord_7868747, baseEnd_7868747] using wordTrace_append hprefix tailTrace_7868747
  have hstable : (prefixWord ++ tailWord_7868747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868747).length < 2 ^ (prefixWord ++ tailWord_7868747).sum := by decide
  have hdescent : baseEnd_7868747 < baseStart_7868747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868775 : List Nat := [1, 1, 5, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_7868775 : Nat := 118140960795 + 7868775 * 2 ^ 59
def prefixEnd_7868775 : Nat := 4983230072969 + 3 ^ 40 * 7868775 * 2
def baseEnd_7868775 : Nat := 4040463737082556115324669

theorem tailTrace_7868775 : CollatzResearch.WordTrace tailWord_7868775 prefixEnd_7868775 4040463737082556115324669 := by
  unfold tailWord_7868775
  simp only [CollatzResearch.WordTrace]
  refine ⟨286997802067779529623375779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191331868045186353082250519 286997802067779529623375779)
  ·
    refine ⟨430496703101669294435063669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286997802067779529623375779 430496703101669294435063669)
    ·
      refine ⟨40359065915781496353287219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430496703101669294435063669 40359065915781496353287219)
      ·
        refine ⟨60538598873672244529930829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40359065915781496353287219 60538598873672244529930829)
        ·
          refine ⟨22701974577627091698724061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60538598873672244529930829 22701974577627091698724061)
          ·
            refine ⟨8513240466610159387021523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22701974577627091698724061 8513240466610159387021523)
            ·
              refine ⟨12769860699915239080532285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513240466610159387021523 12769860699915239080532285)
              ·
                refine ⟨4788697762468214655199607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12769860699915239080532285 4788697762468214655199607)
                ·
                  refine ⟨7183046643702321982799411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788697762468214655199607 7183046643702321982799411)
                  ·
                    refine ⟨10774569965553482974199117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7183046643702321982799411 10774569965553482974199117)
                    ·
                      refine ⟨4040463737082556115324669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10774569965553482974199117 4040463737082556115324669)
                      ·
                        rfl

theorem cell23_7868775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_7868775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868775 prefixEnd_7868775 := by exact prefixLift 7868775
  have htrace : WordTrace (prefixWord ++ tailWord_7868775) baseStart_7868775 baseEnd_7868775 := by
    simpa [prefixWord, tailWord_7868775, baseEnd_7868775] using wordTrace_append hprefix tailTrace_7868775
  have hstable : (prefixWord ++ tailWord_7868775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868775).length < 2 ^ (prefixWord ++ tailWord_7868775).sum := by decide
  have hdescent : baseEnd_7868775 < baseStart_7868775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868777 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_7868777 : Nat := 118140960795 + 7868777 * 2 ^ 59
def prefixEnd_7868777 : Nat := 4983230072969 + 3 ^ 40 * 7868777 * 2
def baseEnd_7868777 : Nat := 4040464764043865107499659

theorem tailTrace_7868777 : CollatzResearch.WordTrace tailWord_7868777 prefixEnd_7868777 4040464764043865107499659 := by
  unfold tailWord_7868777
  simp only [CollatzResearch.WordTrace]
  refine ⟨286997875013772283964948585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191331916675848189309965723 286997875013772283964948585)
  ·
    refine ⟨215248406260329212973711439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286997875013772283964948585 215248406260329212973711439)
    ·
      refine ⟨322872609390493819460567159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215248406260329212973711439 322872609390493819460567159)
      ·
        refine ⟨484308914085740729190850739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322872609390493819460567159 484308914085740729190850739)
        ·
          refine ⟨726463371128611093786276109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484308914085740729190850739 726463371128611093786276109)
          ·
            refine ⟨272423764173229160169853541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726463371128611093786276109 272423764173229160169853541)
            ·
              refine ⟨51079455782480467531847539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272423764173229160169853541 51079455782480467531847539)
              ·
                refine ⟨76619183673720701297771309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51079455782480467531847539 76619183673720701297771309)
                ·
                  refine ⟨28732193877645262986664241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76619183673720701297771309 28732193877645262986664241)
                  ·
                    refine ⟨21549145408233947239998181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28732193877645262986664241 21549145408233947239998181)
                    ·
                      refine ⟨4040464764043865107499659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21549145408233947239998181 4040464764043865107499659)
                      ·
                        rfl

theorem cell23_7868777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_7868777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868777 prefixEnd_7868777 := by exact prefixLift 7868777
  have htrace : WordTrace (prefixWord ++ tailWord_7868777) baseStart_7868777 baseEnd_7868777 := by
    simpa [prefixWord, tailWord_7868777, baseEnd_7868777] using wordTrace_append hprefix tailTrace_7868777
  have hstable : (prefixWord ++ tailWord_7868777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868777).length < 2 ^ (prefixWord ++ tailWord_7868777).sum := by decide
  have hdescent : baseEnd_7868777 < baseStart_7868777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868784 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5]
def baseStart_7868784 : Nat := 118140960795 + 7868784 * 2 ^ 59
def prefixEnd_7868784 : Nat := 4983230072969 + 3 ^ 40 * 7868784 * 2
def baseEnd_7868784 : Nat := 4040468358408446580112127

theorem tailTrace_7868784 : CollatzResearch.WordTrace tailWord_7868784 prefixEnd_7868784 4040468358408446580112127 := by
  unfold tailWord_7868784
  simp only [CollatzResearch.WordTrace]
  refine ⟨143499065162373462080226703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191332086883164616106968937 143499065162373462080226703)
  ·
    refine ⟨215248597743560193120340055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143499065162373462080226703 215248597743560193120340055)
    ·
      refine ⟨322872896615340289680510083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215248597743560193120340055 322872896615340289680510083)
      ·
        refine ⟨484309344923010434520765125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322872896615340289680510083 484309344923010434520765125)
        ·
          refine ⟨90808002173064456472643461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484309344923010434520765125 90808002173064456472643461)
          ·
            refine ⟨17026500407449585588620649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90808002173064456472643461 17026500407449585588620649)
            ·
              refine ⟨12769875305587189191465487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17026500407449585588620649 12769875305587189191465487)
              ·
                refine ⟨19154812958380783787198231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12769875305587189191465487 19154812958380783787198231)
                ·
                  refine ⟨28732219437571175680797347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19154812958380783787198231 28732219437571175680797347)
                  ·
                    refine ⟨43098329156356763521196021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28732219437571175680797347 43098329156356763521196021)
                    ·
                      refine ⟨4040468358408446580112127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43098329156356763521196021 4040468358408446580112127)
                      ·
                        rfl

theorem cell23_7868784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_7868784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868784 prefixEnd_7868784 := by exact prefixLift 7868784
  have htrace : WordTrace (prefixWord ++ tailWord_7868784) baseStart_7868784 baseEnd_7868784 := by
    simpa [prefixWord, tailWord_7868784, baseEnd_7868784] using wordTrace_append hprefix tailTrace_7868784
  have hstable : (prefixWord ++ tailWord_7868784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868784).length < 2 ^ (prefixWord ++ tailWord_7868784).sum := by decide
  have hdescent : baseEnd_7868784 < baseStart_7868784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868807 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_7868807 : Nat := 118140960795 + 7868807 * 2 ^ 59
def prefixEnd_7868807 : Nat := 4983230072969 + 3 ^ 40 * 7868807 * 2
def baseEnd_7868807 : Nat := 4040480168463499990124521

theorem tailTrace_7868807 : CollatzResearch.WordTrace tailWord_7868807 prefixEnd_7868807 4040480168463499990124521 := by
  unfold tailWord_7868807
  simp only [CollatzResearch.WordTrace]
  refine ⟨286998969203663599088540675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191332646135775732725693783 286998969203663599088540675)
  ·
    refine ⟨430498453805495398632811013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286998969203663599088540675 430498453805495398632811013)
    ·
      refine ⟨80718460088530387243652065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430498453805495398632811013 80718460088530387243652065)
      ·
        refine ⟨60538845066397790432739049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80718460088530387243652065 60538845066397790432739049)
        ·
          refine ⟨45404133799798342824554287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60538845066397790432739049 45404133799798342824554287)
          ·
            refine ⟨68106200699697514236831431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45404133799798342824554287 68106200699697514236831431)
            ·
              refine ⟨102159301049546271355247147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68106200699697514236831431 102159301049546271355247147)
              ·
                refine ⟨153238951574319407032870721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102159301049546271355247147 153238951574319407032870721)
                ·
                  refine ⟨114929213680739555274653041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153238951574319407032870721 114929213680739555274653041)
                  ·
                    refine ⟨86196910260554666455989781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114929213680739555274653041 86196910260554666455989781)
                    ·
                      refine ⟨4040480168463499990124521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86196910260554666455989781 4040480168463499990124521)
                      ·
                        rfl

theorem cell23_7868807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_7868807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868807 prefixEnd_7868807 := by exact prefixLift 7868807
  have htrace : WordTrace (prefixWord ++ tailWord_7868807) baseStart_7868807 baseEnd_7868807 := by
    simpa [prefixWord, tailWord_7868807, baseEnd_7868807] using wordTrace_append hprefix tailTrace_7868807
  have hstable : (prefixWord ++ tailWord_7868807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868807).length < 2 ^ (prefixWord ++ tailWord_7868807).sum := by decide
  have hdescent : baseEnd_7868807 < baseStart_7868807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868841 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 1, 3, 2]
def baseStart_7868841 : Nat := 118140960795 + 7868841 * 2 ^ 59
def prefixEnd_7868841 : Nat := 4983230072969 + 3 ^ 40 * 7868841 * 2
def baseEnd_7868841 : Nat := 4040497626805752857099365

theorem tailTrace_7868841 : CollatzResearch.WordTrace tailWord_7868841 prefixEnd_7868841 4040497626805752857099365 := by
  unfold tailWord_7868841
  simp only [CollatzResearch.WordTrace]
  refine ⟨287000209285540422895278377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191333472857026948596852251 287000209285540422895278377)
  ·
    refine ⟨215250156964155317171458783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287000209285540422895278377 215250156964155317171458783)
    ·
      refine ⟨322875235446232975757188175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215250156964155317171458783 322875235446232975757188175)
      ·
        refine ⟨484312853169349463635782263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322875235446232975757188175 484312853169349463635782263)
        ·
          refine ⟨726469279754024195453673395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484312853169349463635782263 726469279754024195453673395)
          ·
            refine ⟨1089703919631036293180510093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726469279754024195453673395 1089703919631036293180510093)
            ·
              refine ⟨408638969861638609942691285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1089703919631036293180510093 408638969861638609942691285)
              ·
                refine ⟨9577475856132154920531827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 408638969861638609942691285 9577475856132154920531827)
                ·
                  refine ⟨14366213784198232380797741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9577475856132154920531827 14366213784198232380797741)
                  ·
                    refine ⟨5387330169074337142799153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14366213784198232380797741 5387330169074337142799153)
                    ·
                      refine ⟨4040497626805752857099365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387330169074337142799153 4040497626805752857099365)
                      ·
                        rfl

theorem cell23_7868841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 3, 2].length) (baseStart_7868841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868841 prefixEnd_7868841 := by exact prefixLift 7868841
  have htrace : WordTrace (prefixWord ++ tailWord_7868841) baseStart_7868841 baseEnd_7868841 := by
    simpa [prefixWord, tailWord_7868841, baseEnd_7868841] using wordTrace_append hprefix tailTrace_7868841
  have hstable : (prefixWord ++ tailWord_7868841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868841).length < 2 ^ (prefixWord ++ tailWord_7868841).sum := by decide
  have hdescent : baseEnd_7868841 < baseStart_7868841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868842 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7868842 : Nat := 118140960795 + 7868842 * 2 ^ 59
def prefixEnd_7868842 : Nat := 4983230072969 + 3 ^ 40 * 7868842 * 2
def baseEnd_7868842 : Nat := 1346832713428802451062287

theorem tailTrace_7868842 : CollatzResearch.WordTrace tailWord_7868842 prefixEnd_7868842 1346832713428802451062287 := by
  unfold tailWord_7868842
  simp only [CollatzResearch.WordTrace]
  refine ⟨71750061439634200016516195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191333497172357866710709853 71750061439634200016516195)
  ·
    refine ⟨107625092159451300024774293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71750061439634200016516195 107625092159451300024774293)
    ·
      refine ⟨5044926194974279688661295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107625092159451300024774293 5044926194974279688661295)
      ·
        refine ⟨7567389292461419532991943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5044926194974279688661295 7567389292461419532991943)
        ·
          refine ⟨11351083938692129299487915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7567389292461419532991943 11351083938692129299487915)
          ·
            refine ⟨17026625908038193949231873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11351083938692129299487915 17026625908038193949231873)
            ·
              refine ⟨12769969431028645461923905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17026625908038193949231873 12769969431028645461923905)
              ·
                refine ⟨9577477073271484096442929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12769969431028645461923905 9577477073271484096442929)
                ·
                  refine ⟨7183107804953613072332197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9577477073271484096442929 7183107804953613072332197)
                  ·
                    refine ⟨1346832713428802451062287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7183107804953613072332197 1346832713428802451062287)
                    ·
                      rfl

theorem cell23_7868842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7868842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868842 prefixEnd_7868842 := by exact prefixLift 7868842
  have htrace : WordTrace (prefixWord ++ tailWord_7868842) baseStart_7868842 baseEnd_7868842 := by
    simpa [prefixWord, tailWord_7868842, baseEnd_7868842] using wordTrace_append hprefix tailTrace_7868842
  have hstable : (prefixWord ++ tailWord_7868842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868842).length < 2 ^ (prefixWord ++ tailWord_7868842).sum := by decide
  have hdescent : baseEnd_7868842 < baseStart_7868842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868871 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_7868871 : Nat := 118140960795 + 7868871 * 2 ^ 59
def prefixEnd_7868871 : Nat := 4983230072969 + 3 ^ 40 * 7868871 * 2
def baseEnd_7868871 : Nat := 4040513031225387739724227

theorem tailTrace_7868871 : CollatzResearch.WordTrace tailWord_7868871 prefixEnd_7868871 4040513031225387739724227 := by
  unfold tailWord_7868871
  simp only [CollatzResearch.WordTrace]
  refine ⟨287001303475431738018870467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191334202316954492012580311 287001303475431738018870467)
  ·
    refine ⟨430501955213147607028305701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287001303475431738018870467 430501955213147607028305701)
    ·
      refine ⟨80719116602465176317807319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430501955213147607028305701 80719116602465176317807319)
      ·
        refine ⟨121078674903697764476710979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80719116602465176317807319 121078674903697764476710979)
        ·
          refine ⟨181618012355546646715066469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121078674903697764476710979 181618012355546646715066469)
          ·
            refine ⟨34053377316664996259074963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181618012355546646715066469 34053377316664996259074963)
            ·
              refine ⟨51080065974997494388612445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34053377316664996259074963 51080065974997494388612445)
              ·
                refine ⟨19155024740624060395729667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51080065974997494388612445 19155024740624060395729667)
                ·
                  refine ⟨28732537110936090593594501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19155024740624060395729667 28732537110936090593594501)
                  ·
                    refine ⟨5387350708300516986298969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28732537110936090593594501 5387350708300516986298969)
                    ·
                      refine ⟨4040513031225387739724227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387350708300516986298969 4040513031225387739724227)
                      ·
                        rfl

theorem cell23_7868871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_7868871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868871 prefixEnd_7868871 := by exact prefixLift 7868871
  have htrace : WordTrace (prefixWord ++ tailWord_7868871) baseStart_7868871 baseEnd_7868871 := by
    simpa [prefixWord, tailWord_7868871, baseEnd_7868871] using wordTrace_append hprefix tailTrace_7868871
  have hstable : (prefixWord ++ tailWord_7868871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868871).length < 2 ^ (prefixWord ++ tailWord_7868871).sum := by decide
  have hdescent : baseEnd_7868871 < baseStart_7868871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868874 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_7868874 : Nat := 118140960795 + 7868874 * 2 ^ 59
def prefixEnd_7868874 : Nat := 4983230072969 + 3 ^ 40 * 7868874 * 2
def baseEnd_7868874 : Nat := 4040514571667351227986713

theorem tailTrace_7868874 : CollatzResearch.WordTrace tailWord_7868874 prefixEnd_7868874 4040514571667351227986713 := by
  unfold tailWord_7868874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71750353223605217382807419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191334275262947246354153117 71750353223605217382807419)
  ·
    refine ⟨107625529835407826074211129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71750353223605217382807419 107625529835407826074211129)
    ·
      refine ⟨80719147376555869555658347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107625529835407826074211129 80719147376555869555658347)
      ·
        refine ⟨121078721064833804333487521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80719147376555869555658347 121078721064833804333487521)
        ·
          refine ⟨90809040798625353250115641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121078721064833804333487521 90809040798625353250115641)
          ·
            refine ⟨68106780598969014937586731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90809040798625353250115641 68106780598969014937586731)
            ·
              refine ⟨102160170898453522406380097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68106780598969014937586731 102160170898453522406380097)
              ·
                refine ⟨76620128173840141804785073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102160170898453522406380097 76620128173840141804785073)
                ·
                  refine ⟨57465096130380106353588805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76620128173840141804785073 57465096130380106353588805)
                  ·
                    refine ⟨10774705524446269941297901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57465096130380106353588805 10774705524446269941297901)
                    ·
                      refine ⟨4040514571667351227986713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10774705524446269941297901 4040514571667351227986713)
                      ·
                        rfl

theorem cell23_7868874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_7868874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868874 prefixEnd_7868874 := by exact prefixLift 7868874
  have htrace : WordTrace (prefixWord ++ tailWord_7868874) baseStart_7868874 baseEnd_7868874 := by
    simpa [prefixWord, tailWord_7868874, baseEnd_7868874] using wordTrace_append hprefix tailTrace_7868874
  have hstable : (prefixWord ++ tailWord_7868874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868874).length < 2 ^ (prefixWord ++ tailWord_7868874).sum := by decide
  have hdescent : baseEnd_7868874 < baseStart_7868874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868887 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_7868887 : Nat := 118140960795 + 7868887 * 2 ^ 59
def prefixEnd_7868887 : Nat := 4983230072969 + 3 ^ 40 * 7868887 * 2
def baseEnd_7868887 : Nat := 4040521246915859677124153

theorem tailTrace_7868887 : CollatzResearch.WordTrace tailWord_7868887 prefixEnd_7868887 4040521246915859677124153 := by
  unfold tailWord_7868887
  simp only [CollatzResearch.WordTrace]
  refine ⟨287001887043373772751452915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191334591362249181834301943 287001887043373772751452915)
  ·
    refine ⟨430502830565060659127179373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287001887043373772751452915 430502830565060659127179373)
    ·
      refine ⟨161438561461897747172692265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430502830565060659127179373 161438561461897747172692265)
      ·
        refine ⟨121078921096423310379519199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161438561461897747172692265 121078921096423310379519199)
        ·
          refine ⟨181618381644634965569278799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121078921096423310379519199 181618381644634965569278799)
          ·
            refine ⟨272427572466952448353918199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181618381644634965569278799 272427572466952448353918199)
            ·
              refine ⟨408641358700428672530877299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272427572466952448353918199 408641358700428672530877299)
              ·
                refine ⟨612962038050643008796315949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408641358700428672530877299 612962038050643008796315949)
                ·
                  refine ⟨229860764268991128298618481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612962038050643008796315949 229860764268991128298618481)
                  ·
                    refine ⟨172395573201743346223963861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229860764268991128298618481 172395573201743346223963861)
                    ·
                      refine ⟨4040521246915859677124153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172395573201743346223963861 4040521246915859677124153)
                      ·
                        rfl

theorem cell23_7868887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_7868887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868887 prefixEnd_7868887 := by exact prefixLift 7868887
  have htrace : WordTrace (prefixWord ++ tailWord_7868887) baseStart_7868887 baseEnd_7868887 := by
    simpa [prefixWord, tailWord_7868887, baseEnd_7868887] using wordTrace_append hprefix tailTrace_7868887
  have hstable : (prefixWord ++ tailWord_7868887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868887).length < 2 ^ (prefixWord ++ tailWord_7868887).sum := by decide
  have hdescent : baseEnd_7868887 < baseStart_7868887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868961 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7868961 : Nat := 118140960795 + 7868961 * 2 ^ 59
def prefixEnd_7868961 : Nat := 4983230072969 + 3 ^ 40 * 7868961 * 2
def baseEnd_7868961 : Nat := 4040559244484292387598813

theorem tailTrace_7868961 : CollatzResearch.WordTrace tailWord_7868961 prefixEnd_7868961 4040559244484292387598813 := by
  unfold tailWord_7868961
  simp only [CollatzResearch.WordTrace]
  refine ⟨287004586045105683389646737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191336390696737122259764491 287004586045105683389646737)
  ·
    refine ⟨215253439533829262542235053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287004586045105683389646737 215253439533829262542235053)
    ·
      refine ⟨80720039825185973453338145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215253439533829262542235053 80720039825185973453338145)
      ·
        refine ⟨60540029868889480090003609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80720039825185973453338145 60540029868889480090003609)
        ·
          refine ⟨45405022401667110067502707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60540029868889480090003609 45405022401667110067502707)
          ·
            refine ⟨68107533602500665101254061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45405022401667110067502707 68107533602500665101254061)
            ·
              refine ⟨25540325100937749412970273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68107533602500665101254061 25540325100937749412970273)
              ·
                refine ⟨19155243825703312059727705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25540325100937749412970273 19155243825703312059727705)
                ·
                  refine ⟨14366432869277484044795779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19155243825703312059727705 14366432869277484044795779)
                  ·
                    refine ⟨21549649303916226067193669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14366432869277484044795779 21549649303916226067193669)
                    ·
                      refine ⟨4040559244484292387598813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21549649303916226067193669 4040559244484292387598813)
                      ·
                        rfl

theorem cell23_7868961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7868961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868961 prefixEnd_7868961 := by exact prefixLift 7868961
  have htrace : WordTrace (prefixWord ++ tailWord_7868961) baseStart_7868961 baseEnd_7868961 := by
    simpa [prefixWord, tailWord_7868961, baseEnd_7868961] using wordTrace_append hprefix tailTrace_7868961
  have hstable : (prefixWord ++ tailWord_7868961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868961).length < 2 ^ (prefixWord ++ tailWord_7868961).sum := by decide
  have hdescent : baseEnd_7868961 < baseStart_7868961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868973 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7868973 : Nat := 118140960795 + 7868973 * 2 ^ 59
def prefixEnd_7868973 : Nat := 4983230072969 + 3 ^ 40 * 7868973 * 2
def baseEnd_7868973 : Nat := 4040565406252146340648759

theorem tailTrace_7868973 : CollatzResearch.WordTrace tailWord_7868973 prefixEnd_7868973 4040565406252146340648759 := by
  unfold tailWord_7868973
  simp only [CollatzResearch.WordTrace]
  refine ⟨287005023721062209439083573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191336682480708139626055715 287005023721062209439083573)
  ·
    refine ⟨26906720973849582134914085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287005023721062209439083573 26906720973849582134914085)
    ·
      refine ⟨5045010182596796650296391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26906720973849582134914085 5045010182596796650296391)
      ·
        refine ⟨7567515273895194975444587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5045010182596796650296391 7567515273895194975444587)
        ·
          refine ⟨11351272910842792463166881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7567515273895194975444587 11351272910842792463166881)
          ·
            refine ⟨8513454683132094347375161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11351272910842792463166881 8513454683132094347375161)
            ·
              refine ⟨6385091012349070760531371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8513454683132094347375161 6385091012349070760531371)
              ·
                refine ⟨9577636518523606140797057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385091012349070760531371 9577636518523606140797057)
                ·
                  refine ⟨7183227388892704605597793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9577636518523606140797057 7183227388892704605597793)
                  ·
                    refine ⟨5387420541669528454198345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183227388892704605597793 5387420541669528454198345)
                    ·
                      refine ⟨4040565406252146340648759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387420541669528454198345 4040565406252146340648759)
                      ·
                        rfl

theorem cell23_7868973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7868973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868973 prefixEnd_7868973 := by exact prefixLift 7868973
  have htrace : WordTrace (prefixWord ++ tailWord_7868973) baseStart_7868973 baseEnd_7868973 := by
    simpa [prefixWord, tailWord_7868973, baseEnd_7868973] using wordTrace_append hprefix tailTrace_7868973
  have hstable : (prefixWord ++ tailWord_7868973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868973).length < 2 ^ (prefixWord ++ tailWord_7868973).sum := by decide
  have hdescent : baseEnd_7868973 < baseStart_7868973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7868981 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_7868981 : Nat := 118140960795 + 7868981 * 2 ^ 59
def prefixEnd_7868981 : Nat := 4983230072969 + 3 ^ 40 * 7868981 * 2
def baseEnd_7868981 : Nat := 4040569514097382309348721

theorem tailTrace_7868981 : CollatzResearch.WordTrace tailWord_7868981 prefixEnd_7868981 4040569514097382309348721 := by
  unfold tailWord_7868981
  simp only [CollatzResearch.WordTrace]
  refine ⟨287005315505033226805374797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191336877003355484536916531 287005315505033226805374797)
  ·
    refine ⟨107626993314387460052015549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287005315505033226805374797 107626993314387460052015549)
    ·
      refine ⟨40360122492895297519505831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107626993314387460052015549 40360122492895297519505831)
      ·
        refine ⟨60540183739342946279258747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40360122492895297519505831 60540183739342946279258747)
        ·
          refine ⟨90810275609014419418888121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60540183739342946279258747 90810275609014419418888121)
          ·
            refine ⟨68107706706760814564166091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90810275609014419418888121 68107706706760814564166091)
            ·
              refine ⟨102161560060141221846249137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68107706706760814564166091 102161560060141221846249137)
              ·
                refine ⟨76621170045105916384686853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102161560060141221846249137 76621170045105916384686853)
                ·
                  refine ⟨14366469383457359322128785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76621170045105916384686853 14366469383457359322128785)
                  ·
                    refine ⟨10774852037593019491596589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14366469383457359322128785 10774852037593019491596589)
                    ·
                      refine ⟨4040569514097382309348721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10774852037593019491596589 4040569514097382309348721)
                      ·
                        rfl

theorem cell23_7868981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_7868981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7868981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7868981 prefixEnd_7868981 := by exact prefixLift 7868981
  have htrace : WordTrace (prefixWord ++ tailWord_7868981) baseStart_7868981 baseEnd_7868981 := by
    simpa [prefixWord, tailWord_7868981, baseEnd_7868981] using wordTrace_append hprefix tailTrace_7868981
  have hstable : (prefixWord ++ tailWord_7868981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7868981).length < 2 ^ (prefixWord ++ tailWord_7868981).sum := by decide
  have hdescent : baseEnd_7868981 < baseStart_7868981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7868981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869028 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_7869028 : Nat := 118140960795 + 7869028 * 2 ^ 59
def prefixEnd_7869028 : Nat := 4983230072969 + 3 ^ 40 * 7869028 * 2
def baseEnd_7869028 : Nat := 4040593647688143625461005

theorem tailTrace_7869028 : CollatzResearch.WordTrace tailWord_7869028 prefixEnd_7869028 4040593647688143625461005 := by
  unfold tailWord_7869028
  simp only [CollatzResearch.WordTrace]
  refine ⟨143503514867931476916167869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191338019823908635888223825 143503514867931476916167869)
  ·
    refine ⟨53813818075474303843562951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143503514867931476916167869 53813818075474303843562951)
    ·
      refine ⟨80720727113211455765344427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53813818075474303843562951 80720727113211455765344427)
      ·
        refine ⟨121081090669817183648016641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80720727113211455765344427 121081090669817183648016641)
        ·
          refine ⟨90810818002362887736012481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121081090669817183648016641 90810818002362887736012481)
          ·
            refine ⟨68108113501772165802009361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90810818002362887736012481 68108113501772165802009361)
            ·
              refine ⟨51081085126329124351507021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68108113501772165802009361 51081085126329124351507021)
              ·
                refine ⟨19155406922373421631815133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51081085126329124351507021 19155406922373421631815133)
                ·
                  refine ⟨7183277595890033111930675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19155406922373421631815133 7183277595890033111930675)
                  ·
                    refine ⟨10774916393835049667896013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7183277595890033111930675 10774916393835049667896013)
                    ·
                      refine ⟨4040593647688143625461005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10774916393835049667896013 4040593647688143625461005)
                      ·
                        rfl

theorem cell23_7869028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_7869028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869028 prefixEnd_7869028 := by exact prefixLift 7869028
  have htrace : WordTrace (prefixWord ++ tailWord_7869028) baseStart_7869028 baseEnd_7869028 := by
    simpa [prefixWord, tailWord_7869028, baseEnd_7869028] using wordTrace_append hprefix tailTrace_7869028
  have hstable : (prefixWord ++ tailWord_7869028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869028).length < 2 ^ (prefixWord ++ tailWord_7869028).sum := by decide
  have hdescent : baseEnd_7869028 < baseStart_7869028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869051 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 8, 2]
def baseStart_7869051 : Nat := 118140960795 + 7869051 * 2 ^ 59
def prefixEnd_7869051 : Nat := 4983230072969 + 3 ^ 40 * 7869051 * 2
def baseEnd_7869051 : Nat := 4040605457743197035473399

theorem tailTrace_7869051 : CollatzResearch.WordTrace tailWord_7869051 prefixEnd_7869051 4040605457743197035473399 := by
  unfold tailWord_7869051
  simp only [CollatzResearch.WordTrace]
  refine ⟨287007868614779628760423007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191338579076519752506948671 287007868614779628760423007)
  ·
    refine ⟨430511802922169443140634511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287007868614779628760423007 430511802922169443140634511)
    ·
      refine ⟨645767704383254164710951767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430511802922169443140634511 645767704383254164710951767)
      ·
        refine ⟨968651556574881247066427651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645767704383254164710951767 968651556574881247066427651)
        ·
          refine ⟨1452977334862321870599641477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968651556574881247066427651 1452977334862321870599641477)
          ·
            refine ⟨272433250286685350737432777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1452977334862321870599641477 272433250286685350737432777)
            ·
              refine ⟨204324937715014013053074583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272433250286685350737432777 204324937715014013053074583)
              ·
                refine ⟨306487406572521019579611875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204324937715014013053074583 306487406572521019579611875)
                ·
                  refine ⟨459731109858781529369417813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306487406572521019579611875 459731109858781529369417813)
                  ·
                    refine ⟨5387473943657596047297865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 459731109858781529369417813 5387473943657596047297865)
                    ·
                      refine ⟨4040605457743197035473399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387473943657596047297865 4040605457743197035473399)
                      ·
                        rfl

theorem cell23_7869051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8, 2].length) (baseStart_7869051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869051 prefixEnd_7869051 := by exact prefixLift 7869051
  have htrace : WordTrace (prefixWord ++ tailWord_7869051) baseStart_7869051 baseEnd_7869051 := by
    simpa [prefixWord, tailWord_7869051, baseEnd_7869051] using wordTrace_append hprefix tailTrace_7869051
  have hstable : (prefixWord ++ tailWord_7869051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869051).length < 2 ^ (prefixWord ++ tailWord_7869051).sum := by decide
  have hdescent : baseEnd_7869051 < baseStart_7869051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869061 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_7869061 : Nat := 118140960795 + 7869061 * 2 ^ 59
def prefixEnd_7869061 : Nat := 4983230072969 + 3 ^ 40 * 7869061 * 2
def baseEnd_7869061 : Nat := 1346870197516580665449451

theorem tailTrace_7869061 : CollatzResearch.WordTrace tailWord_7869061 prefixEnd_7869061 1346870197516580665449451 := by
  unfold tailWord_7869061
  simp only [CollatzResearch.WordTrace]
  refine ⟨287008233344743400468287037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191338822229828933645524691 287008233344743400468287037)
  ·
    refine ⟨107628087504278775175607639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287008233344743400468287037 107628087504278775175607639)
    ·
      refine ⟨161442131256418162763411459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107628087504278775175607639 161442131256418162763411459)
      ·
        refine ⟨242163196884627244145117189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161442131256418162763411459 242163196884627244145117189)
        ·
          refine ⟨45405599415867608277209473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242163196884627244145117189 45405599415867608277209473)
          ·
            refine ⟨34054199561900706207907105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45405599415867608277209473 34054199561900706207907105)
            ·
              refine ⟨25540649671425529655930329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34054199561900706207907105 25540649671425529655930329)
              ·
                refine ⟨19155487253569147241947747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25540649671425529655930329 19155487253569147241947747)
                ·
                  refine ⟨28733230880353720862921621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19155487253569147241947747 28733230880353720862921621)
                  ·
                    refine ⟨1346870197516580665449451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28733230880353720862921621 1346870197516580665449451)
                    ·
                      rfl

theorem cell23_7869061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_7869061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869061 prefixEnd_7869061 := by exact prefixLift 7869061
  have htrace : WordTrace (prefixWord ++ tailWord_7869061) baseStart_7869061 baseEnd_7869061 := by
    simpa [prefixWord, tailWord_7869061, baseEnd_7869061] using wordTrace_append hprefix tailTrace_7869061
  have hstable : (prefixWord ++ tailWord_7869061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869061).length < 2 ^ (prefixWord ++ tailWord_7869061).sum := by decide
  have hdescent : baseEnd_7869061 < baseStart_7869061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869085 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_7869085 : Nat := 118140960795 + 7869085 * 2 ^ 59
def prefixEnd_7869085 : Nat := 4983230072969 + 3 ^ 40 * 7869085 * 2
def baseEnd_7869085 : Nat := 4040622916085449902448243

theorem tailTrace_7869085 : CollatzResearch.WordTrace tailWord_7869085 prefixEnd_7869085 4040622916085449902448243 := by
  unfold tailWord_7869085
  simp only [CollatzResearch.WordTrace]
  refine ⟨287009108696656452567160709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191339405797770968378107139 287009108696656452567160709)
  ·
    refine ⟨53814207880623084856342633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287009108696656452567160709 53814207880623084856342633)
    ·
      refine ⟨40360655910467313642256975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53814207880623084856342633 40360655910467313642256975)
      ·
        refine ⟨60540983865700970463385463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40360655910467313642256975 60540983865700970463385463)
        ·
          refine ⟨90811475798551455695078195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60540983865700970463385463 90811475798551455695078195)
          ·
            refine ⟨136217213697827183542617293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90811475798551455695078195 136217213697827183542617293)
            ·
              refine ⟨51081455136685193828481485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136217213697827183542617293 51081455136685193828481485)
              ·
                refine ⟨19155545676256947685680557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51081455136685193828481485 19155545676256947685680557)
                ·
                  refine ⟨7183329628596355382130209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19155545676256947685680557 7183329628596355382130209)
                  ·
                    refine ⟨5387497221447266536597657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183329628596355382130209 5387497221447266536597657)
                    ·
                      refine ⟨4040622916085449902448243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387497221447266536597657 4040622916085449902448243)
                      ·
                        rfl

theorem cell23_7869085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_7869085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869085 prefixEnd_7869085 := by exact prefixLift 7869085
  have htrace : WordTrace (prefixWord ++ tailWord_7869085) baseStart_7869085 baseEnd_7869085 := by
    simpa [prefixWord, tailWord_7869085, baseEnd_7869085] using wordTrace_append hprefix tailTrace_7869085
  have hstable : (prefixWord ++ tailWord_7869085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869085).length < 2 ^ (prefixWord ++ tailWord_7869085).sum := by decide
  have hdescent : baseEnd_7869085 < baseStart_7869085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869088 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5]
def baseStart_7869088 : Nat := 118140960795 + 7869088 * 2 ^ 59
def prefixEnd_7869088 : Nat := 4983230072969 + 3 ^ 40 * 7869088 * 2
def baseEnd_7869088 : Nat := 4040624456527413390710729

theorem tailTrace_7869088 : CollatzResearch.WordTrace tailWord_7869088 prefixEnd_7869088 4040624456527413390710729 := by
  unfold tailWord_7869088
  simp only [CollatzResearch.WordTrace]
  refine ⟨143504609057822792039759959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191339478743763722719679945 143504609057822792039759959)
  ·
    refine ⟨215256913586734188059639939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143504609057822792039759959 215256913586734188059639939)
    ·
      refine ⟨322885370380101282089459909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215256913586734188059639939 322885370380101282089459909)
      ·
        refine ⟨60541006946268990391773733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322885370380101282089459909 60541006946268990391773733)
        ·
          refine ⟨11351438802425435698457575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60541006946268990391773733 11351438802425435698457575)
          ·
            refine ⟨17027158203638153547686363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11351438802425435698457575 17027158203638153547686363)
            ·
              refine ⟨25540737305457230321529545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17027158203638153547686363 25540737305457230321529545)
              ·
                refine ⟨19155552979092922741147159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25540737305457230321529545 19155552979092922741147159)
                ·
                  refine ⟨28733329468639384111720739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19155552979092922741147159 28733329468639384111720739)
                  ·
                    refine ⟨43099994202959076167581109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28733329468639384111720739 43099994202959076167581109)
                    ·
                      refine ⟨4040624456527413390710729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43099994202959076167581109 4040624456527413390710729)
                      ·
                        rfl

theorem cell23_7869088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_7869088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869088 prefixEnd_7869088 := by exact prefixLift 7869088
  have htrace : WordTrace (prefixWord ++ tailWord_7869088) baseStart_7869088 baseEnd_7869088 := by
    simpa [prefixWord, tailWord_7869088, baseEnd_7869088] using wordTrace_append hprefix tailTrace_7869088
  have hstable : (prefixWord ++ tailWord_7869088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869088).length < 2 ^ (prefixWord ++ tailWord_7869088).sum := by decide
  have hdescent : baseEnd_7869088 < baseStart_7869088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869102 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7869102 : Nat := 118140960795 + 7869102 * 2 ^ 59
def prefixEnd_7869102 : Nat := 4983230072969 + 3 ^ 40 * 7869102 * 2
def baseEnd_7869102 : Nat := 4040631645256576335935665

theorem tailTrace_7869102 : CollatzResearch.WordTrace tailWord_7869102 prefixEnd_7869102 4040631645256576335935665 := by
  unfold tailWord_7869102
  simp only [CollatzResearch.WordTrace]
  refine ⟨35876216092199358058816195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191339819158396576313686373 35876216092199358058816195)
  ·
    refine ⟨53814324138299037088224293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35876216092199358058816195 53814324138299037088224293)
    ·
      refine ⟨10090185775931069454042055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53814324138299037088224293 10090185775931069454042055)
      ·
        refine ⟨15135278663896604181063083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10090185775931069454042055 15135278663896604181063083)
        ·
          refine ⟨22702917995844906271594625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15135278663896604181063083 22702917995844906271594625)
          ·
            refine ⟨17027188496883679703695969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22702917995844906271594625 17027188496883679703695969)
            ·
              refine ⟨12770391372662759777771977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17027188496883679703695969 12770391372662759777771977)
              ·
                refine ⟨9577793529497069833328983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12770391372662759777771977 9577793529497069833328983)
                ·
                  refine ⟨14366690294245604749993475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9577793529497069833328983 14366690294245604749993475)
                  ·
                    refine ⟨21550035441368407124990213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14366690294245604749993475 21550035441368407124990213)
                    ·
                      refine ⟨4040631645256576335935665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21550035441368407124990213 4040631645256576335935665)
                      ·
                        rfl

theorem cell23_7869102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7869102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869102 prefixEnd_7869102 := by exact prefixLift 7869102
  have htrace : WordTrace (prefixWord ++ tailWord_7869102) baseStart_7869102 baseEnd_7869102 := by
    simpa [prefixWord, tailWord_7869102, baseEnd_7869102] using wordTrace_append hprefix tailTrace_7869102
  have hstable : (prefixWord ++ tailWord_7869102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869102).length < 2 ^ (prefixWord ++ tailWord_7869102).sum := by decide
  have hdescent : baseEnd_7869102 < baseStart_7869102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869118 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_7869118 : Nat := 118140960795 + 7869118 * 2 ^ 59
def prefixEnd_7869118 : Nat := 4983230072969 + 3 ^ 40 * 7869118 * 2
def baseEnd_7869118 : Nat := 4040639860947048273335591

theorem tailTrace_7869118 : CollatzResearch.WordTrace tailWord_7869118 prefixEnd_7869118 4040639860947048273335591 := by
  unfold tailWord_7869118
  simp only [CollatzResearch.WordTrace]
  refine ⟨35876289038192112400389001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191340208203691266135408005 35876289038192112400389001)
  ·
    refine ⟨26907216778644084300291751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35876289038192112400389001 26907216778644084300291751)
    ·
      refine ⟨40360825167966126450437627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26907216778644084300291751 40360825167966126450437627)
      ·
        refine ⟨60541237751949189675656441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40360825167966126450437627 60541237751949189675656441)
        ·
          refine ⟨45405928313961892256742331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60541237751949189675656441 45405928313961892256742331)
          ·
            refine ⟨68108892470942838385113497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45405928313961892256742331 68108892470942838385113497)
            ·
              refine ⟨51081669353207128788835123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68108892470942838385113497 51081669353207128788835123)
              ·
                refine ⟨76622504029810693183252685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51081669353207128788835123 76622504029810693183252685)
                ·
                  refine ⟨28733439011179009943719757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76622504029810693183252685 28733439011179009943719757)
                  ·
                    refine ⟨10775039629192128728894909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28733439011179009943719757 10775039629192128728894909)
                    ·
                      refine ⟨4040639860947048273335591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10775039629192128728894909 4040639860947048273335591)
                      ·
                        rfl

theorem cell23_7869118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_7869118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869118 prefixEnd_7869118 := by exact prefixLift 7869118
  have htrace : WordTrace (prefixWord ++ tailWord_7869118) baseStart_7869118 baseEnd_7869118 := by
    simpa [prefixWord, tailWord_7869118, baseEnd_7869118] using wordTrace_append hprefix tailTrace_7869118
  have hstable : (prefixWord ++ tailWord_7869118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869118).length < 2 ^ (prefixWord ++ tailWord_7869118).sum := by decide
  have hdescent : baseEnd_7869118 < baseStart_7869118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869119 : List Nat := [1, 1, 2, 2, 2, 6, 1, 3, 1, 2, 2]
def baseStart_7869119 : Nat := 118140960795 + 7869119 * 2 ^ 59
def prefixEnd_7869119 : Nat := 4983230072969 + 3 ^ 40 * 7869119 * 2
def baseEnd_7869119 : Nat := 4040640374427702769423087

theorem tailTrace_7869119 : CollatzResearch.WordTrace tailWord_7869119 prefixEnd_7869119 4040640374427702769423087 := by
  unfold tailWord_7869119
  simp only [CollatzResearch.WordTrace]
  refine ⟨287010348778533276373898411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191340232519022184249265607 287010348778533276373898411)
  ·
    refine ⟨430515523167799914560847617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287010348778533276373898411 430515523167799914560847617)
    ·
      refine ⟨322886642375849935920635713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430515523167799914560847617 322886642375849935920635713)
      ·
        refine ⟨242164981781887451940476785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322886642375849935920635713 242164981781887451940476785)
        ·
          refine ⟨181623736336415588955357589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242164981781887451940476785 181623736336415588955357589)
          ·
            refine ⟨8513612640769480732282387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181623736336415588955357589 8513612640769480732282387)
            ·
              refine ⟨12770418961154221098423581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513612640769480732282387 12770418961154221098423581)
              ·
                refine ⟨4788907110432832911908843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12770418961154221098423581 4788907110432832911908843)
                ·
                  refine ⟨7183360665649249367863265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788907110432832911908843 7183360665649249367863265)
                  ·
                    refine ⟨5387520499236937025897449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183360665649249367863265 5387520499236937025897449)
                    ·
                      refine ⟨4040640374427702769423087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387520499236937025897449 4040640374427702769423087)
                      ·
                        rfl

theorem cell23_7869119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_7869119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869119 prefixEnd_7869119 := by exact prefixLift 7869119
  have htrace : WordTrace (prefixWord ++ tailWord_7869119) baseStart_7869119 baseEnd_7869119 := by
    simpa [prefixWord, tailWord_7869119, baseEnd_7869119] using wordTrace_append hprefix tailTrace_7869119
  have hstable : (prefixWord ++ tailWord_7869119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869119).length < 2 ^ (prefixWord ++ tailWord_7869119).sum := by decide
  have hdescent : baseEnd_7869119 < baseStart_7869119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869161 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_7869161 : Nat := 118140960795 + 7869161 * 2 ^ 59
def prefixEnd_7869161 : Nat := 4983230072969 + 3 ^ 40 * 7869161 * 2
def baseEnd_7869161 : Nat := 4040661940615191605097893

theorem tailTrace_7869161 : CollatzResearch.WordTrace tailWord_7869161 prefixEnd_7869161 4040661940615191605097893 := by
  unfold tailWord_7869161
  simp only [CollatzResearch.WordTrace]
  refine ⟨287011880644381117546927337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191341253762920745031284891 287011880644381117546927337)
  ·
    refine ⟨215258910483285838160195503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287011880644381117546927337 215258910483285838160195503)
    ·
      refine ⟨322888365724928757240293255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215258910483285838160195503 322888365724928757240293255)
      ·
        refine ⟨484332548587393135860439883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322888365724928757240293255 484332548587393135860439883)
        ·
          refine ⟨726498822881089703790659825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484332548587393135860439883 726498822881089703790659825)
          ·
            refine ⟨544874117160817277842994869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726498822881089703790659825 544874117160817277842994869)
            ·
              refine ⟨51081948483826619797780769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 544874117160817277842994869 51081948483826619797780769)
              ·
                refine ⟨38311461362869964848335577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51081948483826619797780769 38311461362869964848335577)
                ·
                  refine ⟨28733596022152473636251683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38311461362869964848335577 28733596022152473636251683)
                  ·
                    refine ⟨43100394033228710454377525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28733596022152473636251683 43100394033228710454377525)
                    ·
                      refine ⟨4040661940615191605097893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43100394033228710454377525 4040661940615191605097893)
                      ·
                        rfl

theorem cell23_7869161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_7869161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869161 prefixEnd_7869161 := by exact prefixLift 7869161
  have htrace : WordTrace (prefixWord ++ tailWord_7869161) baseStart_7869161 baseEnd_7869161 := by
    simpa [prefixWord, tailWord_7869161, baseEnd_7869161] using wordTrace_append hprefix tailTrace_7869161
  have hstable : (prefixWord ++ tailWord_7869161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869161).length < 2 ^ (prefixWord ++ tailWord_7869161).sum := by decide
  have hdescent : baseEnd_7869161 < baseStart_7869161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869171 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4]
def baseStart_7869171 : Nat := 118140960795 + 7869171 * 2 ^ 59
def prefixEnd_7869171 : Nat := 4983230072969 + 3 ^ 40 * 7869171 * 2
def baseEnd_7869171 : Nat := 4040667075421736565972847

theorem tailTrace_7869171 : CollatzResearch.WordTrace tailWord_7869171 prefixEnd_7869171 4040667075421736565972847 := by
  unfold tailWord_7869171
  simp only [CollatzResearch.WordTrace]
  refine ⟨287012245374344889254791367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191341496916229926169860911 287012245374344889254791367)
  ·
    refine ⟨430518368061517333882187051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287012245374344889254791367 430518368061517333882187051)
    ·
      refine ⟨645777552092276000823280577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430518368061517333882187051 645777552092276000823280577)
      ·
        refine ⟨484333164069207000617460433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645777552092276000823280577 484333164069207000617460433)
        ·
          refine ⟨363249873051905250463095325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484333164069207000617460433 363249873051905250463095325)
          ·
            refine ⟨136218702394464468923660747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363249873051905250463095325 136218702394464468923660747)
            ·
              refine ⟨204328053591696703385491121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136218702394464468923660747 204328053591696703385491121)
              ·
                refine ⟨153246040193772527539118341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204328053591696703385491121 153246040193772527539118341)
                ·
                  refine ⟨28733632536332348913584689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153246040193772527539118341 28733632536332348913584689)
                  ·
                    refine ⟨21550224402249261685188517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28733632536332348913584689 21550224402249261685188517)
                    ·
                      refine ⟨4040667075421736565972847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21550224402249261685188517 4040667075421736565972847)
                      ·
                        rfl

theorem cell23_7869171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_7869171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869171 prefixEnd_7869171 := by exact prefixLift 7869171
  have htrace : WordTrace (prefixWord ++ tailWord_7869171) baseStart_7869171 baseEnd_7869171 := by
    simpa [prefixWord, tailWord_7869171, baseEnd_7869171] using wordTrace_append hprefix tailTrace_7869171
  have hstable : (prefixWord ++ tailWord_7869171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869171).length < 2 ^ (prefixWord ++ tailWord_7869171).sum := by decide
  have hdescent : baseEnd_7869171 < baseStart_7869171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869188 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7869188 : Nat := 118140960795 + 7869188 * 2 ^ 59
def prefixEnd_7869188 : Nat := 4983230072969 + 3 ^ 40 * 7869188 * 2
def baseEnd_7869188 : Nat := 4040675804592862999460269

theorem tailTrace_7869188 : CollatzResearch.WordTrace tailWord_7869188 prefixEnd_7869188 4040675804592862999460269 := by
  unfold tailWord_7869188
  simp only [CollatzResearch.WordTrace]
  refine ⟨143506432707641650579080109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191341910276855534105440145 143506432707641650579080109)
  ·
    refine ⟨53814912265365618967155041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143506432707641650579080109 53814912265365618967155041)
    ·
      refine ⟨40361184199024214225366281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53814912265365618967155041 40361184199024214225366281)
      ·
        refine ⟨30270888149268160669024711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40361184199024214225366281 30270888149268160669024711)
        ·
          refine ⟨45406332223902241003537067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30270888149268160669024711 45406332223902241003537067)
          ·
            refine ⟨68109498335853361505305601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45406332223902241003537067 68109498335853361505305601)
            ·
              refine ⟨51082123751890021128979201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68109498335853361505305601 51082123751890021128979201)
              ·
                refine ⟨38311592813917515846734401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51082123751890021128979201 38311592813917515846734401)
                ·
                  refine ⟨28733694610438136885050801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38311592813917515846734401 28733694610438136885050801)
                  ·
                    refine ⟨21550270957828602663788101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28733694610438136885050801 21550270957828602663788101)
                    ·
                      refine ⟨4040675804592862999460269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21550270957828602663788101 4040675804592862999460269)
                      ·
                        rfl

theorem cell23_7869188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7869188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869188 prefixEnd_7869188 := by exact prefixLift 7869188
  have htrace : WordTrace (prefixWord ++ tailWord_7869188) baseStart_7869188 baseEnd_7869188 := by
    simpa [prefixWord, tailWord_7869188, baseEnd_7869188] using wordTrace_append hprefix tailTrace_7869188
  have hstable : (prefixWord ++ tailWord_7869188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869188).length < 2 ^ (prefixWord ++ tailWord_7869188).sum := by decide
  have hdescent : baseEnd_7869188 < baseStart_7869188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869192 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_7869192 : Nat := 118140960795 + 7869192 * 2 ^ 59
def prefixEnd_7869192 : Nat := 4983230072969 + 3 ^ 40 * 7869192 * 2
def baseEnd_7869192 : Nat := 4040677858515480983810251

theorem tailTrace_7869192 : CollatzResearch.WordTrace tailWord_7869192 prefixEnd_7869192 4040677858515480983810251 := by
  unfold tailWord_7869192
  simp only [CollatzResearch.WordTrace]
  refine ⟨143506505653634404920652915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191342007538179206560870553 143506505653634404920652915)
  ·
    refine ⟨215259758480451607380979373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143506505653634404920652915 215259758480451607380979373)
    ·
      refine ⟨80722409430169352767867265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215259758480451607380979373 80722409430169352767867265)
      ·
        refine ⟨60541807072627014575900449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80722409430169352767867265 60541807072627014575900449)
        ·
          refine ⟨45406355304470260931925337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60541807072627014575900449 45406355304470260931925337)
          ·
            refine ⟨34054766478352695698944003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45406355304470260931925337 34054766478352695698944003)
            ·
              refine ⟨51082149717529043548416005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34054766478352695698944003 51082149717529043548416005)
              ·
                refine ⟨9577903072036695665328001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51082149717529043548416005 9577903072036695665328001)
                ·
                  refine ⟨7183427304027521748996001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9577903072036695665328001 7183427304027521748996001)
                  ·
                    refine ⟨5387570478020641311747001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183427304027521748996001 5387570478020641311747001)
                    ·
                      refine ⟨4040677858515480983810251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387570478020641311747001 4040677858515480983810251)
                      ·
                        rfl

theorem cell23_7869192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_7869192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869192 prefixEnd_7869192 := by exact prefixLift 7869192
  have htrace : WordTrace (prefixWord ++ tailWord_7869192) baseStart_7869192 baseEnd_7869192 := by
    simpa [prefixWord, tailWord_7869192, baseEnd_7869192] using wordTrace_append hprefix tailTrace_7869192
  have hstable : (prefixWord ++ tailWord_7869192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869192).length < 2 ^ (prefixWord ++ tailWord_7869192).sum := by decide
  have hdescent : baseEnd_7869192 < baseStart_7869192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869248 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_7869248 : Nat := 118140960795 + 7869248 * 2 ^ 59
def prefixEnd_7869248 : Nat := 4983230072969 + 3 ^ 40 * 7869248 * 2
def baseEnd_7869248 : Nat := 4040706613432132764709993

theorem tailTrace_7869248 : CollatzResearch.WordTrace tailWord_7869248 prefixEnd_7869248 4040706613432132764709993 := by
  unfold tailWord_7869248
  simp only [CollatzResearch.WordTrace]
  refine ⟨143507526897532965702672199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191343369196710620936896265 143507526897532965702672199)
  ·
    refine ⟨215261290346299448554008299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143507526897532965702672199 215261290346299448554008299)
    ·
      refine ⟨322891935519449172831012449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215261290346299448554008299 322891935519449172831012449)
      ·
        refine ⟨242168951639586879623259337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322891935519449172831012449 242168951639586879623259337)
        ·
          refine ⟨181626713729690159717444503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242168951639586879623259337 181626713729690159717444503)
          ·
            refine ⟨272440070594535239576166755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181626713729690159717444503 272440070594535239576166755)
            ·
              refine ⟨408660105891802859364250133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272440070594535239576166755 408660105891802859364250133)
              ·
                refine ⟨19155942463678259032699225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 408660105891802859364250133 19155942463678259032699225)
                ·
                  refine ⟨14366956847758694274524419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19155942463678259032699225 14366956847758694274524419)
                  ·
                    refine ⟨21550435271638041411786629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14366956847758694274524419 21550435271638041411786629)
                    ·
                      refine ⟨4040706613432132764709993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21550435271638041411786629 4040706613432132764709993)
                      ·
                        rfl

theorem cell23_7869248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_7869248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869248 prefixEnd_7869248 := by exact prefixLift 7869248
  have htrace : WordTrace (prefixWord ++ tailWord_7869248) baseStart_7869248 baseEnd_7869248 := by
    simpa [prefixWord, tailWord_7869248, baseEnd_7869248] using wordTrace_append hprefix tailTrace_7869248
  have hstable : (prefixWord ++ tailWord_7869248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869248).length < 2 ^ (prefixWord ++ tailWord_7869248).sum := by decide
  have hdescent : baseEnd_7869248 < baseStart_7869248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869288 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 8]
def baseStart_7869288 : Nat := 118140960795 + 7869288 * 2 ^ 59
def prefixEnd_7869288 : Nat := 4983230072969 + 3 ^ 40 * 7869288 * 2
def baseEnd_7869288 : Nat := 448969683628701400912201

theorem tailTrace_7869288 : CollatzResearch.WordTrace tailWord_7869288 prefixEnd_7869288 448969683628701400912201 := by
  unfold tailWord_7869288
  simp only [CollatzResearch.WordTrace]
  refine ⟨143508256357460509118400259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191344341809947345491200345 143508256357460509118400259)
  ·
    refine ⟨215262384536190763677600389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143508256357460509118400259 215262384536190763677600389)
    ·
      refine ⟨40361697100535768189550073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215262384536190763677600389 40361697100535768189550073)
      ·
        refine ⟨30271272825401826142162555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40361697100535768189550073 30271272825401826142162555)
        ·
          refine ⟨45406909238102739213243833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30271272825401826142162555 45406909238102739213243833)
          ·
            refine ⟨34055181928577054409932875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45406909238102739213243833 34055181928577054409932875)
            ·
              refine ⟨51082772892865581614899313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34055181928577054409932875 51082772892865581614899313)
              ·
                refine ⟨38312079669649186211174485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51082772892865581614899313 38312079669649186211174485)
                ·
                  refine ⟨448969683628701400912201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38312079669649186211174485 448969683628701400912201)
                  ·
                    rfl

theorem cell23_7869288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 8].length) (baseStart_7869288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869288 prefixEnd_7869288 := by exact prefixLift 7869288
  have htrace : WordTrace (prefixWord ++ tailWord_7869288) baseStart_7869288 baseEnd_7869288 := by
    simpa [prefixWord, tailWord_7869288, baseEnd_7869288] using wordTrace_append hprefix tailTrace_7869288
  have hstable : (prefixWord ++ tailWord_7869288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869288).length < 2 ^ (prefixWord ++ tailWord_7869288).sum := by decide
  have hdescent : baseEnd_7869288 < baseStart_7869288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869302 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7869302 : Nat := 118140960795 + 7869302 * 2 ^ 59
def prefixEnd_7869302 : Nat := 4983230072969 + 3 ^ 40 * 7869302 * 2
def baseEnd_7869302 : Nat := 4040734341387475553434745

theorem tailTrace_7869302 : CollatzResearch.WordTrace tailWord_7869302 prefixEnd_7869302 4040734341387475553434745 := by
  unfold tailWord_7869302
  simp only [CollatzResearch.WordTrace]
  refine ⟨17938563958554393664238135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191344682224580199085206773 17938563958554393664238135)
  ·
    refine ⟨26907845937831590496357203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17938563958554393664238135 26907845937831590496357203)
    ·
      refine ⟨40361768906747385744535805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26907845937831590496357203 40361768906747385744535805)
      ·
        refine ⟨15135663340030269654200927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40361768906747385744535805 15135663340030269654200927)
        ·
          refine ⟨22703495010045404481301391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15135663340030269654200927 22703495010045404481301391)
          ·
            refine ⟨34055242515068106721952087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22703495010045404481301391 34055242515068106721952087)
            ·
              refine ⟨51082863772602160082928131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34055242515068106721952087 51082863772602160082928131)
              ·
                refine ⟨76624295658903240124392197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51082863772602160082928131 76624295658903240124392197)
                ·
                  refine ⟨14367055436044357523323537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76624295658903240124392197 14367055436044357523323537)
                  ·
                    refine ⟨10775291577033268142492653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14367055436044357523323537 10775291577033268142492653)
                    ·
                      refine ⟨4040734341387475553434745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10775291577033268142492653 4040734341387475553434745)
                      ·
                        rfl

theorem cell23_7869302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7869302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869302 prefixEnd_7869302 := by exact prefixLift 7869302
  have htrace : WordTrace (prefixWord ++ tailWord_7869302) baseStart_7869302 baseEnd_7869302 := by
    simpa [prefixWord, tailWord_7869302, baseEnd_7869302] using wordTrace_append hprefix tailTrace_7869302
  have hstable : (prefixWord ++ tailWord_7869302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869302).length < 2 ^ (prefixWord ++ tailWord_7869302).sum := by decide
  have hdescent : baseEnd_7869302 < baseStart_7869302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869322 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 6]
def baseStart_7869322 : Nat := 118140960795 + 7869322 * 2 ^ 59
def prefixEnd_7869322 : Nat := 4983230072969 + 3 ^ 40 * 7869322 * 2
def baseEnd_7869322 : Nat := 448971623444507275020517

theorem tailTrace_7869322 : CollatzResearch.WordTrace tailWord_7869322 prefixEnd_7869322 448971623444507275020517 := by
  unfold tailWord_7869322
  simp only [CollatzResearch.WordTrace]
  refine ⟨71754438199199460510884555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191345168531198561362358813 71754438199199460510884555)
  ·
    refine ⟨107631657298799190766326833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71754438199199460510884555 107631657298799190766326833)
    ·
      refine ⟨80723742974099393074745125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107631657298799190766326833 80723742974099393074745125)
      ·
        refine ⟨15135701807643636201514711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80723742974099393074745125 15135701807643636201514711)
        ·
          refine ⟨22703552711465454302272067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15135701807643636201514711 22703552711465454302272067)
          ·
            refine ⟨34055329067198181453408101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22703552711465454302272067 34055329067198181453408101)
            ·
              refine ⟨6385374200099659022514019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34055329067198181453408101 6385374200099659022514019)
              ·
                refine ⟨9578061300149488533771029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385374200099659022514019 9578061300149488533771029)
                ·
                  refine ⟨448971623444507275020517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9578061300149488533771029 448971623444507275020517)
                  ·
                    rfl

theorem cell23_7869322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_7869322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869322 prefixEnd_7869322 := by exact prefixLift 7869322
  have htrace : WordTrace (prefixWord ++ tailWord_7869322) baseStart_7869322 baseEnd_7869322 := by
    simpa [prefixWord, tailWord_7869322, baseEnd_7869322] using wordTrace_append hprefix tailTrace_7869322
  have hstable : (prefixWord ++ tailWord_7869322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869322).length < 2 ^ (prefixWord ++ tailWord_7869322).sum := by decide
  have hdescent : baseEnd_7869322 < baseStart_7869322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869332 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_7869332 : Nat := 118140960795 + 7869332 * 2 ^ 59
def prefixEnd_7869332 : Nat := 4983230072969 + 3 ^ 40 * 7869332 * 2
def baseEnd_7869332 : Nat := 4040749745807110436059607

theorem tailTrace_7869332 : CollatzResearch.WordTrace tailWord_7869332 prefixEnd_7869332 4040749745807110436059607 := by
  unfold tailWord_7869332
  simp only [CollatzResearch.WordTrace]
  refine ⟨143509058763380806875701125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191345411684507742500934833 143509058763380806875701125)
  ·
    refine ⟨26907948518133901289193961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143509058763380806875701125 26907948518133901289193961)
    ·
      refine ⟨20180961388600425966895471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26907948518133901289193961 20180961388600425966895471)
      ·
        refine ⟨30271442082900638950343207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20180961388600425966895471 30271442082900638950343207)
        ·
          refine ⟨45407163124350958425514811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30271442082900638950343207 45407163124350958425514811)
          ·
            refine ⟨68110744686526437638272217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45407163124350958425514811 68110744686526437638272217)
            ·
              refine ⟨51083058514894828228704163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68110744686526437638272217 51083058514894828228704163)
              ·
                refine ⟨76624587772342242343056245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51083058514894828228704163 76624587772342242343056245)
                ·
                  refine ⟨7183555103657085219661523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76624587772342242343056245 7183555103657085219661523)
                  ·
                    refine ⟨10775332655485627829492285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7183555103657085219661523 10775332655485627829492285)
                    ·
                      refine ⟨4040749745807110436059607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10775332655485627829492285 4040749745807110436059607)
                      ·
                        rfl

theorem cell23_7869332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_7869332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869332 prefixEnd_7869332 := by exact prefixLift 7869332
  have htrace : WordTrace (prefixWord ++ tailWord_7869332) baseStart_7869332 baseEnd_7869332 := by
    simpa [prefixWord, tailWord_7869332, baseEnd_7869332] using wordTrace_append hprefix tailTrace_7869332
  have hstable : (prefixWord ++ tailWord_7869332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869332).length < 2 ^ (prefixWord ++ tailWord_7869332).sum := by decide
  have hdescent : baseEnd_7869332 < baseStart_7869332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869495 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_7869495 : Nat := 118140960795 + 7869495 * 2 ^ 59
def prefixEnd_7869495 : Nat := 4983230072969 + 3 ^ 40 * 7869495 * 2
def baseEnd_7869495 : Nat := 4040833443153793298321357

theorem tailTrace_7869495 : CollatzResearch.WordTrace tailWord_7869495 prefixEnd_7869495 4040833443153793298321357 := by
  unfold tailWord_7869495
  simp only [CollatzResearch.WordTrace]
  refine ⟨287024062625171092589585939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191349375083447395059723959 287024062625171092589585939)
  ·
    refine ⟨430536093937756638884378909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287024062625171092589585939 430536093937756638884378909)
    ·
      refine ⟨161451035226658739581642091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430536093937756638884378909 161451035226658739581642091)
      ·
        refine ⟨242176552839988109372463137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161451035226658739581642091 242176552839988109372463137)
        ·
          refine ⟨181632414629991082029347353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242176552839988109372463137 181632414629991082029347353)
          ·
            refine ⟨136224310972493311522010515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181632414629991082029347353 136224310972493311522010515)
            ·
              refine ⟨204336466458739967283015773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136224310972493311522010515 204336466458739967283015773)
              ·
                refine ⟨76626174922027487731130915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204336466458739967283015773 76626174922027487731130915)
                ·
                  refine ⟨114939262383041231596696373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76626174922027487731130915 114939262383041231596696373)
                  ·
                    refine ⟨10775555848410115462190285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114939262383041231596696373 10775555848410115462190285)
                    ·
                      refine ⟨4040833443153793298321357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10775555848410115462190285 4040833443153793298321357)
                      ·
                        rfl

theorem cell23_7869495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_7869495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869495 prefixEnd_7869495 := by exact prefixLift 7869495
  have htrace : WordTrace (prefixWord ++ tailWord_7869495) baseStart_7869495 baseEnd_7869495 := by
    simpa [prefixWord, tailWord_7869495, baseEnd_7869495] using wordTrace_append hprefix tailTrace_7869495
  have hstable : (prefixWord ++ tailWord_7869495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869495).length < 2 ^ (prefixWord ++ tailWord_7869495).sum := by decide
  have hdescent : baseEnd_7869495 < baseStart_7869495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869496 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 2, 2, 2]
def baseStart_7869496 : Nat := 118140960795 + 7869496 * 2 ^ 59
def prefixEnd_7869496 : Nat := 4983230072969 + 3 ^ 40 * 7869496 * 2
def baseEnd_7869496 : Nat := 4040833956634447794408853

theorem tailTrace_7869496 : CollatzResearch.WordTrace tailWord_7869496 prefixEnd_7869496 4040833956634447794408853 := by
  unfold tailWord_7869496
  simp only [CollatzResearch.WordTrace]
  refine ⟨143512049549083734880186171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191349399398778313173581561 143512049549083734880186171)
  ·
    refine ⟨215268074323625602320279257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143512049549083734880186171 215268074323625602320279257)
    ·
      refine ⟨161451055742719201740209443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215268074323625602320279257 161451055742719201740209443)
      ·
        refine ⟨242176583614078802610314165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161451055742719201740209443 242176583614078802610314165)
        ·
          refine ⟨22704054713819887744716953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242176583614078802610314165 22704054713819887744716953)
          ·
            refine ⟨17028041035364915808537715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22704054713819887744716953 17028041035364915808537715)
            ·
              refine ⟨25542061553047373712806573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17028041035364915808537715 25542061553047373712806573)
              ·
                refine ⟨9578273082392765142302465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25542061553047373712806573 9578273082392765142302465)
                ·
                  refine ⟨7183704811794573856726849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9578273082392765142302465 7183704811794573856726849)
                  ·
                    refine ⟨5387778608845930392545137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183704811794573856726849 5387778608845930392545137)
                    ·
                      refine ⟨4040833956634447794408853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387778608845930392545137 4040833956634447794408853)
                      ·
                        rfl

theorem cell23_7869496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_7869496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869496 prefixEnd_7869496 := by exact prefixLift 7869496
  have htrace : WordTrace (prefixWord ++ tailWord_7869496) baseStart_7869496 baseEnd_7869496 := by
    simpa [prefixWord, tailWord_7869496, baseEnd_7869496] using wordTrace_append hprefix tailTrace_7869496
  have hstable : (prefixWord ++ tailWord_7869496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869496).length < 2 ^ (prefixWord ++ tailWord_7869496).sum := by decide
  have hdescent : baseEnd_7869496 < baseStart_7869496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869525 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7869525 : Nat := 118140960795 + 7869525 * 2 ^ 59
def prefixEnd_7869525 : Nat := 4983230072969 + 3 ^ 40 * 7869525 * 2
def baseEnd_7869525 : Nat := 4040848847573428180946219

theorem tailTrace_7869525 : CollatzResearch.WordTrace tailWord_7869525 prefixEnd_7869525 4040848847573428180946219 := by
  unfold tailWord_7869525
  simp only [CollatzResearch.WordTrace]
  refine ⟨287025156815062407713178029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191350104543374938475452019 287025156815062407713178029)
  ·
    refine ⟨107634433805648402892441761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287025156815062407713178029 107634433805648402892441761)
    ·
      refine ⟨80725825354236302169331321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107634433805648402892441761 80725825354236302169331321)
      ·
        refine ⟨60544369015677226626998491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80725825354236302169331321 60544369015677226626998491)
        ·
          refine ⟨90816553523515839940497737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60544369015677226626998491 90816553523515839940497737)
          ·
            refine ⟨68112415142636879955373303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90816553523515839940497737 68112415142636879955373303)
            ·
              refine ⟨102168622713955319933059955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68112415142636879955373303 102168622713955319933059955)
              ·
                refine ⟨153252934070932979899589933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102168622713955319933059955 153252934070932979899589933)
                ·
                  refine ⟨57469850276599867462346225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153252934070932979899589933 57469850276599867462346225)
                  ·
                    refine ⟨43102387707449900596759669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57469850276599867462346225 43102387707449900596759669)
                    ·
                      refine ⟨4040848847573428180946219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43102387707449900596759669 4040848847573428180946219)
                      ·
                        rfl

theorem cell23_7869525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7869525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869525 prefixEnd_7869525 := by exact prefixLift 7869525
  have htrace : WordTrace (prefixWord ++ tailWord_7869525) baseStart_7869525 baseEnd_7869525 := by
    simpa [prefixWord, tailWord_7869525, baseEnd_7869525] using wordTrace_append hprefix tailTrace_7869525
  have hstable : (prefixWord ++ tailWord_7869525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869525).length < 2 ^ (prefixWord ++ tailWord_7869525).sum := by decide
  have hdescent : baseEnd_7869525 < baseStart_7869525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869532 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7869532 : Nat := 118140960795 + 7869532 * 2 ^ 59
def prefixEnd_7869532 : Nat := 4983230072969 + 3 ^ 40 * 7869532 * 2
def baseEnd_7869532 : Nat := 1346950813979336551186229

theorem tailTrace_7869532 : CollatzResearch.WordTrace tailWord_7869532 prefixEnd_7869532 1346950813979336551186229 := by
  unfold tailWord_7869532
  simp only [CollatzResearch.WordTrace]
  refine ⟨143512706063018523954341425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191350274750691365272455233 143512706063018523954341425)
  ·
    refine ⟨107634529547263892965756069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143512706063018523954341425 107634529547263892965756069)
    ·
      refine ⟨20181474290111979931079263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107634529547263892965756069 20181474290111979931079263)
      ·
        refine ⟨30272211435167969896618895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20181474290111979931079263 30272211435167969896618895)
        ·
          refine ⟨45408317152751954844928343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30272211435167969896618895 45408317152751954844928343)
          ·
            refine ⟨68112475729127932267392515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45408317152751954844928343 68112475729127932267392515)
            ·
              refine ⟨102168713593691898401088773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68112475729127932267392515 102168713593691898401088773)
              ·
                refine ⟨19156633798817230950204145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102168713593691898401088773 19156633798817230950204145)
                ·
                  refine ⟨14367475349112923212653109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19156633798817230950204145 14367475349112923212653109)
                  ·
                    refine ⟨1346950813979336551186229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14367475349112923212653109 1346950813979336551186229)
                    ·
                      rfl

theorem cell23_7869532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7869532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869532 prefixEnd_7869532 := by exact prefixLift 7869532
  have htrace : WordTrace (prefixWord ++ tailWord_7869532) baseStart_7869532 baseEnd_7869532 := by
    simpa [prefixWord, tailWord_7869532, baseEnd_7869532] using wordTrace_append hprefix tailTrace_7869532
  have hstable : (prefixWord ++ tailWord_7869532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869532).length < 2 ^ (prefixWord ++ tailWord_7869532).sum := by decide
  have hdescent : baseEnd_7869532 < baseStart_7869532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869569 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_7869569 : Nat := 118140960795 + 7869569 * 2 ^ 59
def prefixEnd_7869569 : Nat := 4983230072969 + 3 ^ 40 * 7869569 * 2
def baseEnd_7869569 : Nat := 4040871440722226008796017

theorem tailTrace_7869569 : CollatzResearch.WordTrace tailWord_7869569 prefixEnd_7869569 4040871440722226008796017 := by
  unfold tailWord_7869569
  simp only [CollatzResearch.WordTrace]
  refine ⟨287026761626903003227779761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191351174417935335485186507 287026761626903003227779761)
  ·
    refine ⟨215270071220177252420834821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287026761626903003227779761 215270071220177252420834821)
    ·
      refine ⟨40363138353783234828906529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215270071220177252420834821 40363138353783234828906529)
      ·
        refine ⟨30272353765337426121679897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40363138353783234828906529 30272353765337426121679897)
        ·
          refine ⟨22704265324003069591259923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30272353765337426121679897 22704265324003069591259923)
          ·
            refine ⟨34056397986004604386889885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22704265324003069591259923 34056397986004604386889885)
            ·
              refine ⟨12771149244751726645083707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34056397986004604386889885 12771149244751726645083707)
              ·
                refine ⟨19156723867127589967625561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12771149244751726645083707 19156723867127589967625561)
                ·
                  refine ⟨14367542900345692475719171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19156723867127589967625561 14367542900345692475719171)
                  ·
                    refine ⟨21551314350518538713578757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14367542900345692475719171 21551314350518538713578757)
                    ·
                      refine ⟨4040871440722226008796017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21551314350518538713578757 4040871440722226008796017)
                      ·
                        rfl

theorem cell23_7869569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_7869569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869569 prefixEnd_7869569 := by exact prefixLift 7869569
  have htrace : WordTrace (prefixWord ++ tailWord_7869569) baseStart_7869569 baseEnd_7869569 := by
    simpa [prefixWord, tailWord_7869569, baseEnd_7869569] using wordTrace_append hprefix tailTrace_7869569
  have hstable : (prefixWord ++ tailWord_7869569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869569).length < 2 ^ (prefixWord ++ tailWord_7869569).sum := by decide
  have hdescent : baseEnd_7869569 < baseStart_7869569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869575 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 8]
def baseStart_7869575 : Nat := 118140960795 + 7869575 * 2 ^ 59
def prefixEnd_7869575 : Nat := 4983230072969 + 3 ^ 40 * 7869575 * 2
def baseEnd_7869575 : Nat := 448986057956239220591221

theorem tailTrace_7869575 : CollatzResearch.WordTrace tailWord_7869575 prefixEnd_7869575 448986057956239220591221 := by
  unfold tailWord_7869575
  simp only [CollatzResearch.WordTrace]
  refine ⟨287026980464881266252498179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191351320309920844168332119 287026980464881266252498179)
  ·
    refine ⟨430540470697321899378747269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287026980464881266252498179 430540470697321899378747269)
    ·
      refine ⟨80726338255747856133515113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430540470697321899378747269 80726338255747856133515113)
      ·
        refine ⟨60544753691810892100136335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80726338255747856133515113 60544753691810892100136335)
        ·
          refine ⟨90817130537716338150204503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60544753691810892100136335 90817130537716338150204503)
          ·
            refine ⟨136225695806574507225306755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90817130537716338150204503 136225695806574507225306755)
            ·
              refine ⟨204338543709861760837960133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136225695806574507225306755 204338543709861760837960133)
              ·
                refine ⟨38313476945599080157117525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204338543709861760837960133 38313476945599080157117525)
                ·
                  refine ⟨448986057956239220591221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38313476945599080157117525 448986057956239220591221)
                  ·
                    rfl

theorem cell23_7869575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 8].length) (baseStart_7869575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869575 prefixEnd_7869575 := by exact prefixLift 7869575
  have htrace : WordTrace (prefixWord ++ tailWord_7869575) baseStart_7869575 baseEnd_7869575 := by
    simpa [prefixWord, tailWord_7869575, baseEnd_7869575] using wordTrace_append hprefix tailTrace_7869575
  have hstable : (prefixWord ++ tailWord_7869575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869575).length < 2 ^ (prefixWord ++ tailWord_7869575).sum := by decide
  have hdescent : baseEnd_7869575 < baseStart_7869575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869582 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7869582 : Nat := 118140960795 + 7869582 * 2 ^ 59
def prefixEnd_7869582 : Nat := 4983230072969 + 3 ^ 40 * 7869582 * 2
def baseEnd_7869582 : Nat := 4040878115970734457933457

theorem tailTrace_7869582 : CollatzResearch.WordTrace tailWord_7869582 prefixEnd_7869582 4040878115970734457933457 := by
  unfold tailWord_7869582
  simp only [CollatzResearch.WordTrace]
  refine ⟨35878404471981988306000375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191351490517237270965335333 35878404471981988306000375)
  ·
    refine ⟨53817606707972982459000563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35878404471981988306000375 53817606707972982459000563)
    ·
      refine ⟨80726410061959473688500845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53817606707972982459000563 80726410061959473688500845)
      ·
        refine ⟨30272403773234802633187817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80726410061959473688500845 30272403773234802633187817)
        ·
          refine ⟨22704302829926101974890863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30272403773234802633187817 22704302829926101974890863)
          ·
            refine ⟨34056454244889152962336295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22704302829926101974890863 34056454244889152962336295)
            ·
              refine ⟨51084681367333729443504443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34056454244889152962336295 51084681367333729443504443)
              ·
                refine ⟨76627022051000594165256665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51084681367333729443504443 76627022051000594165256665)
                ·
                  refine ⟨57470266538250445623942499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76627022051000594165256665 57470266538250445623942499)
                  ·
                    refine ⟨86205399807375668435913749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57470266538250445623942499 86205399807375668435913749)
                    ·
                      refine ⟨4040878115970734457933457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86205399807375668435913749 4040878115970734457933457)
                      ·
                        rfl

theorem cell23_7869582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7869582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869582 prefixEnd_7869582 := by exact prefixLift 7869582
  have htrace : WordTrace (prefixWord ++ tailWord_7869582) baseStart_7869582 baseEnd_7869582 := by
    simpa [prefixWord, tailWord_7869582, baseEnd_7869582] using wordTrace_append hprefix tailTrace_7869582
  have hstable : (prefixWord ++ tailWord_7869582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869582).length < 2 ^ (prefixWord ++ tailWord_7869582).sum := by decide
  have hdescent : baseEnd_7869582 < baseStart_7869582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869592 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 8]
def baseStart_7869592 : Nat := 118140960795 + 7869592 * 2 ^ 59
def prefixEnd_7869592 : Nat := 4983230072969 + 3 ^ 40 * 7869592 * 2
def baseEnd_7869592 : Nat := 448987027864142157645379

theorem tailTrace_7869592 : CollatzResearch.WordTrace tailWord_7869592 prefixEnd_7869592 448987027864142157645379 := by
  unfold tailWord_7869592
  simp only [CollatzResearch.WordTrace]
  refine ⟨143513800252909839077933515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191351733670546452103911353 143513800252909839077933515)
  ·
    refine ⟨215270700379364758616900273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143513800252909839077933515 215270700379364758616900273)
    ·
      refine ⟨161453025284523568962675205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215270700379364758616900273 161453025284523568962675205)
      ·
        refine ⟨30272442240848169180501601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161453025284523568962675205 30272442240848169180501601)
        ·
          refine ⟨22704331680636126885376201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30272442240848169180501601 22704331680636126885376201)
          ·
            refine ⟨17028248760477095164032151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22704331680636126885376201 17028248760477095164032151)
            ·
              refine ⟨25542373140715642746048227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17028248760477095164032151 25542373140715642746048227)
              ·
                refine ⟨38313559711073464119072341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25542373140715642746048227 38313559711073464119072341)
                ·
                  refine ⟨448987027864142157645379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38313559711073464119072341 448987027864142157645379)
                  ·
                    rfl

theorem cell23_7869592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 8].length) (baseStart_7869592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869592 prefixEnd_7869592 := by exact prefixLift 7869592
  have htrace : WordTrace (prefixWord ++ tailWord_7869592) baseStart_7869592 baseEnd_7869592 := by
    simpa [prefixWord, tailWord_7869592, baseEnd_7869592] using wordTrace_append hprefix tailTrace_7869592
  have hstable : (prefixWord ++ tailWord_7869592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869592).length < 2 ^ (prefixWord ++ tailWord_7869592).sum := by decide
  have hdescent : baseEnd_7869592 < baseStart_7869592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869596 : List Nat := [2, 2, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_7869596 : Nat := 118140960795 + 7869596 * 2 ^ 59
def prefixEnd_7869596 : Nat := 4983230072969 + 3 ^ 40 * 7869596 * 2
def baseEnd_7869596 : Nat := 1346961768233299134386131

theorem tailTrace_7869596 : CollatzResearch.WordTrace tailWord_7869596 prefixEnd_7869596 1346961768233299134386131 := by
  unfold tailWord_7869596
  simp only [CollatzResearch.WordTrace]
  refine ⟨143513873198902593419506321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191351830931870124559341761 143513873198902593419506321)
  ·
    refine ⟨107635404899176945064629741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143513873198902593419506321 107635404899176945064629741)
    ·
      refine ⟨40363276837191354399236153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107635404899176945064629741 40363276837191354399236153)
      ·
        refine ⟨30272457627893515799427115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40363276837191354399236153 30272457627893515799427115)
        ·
          refine ⟨45408686441840273699140673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30272457627893515799427115 45408686441840273699140673)
          ·
            refine ⟨34056514831380205274355505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45408686441840273699140673 34056514831380205274355505)
            ·
              refine ⟨25542386123535153955766629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34056514831380205274355505 25542386123535153955766629)
              ·
                refine ⟨4789197398162841366706243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25542386123535153955766629 4789197398162841366706243)
                ·
                  refine ⟨7183796097244262050059365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789197398162841366706243 7183796097244262050059365)
                  ·
                    refine ⟨1346961768233299134386131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7183796097244262050059365 1346961768233299134386131)
                    ·
                      rfl

theorem cell23_7869596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_7869596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869596 prefixEnd_7869596 := by exact prefixLift 7869596
  have htrace : WordTrace (prefixWord ++ tailWord_7869596) baseStart_7869596 baseEnd_7869596 := by
    simpa [prefixWord, tailWord_7869596, baseEnd_7869596] using wordTrace_append hprefix tailTrace_7869596
  have hstable : (prefixWord ++ tailWord_7869596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869596).length < 2 ^ (prefixWord ++ tailWord_7869596).sum := by decide
  have hdescent : baseEnd_7869596 < baseStart_7869596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869615 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_7869615 : Nat := 118140960795 + 7869615 * 2 ^ 59
def prefixEnd_7869615 : Nat := 4983230072969 + 3 ^ 40 * 7869615 * 2
def baseEnd_7869615 : Nat := 4040895060832332828820805

theorem tailTrace_7869615 : CollatzResearch.WordTrace tailWord_7869615 prefixEnd_7869615 4040895060832332828820805 := by
  unfold tailWord_7869615
  simp only [CollatzResearch.WordTrace]
  refine ⟨287028439384736353083954299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191352292923157568722636199 287028439384736353083954299)
  ·
    refine ⟨430542659077104529625931449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287028439384736353083954299 430542659077104529625931449)
    ·
      refine ⟨322906994307828397219448587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430542659077104529625931449 322906994307828397219448587)
      ·
        refine ⟨484360491461742595829172881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322906994307828397219448587 484360491461742595829172881)
        ·
          refine ⟨363270368596306946871879661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484360491461742595829172881 363270368596306946871879661)
          ·
            refine ⟨136226388223615105076954873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363270368596306946871879661 136226388223615105076954873)
            ·
              refine ⟨102169791167711328807716155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136226388223615105076954873 102169791167711328807716155)
              ·
                refine ⟨153254686751566993211574233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102169791167711328807716155 153254686751566993211574233)
                ·
                  refine ⟨114941015063675244908680675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153254686751566993211574233 114941015063675244908680675)
                  ·
                    refine ⟨172411522595512867363021013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114941015063675244908680675 172411522595512867363021013)
                    ·
                      refine ⟨4040895060832332828820805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172411522595512867363021013 4040895060832332828820805)
                      ·
                        rfl

theorem cell23_7869615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_7869615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869615 prefixEnd_7869615 := by exact prefixLift 7869615
  have htrace : WordTrace (prefixWord ++ tailWord_7869615) baseStart_7869615 baseEnd_7869615 := by
    simpa [prefixWord, tailWord_7869615, baseEnd_7869615] using wordTrace_append hprefix tailTrace_7869615
  have hstable : (prefixWord ++ tailWord_7869615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869615).length < 2 ^ (prefixWord ++ tailWord_7869615).sum := by decide
  have hdescent : baseEnd_7869615 < baseStart_7869615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869619 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 3]
def baseStart_7869619 : Nat := 118140960795 + 7869619 * 2 ^ 59
def prefixEnd_7869619 : Nat := 4983230072969 + 3 ^ 40 * 7869619 * 2
def baseEnd_7869619 : Nat := 4040897114754950813170787

theorem tailTrace_7869619 : CollatzResearch.WordTrace tailWord_7869619 prefixEnd_7869619 4040897114754950813170787 := by
  unfold tailWord_7869619
  simp only [CollatzResearch.WordTrace]
  refine ⟨287028585276721861767099911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191352390184481241178066607 287028585276721861767099911)
  ·
    refine ⟨430542877915082792650649867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287028585276721861767099911 430542877915082792650649867)
    ·
      refine ⟨645814316872624188975974801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430542877915082792650649867 645814316872624188975974801)
      ·
        refine ⟨484360737654468141731981101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645814316872624188975974801 484360737654468141731981101)
        ·
          refine ⟨181635276620425553149492913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484360737654468141731981101 181635276620425553149492913)
          ·
            refine ⟨136226457465319164862119685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181635276620425553149492913 136226457465319164862119685)
            ·
              refine ⟨25542460774747343411647441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136226457465319164862119685 25542460774747343411647441)
              ·
                refine ⟨19156845581060507558735581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25542460774747343411647441 19156845581060507558735581)
                ·
                  refine ⟨7183817092897690334525843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19156845581060507558735581 7183817092897690334525843)
                  ·
                    refine ⟨10775725639346535501788765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7183817092897690334525843 10775725639346535501788765)
                    ·
                      refine ⟨4040897114754950813170787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10775725639346535501788765 4040897114754950813170787)
                      ·
                        rfl

theorem cell23_7869619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 3].length) (baseStart_7869619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869619 prefixEnd_7869619 := by exact prefixLift 7869619
  have htrace : WordTrace (prefixWord ++ tailWord_7869619) baseStart_7869619 baseEnd_7869619 := by
    simpa [prefixWord, tailWord_7869619, baseEnd_7869619] using wordTrace_append hprefix tailTrace_7869619
  have hstable : (prefixWord ++ tailWord_7869619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869619).length < 2 ^ (prefixWord ++ tailWord_7869619).sum := by decide
  have hdescent : baseEnd_7869619 < baseStart_7869619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869629 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_7869629 : Nat := 118140960795 + 7869629 * 2 ^ 59
def prefixEnd_7869629 : Nat := 4983230072969 + 3 ^ 40 * 7869629 * 2
def baseEnd_7869629 : Nat := 4040902249561495774045741

theorem tailTrace_7869629 : CollatzResearch.WordTrace tailWord_7869629 prefixEnd_7869629 4040902249561495774045741 := by
  unfold tailWord_7869629
  simp only [CollatzResearch.WordTrace]
  refine ⟨287028950006685633474963941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191352633337790422316642627 287028950006685633474963941)
  ·
    refine ⟨53817928126253556276555739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287028950006685633474963941 53817928126253556276555739)
    ·
      refine ⟨80726892189380334414833609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53817928126253556276555739 80726892189380334414833609)
      ·
        refine ⟨60545169142035250811125207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80726892189380334414833609 60545169142035250811125207)
        ·
          refine ⟨90817753713052876216687811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60545169142035250811125207 90817753713052876216687811)
          ·
            refine ⟨136226630569579314325031717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90817753713052876216687811 136226630569579314325031717)
            ·
              refine ⟨25542493231796121435943447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136226630569579314325031717 25542493231796121435943447)
              ·
                refine ⟨38313739847694182153915171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25542493231796121435943447 38313739847694182153915171)
                ·
                  refine ⟨57470609771541273230872757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38313739847694182153915171 57470609771541273230872757)
                  ·
                    refine ⟨5387869666081994365394321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57470609771541273230872757 5387869666081994365394321)
                    ·
                      refine ⟨4040902249561495774045741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387869666081994365394321 4040902249561495774045741)
                      ·
                        rfl

theorem cell23_7869629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_7869629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869629 prefixEnd_7869629 := by exact prefixLift 7869629
  have htrace : WordTrace (prefixWord ++ tailWord_7869629) baseStart_7869629 baseEnd_7869629 := by
    simpa [prefixWord, tailWord_7869629, baseEnd_7869629] using wordTrace_append hprefix tailTrace_7869629
  have hstable : (prefixWord ++ tailWord_7869629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869629).length < 2 ^ (prefixWord ++ tailWord_7869629).sum := by decide
  have hdescent : baseEnd_7869629 < baseStart_7869629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869653 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7869653 : Nat := 118140960795 + 7869653 * 2 ^ 59
def prefixEnd_7869653 : Nat := 4983230072969 + 3 ^ 40 * 7869653 * 2
def baseEnd_7869653 : Nat := 4040914573097203680145631

theorem tailTrace_7869653 : CollatzResearch.WordTrace tailWord_7869653 prefixEnd_7869653 4040914573097203680145631 := by
  unfold tailWord_7869653
  simp only [CollatzResearch.WordTrace]
  refine ⟨287029825358598685573837613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191353216905732457049225075 287029825358598685573837613)
  ·
    refine ⟨107636184509474507090189105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287029825358598685573837613 107636184509474507090189105)
    ·
      refine ⟨80727138382105880317641829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107636184509474507090189105 80727138382105880317641829)
      ·
        refine ⟨15136338446644852559557843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80727138382105880317641829 15136338446644852559557843)
        ·
          refine ⟨22704507669967278839336765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15136338446644852559557843 22704507669967278839336765)
          ·
            refine ⟨8514190376237729564751287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22704507669967278839336765 8514190376237729564751287)
            ·
              refine ⟨12771285564356594347126931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514190376237729564751287 12771285564356594347126931)
              ·
                refine ⟨19156928346534891520690397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12771285564356594347126931 19156928346534891520690397)
                ·
                  refine ⟨7183848129950584320258899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19156928346534891520690397 7183848129950584320258899)
                  ·
                    refine ⟨10775772194925876480388349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7183848129950584320258899 10775772194925876480388349)
                    ·
                      refine ⟨4040914573097203680145631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10775772194925876480388349 4040914573097203680145631)
                      ·
                        rfl

theorem cell23_7869653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7869653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869653 prefixEnd_7869653 := by exact prefixLift 7869653
  have htrace : WordTrace (prefixWord ++ tailWord_7869653) baseStart_7869653 baseEnd_7869653 := by
    simpa [prefixWord, tailWord_7869653, baseEnd_7869653] using wordTrace_append hprefix tailTrace_7869653
  have hstable : (prefixWord ++ tailWord_7869653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869653).length < 2 ^ (prefixWord ++ tailWord_7869653).sum := by decide
  have hdescent : baseEnd_7869653 < baseStart_7869653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869672 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7869672 : Nat := 118140960795 + 7869672 * 2 ^ 59
def prefixEnd_7869672 : Nat := 4983230072969 + 3 ^ 40 * 7869672 * 2
def baseEnd_7869672 : Nat := 4040924329229639105808043

theorem tailTrace_7869672 : CollatzResearch.WordTrace tailWord_7869672 prefixEnd_7869672 4040924329229639105808043 := by
  unfold tailWord_7869672
  simp only [CollatzResearch.WordTrace]
  refine ⟨143515259172764925909389635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191353678897019901212519513 143515259172764925909389635)
  ·
    refine ⟨215272888759147388864084453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143515259172764925909389635 215272888759147388864084453)
    ·
      refine ⟨40363666642340135412015835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215272888759147388864084453 40363666642340135412015835)
      ·
        refine ⟨60545499963510203118023753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40363666642340135412015835 60545499963510203118023753)
        ·
          refine ⟨45409124972632652338517815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60545499963510203118023753 45409124972632652338517815)
          ·
            refine ⟨68113687458948978507776723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45409124972632652338517815 68113687458948978507776723)
            ·
              refine ⟨102170531188423467761665085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68113687458948978507776723 102170531188423467761665085)
              ·
                refine ⟨38313949195658800410624407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102170531188423467761665085 38313949195658800410624407)
                ·
                  refine ⟨57470923793488200615936611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38313949195658800410624407 57470923793488200615936611)
                  ·
                    refine ⟨86206385690232300923904917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57470923793488200615936611 86206385690232300923904917)
                    ·
                      refine ⟨4040924329229639105808043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86206385690232300923904917 4040924329229639105808043)
                      ·
                        rfl

theorem cell23_7869672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7869672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869672 prefixEnd_7869672 := by exact prefixLift 7869672
  have htrace : WordTrace (prefixWord ++ tailWord_7869672) baseStart_7869672 baseEnd_7869672 := by
    simpa [prefixWord, tailWord_7869672, baseEnd_7869672] using wordTrace_append hprefix tailTrace_7869672
  have hstable : (prefixWord ++ tailWord_7869672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869672).length < 2 ^ (prefixWord ++ tailWord_7869672).sum := by decide
  have hdescent : baseEnd_7869672 < baseStart_7869672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869676 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_7869676 : Nat := 118140960795 + 7869676 * 2 ^ 59
def prefixEnd_7869676 : Nat := 4983230072969 + 3 ^ 40 * 7869676 * 2
def baseEnd_7869676 : Nat := 4040926383152257090158025

theorem tailTrace_7869676 : CollatzResearch.WordTrace tailWord_7869676 prefixEnd_7869676 4040926383152257090158025 := by
  unfold tailWord_7869676
  simp only [CollatzResearch.WordTrace]
  refine ⟨143515332118757680250962441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191353776158343573667949921 143515332118757680250962441)
  ·
    refine ⟨107636499089068260188221831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143515332118757680250962441 107636499089068260188221831)
    ·
      refine ⟨161454748633602390282332747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107636499089068260188221831 161454748633602390282332747)
      ·
        refine ⟨242182122950403585423499121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161454748633602390282332747 242182122950403585423499121)
        ·
          refine ⟨181636592212802689067624341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242182122950403585423499121 181636592212802689067624341)
          ·
            refine ⟨8514215259975126050044891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181636592212802689067624341 8514215259975126050044891)
            ·
              refine ⟨12771322889962689075067337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514215259975126050044891 12771322889962689075067337)
              ·
                refine ⟨9578492167472016806300503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12771322889962689075067337 9578492167472016806300503)
                ·
                  refine ⟨14367738251208025209450755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9578492167472016806300503 14367738251208025209450755)
                  ·
                    refine ⟨21551607376812037814176133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14367738251208025209450755 21551607376812037814176133)
                    ·
                      refine ⟨4040926383152257090158025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21551607376812037814176133 4040926383152257090158025)
                      ·
                        rfl

theorem cell23_7869676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_7869676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869676 prefixEnd_7869676 := by exact prefixLift 7869676
  have htrace : WordTrace (prefixWord ++ tailWord_7869676) baseStart_7869676 baseEnd_7869676 := by
    simpa [prefixWord, tailWord_7869676, baseEnd_7869676] using wordTrace_append hprefix tailTrace_7869676
  have hstable : (prefixWord ++ tailWord_7869676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869676).length < 2 ^ (prefixWord ++ tailWord_7869676).sum := by decide
  have hdescent : baseEnd_7869676 < baseStart_7869676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869710 : List Nat := [4, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_7869710 : Nat := 118140960795 + 7869710 * 2 ^ 59
def prefixEnd_7869710 : Nat := 4983230072969 + 3 ^ 40 * 7869710 * 2
def baseEnd_7869710 : Nat := 4040943841494509957132869

theorem tailTrace_7869710 : CollatzResearch.WordTrace tailWord_7869710 prefixEnd_7869710 4040943841494509957132869 := by
  unfold tailWord_7869710
  simp only [CollatzResearch.WordTrace]
  refine ⟨35878988039924023038582823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191354602879594789539108389 35878988039924023038582823)
  ·
    refine ⟨53818482059886034557874235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35878988039924023038582823 53818482059886034557874235)
    ·
      refine ⟨80727723089829051836811353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53818482059886034557874235 80727723089829051836811353)
      ·
        refine ⟨60545792317371788877608515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80727723089829051836811353 60545792317371788877608515)
        ·
          refine ⟨90818688476057683316412773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60545792317371788877608515 90818688476057683316412773)
          ·
            refine ⟨17028504089260815621827395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90818688476057683316412773 17028504089260815621827395)
            ·
              refine ⟨25542756133891223432741093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17028504089260815621827395 25542756133891223432741093)
              ·
                refine ⟨4789266775104604393638955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25542756133891223432741093 4789266775104604393638955)
                ·
                  refine ⟨7183900162656906590458433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789266775104604393638955 7183900162656906590458433)
                  ·
                    refine ⟨5387925121992679942843825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183900162656906590458433 5387925121992679942843825)
                    ·
                      refine ⟨4040943841494509957132869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387925121992679942843825 4040943841494509957132869)
                      ·
                        rfl

theorem cell23_7869710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_7869710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869710 prefixEnd_7869710 := by exact prefixLift 7869710
  have htrace : WordTrace (prefixWord ++ tailWord_7869710) baseStart_7869710 baseEnd_7869710 := by
    simpa [prefixWord, tailWord_7869710, baseEnd_7869710] using wordTrace_append hprefix tailTrace_7869710
  have hstable : (prefixWord ++ tailWord_7869710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869710).length < 2 ^ (prefixWord ++ tailWord_7869710).sum := by decide
  have hdescent : baseEnd_7869710 < baseStart_7869710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869752 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_7869752 : Nat := 118140960795 + 7869752 * 2 ^ 59
def prefixEnd_7869752 : Nat := 4983230072969 + 3 ^ 40 * 7869752 * 2
def baseEnd_7869752 : Nat := 4040965407681998792807675

theorem tailTrace_7869752 : CollatzResearch.WordTrace tailWord_7869752 prefixEnd_7869752 4040965407681998792807675 := by
  unfold tailWord_7869752
  simp only [CollatzResearch.WordTrace]
  refine ⟨143516718092620012740845755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191355624123493350321127673 143516718092620012740845755)
  ·
    refine ⟨215275077138930019111268633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143516718092620012740845755 215275077138930019111268633)
    ·
      refine ⟨161456307854197514333451475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215275077138930019111268633 161456307854197514333451475)
      ·
        refine ⟨242184461781296271500177213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161456307854197514333451475 242184461781296271500177213)
        ·
          refine ⟨90819173167986101812566455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242184461781296271500177213 90819173167986101812566455)
          ·
            refine ⟨136228759751979152718849683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90819173167986101812566455 136228759751979152718849683)
            ·
              refine ⟨204343139627968729078274525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136228759751979152718849683 204343139627968729078274525)
              ·
                refine ⟨76628677360488273404352947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204343139627968729078274525 76628677360488273404352947)
                ·
                  refine ⟨114943016040732410106529421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76628677360488273404352947 114943016040732410106529421)
                  ·
                    refine ⟨43103631015274653789948533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114943016040732410106529421 43103631015274653789948533)
                    ·
                      refine ⟨4040965407681998792807675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43103631015274653789948533 4040965407681998792807675)
                      ·
                        rfl

theorem cell23_7869752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_7869752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869752 prefixEnd_7869752 := by exact prefixLift 7869752
  have htrace : WordTrace (prefixWord ++ tailWord_7869752) baseStart_7869752 baseEnd_7869752 := by
    simpa [prefixWord, tailWord_7869752, baseEnd_7869752] using wordTrace_append hprefix tailTrace_7869752
  have hstable : (prefixWord ++ tailWord_7869752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869752).length < 2 ^ (prefixWord ++ tailWord_7869752).sum := by decide
  have hdescent : baseEnd_7869752 < baseStart_7869752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869783 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 1, 4, 2]
def baseStart_7869783 : Nat := 118140960795 + 7869783 * 2 ^ 59
def prefixEnd_7869783 : Nat := 4983230072969 + 3 ^ 40 * 7869783 * 2
def baseEnd_7869783 : Nat := 4040981325582288171520033

theorem tailTrace_7869783 : CollatzResearch.WordTrace tailWord_7869783 prefixEnd_7869783 4040981325582288171520033 := by
  unfold tailWord_7869783
  simp only [CollatzResearch.WordTrace]
  refine ⟨287034566848127717776070003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191356377898751811850713335 287034566848127717776070003)
  ·
    refine ⟨430551850272191576664105005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287034566848127717776070003 430551850272191576664105005)
    ·
      refine ⟨161456943852071841249039377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430551850272191576664105005 161456943852071841249039377)
      ·
        refine ⟨121092707889053880936779533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161456943852071841249039377 121092707889053880936779533)
        ·
          refine ⟨45409765458395205351292325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121092707889053880936779533 45409765458395205351292325)
          ·
            refine ⟨8514331023449101003367311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45409765458395205351292325 8514331023449101003367311)
            ·
              refine ⟨12771496535173651505050967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514331023449101003367311 12771496535173651505050967)
              ·
                refine ⟨19157244802760477257576451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12771496535173651505050967 19157244802760477257576451)
                ·
                  refine ⟨28735867204140715886364677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19157244802760477257576451 28735867204140715886364677)
                  ·
                    refine ⟨5387975100776384228693377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28735867204140715886364677 5387975100776384228693377)
                    ·
                      refine ⟨4040981325582288171520033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5387975100776384228693377 4040981325582288171520033)
                      ·
                        rfl

theorem cell23_7869783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_7869783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869783 prefixEnd_7869783 := by exact prefixLift 7869783
  have htrace : WordTrace (prefixWord ++ tailWord_7869783) baseStart_7869783 baseEnd_7869783 := by
    simpa [prefixWord, tailWord_7869783, baseEnd_7869783] using wordTrace_append hprefix tailTrace_7869783
  have hstable : (prefixWord ++ tailWord_7869783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869783).length < 2 ^ (prefixWord ++ tailWord_7869783).sum := by decide
  have hdescent : baseEnd_7869783 < baseStart_7869783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869819 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 2, 5]
def baseStart_7869819 : Nat := 118140960795 + 7869819 * 2 ^ 59
def prefixEnd_7869819 : Nat := 4983230072969 + 3 ^ 40 * 7869819 * 2
def baseEnd_7869819 : Nat := 1346999936961950010223289

theorem tailTrace_7869819 : CollatzResearch.WordTrace tailWord_7869819 prefixEnd_7869819 1346999936961950010223289 := by
  unfold tailWord_7869819
  simp only [CollatzResearch.WordTrace]
  refine ⟨287035879875997295924380511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191357253250664863949587007 287035879875997295924380511)
  ·
    refine ⟨430553819813995943886570767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287035879875997295924380511 430553819813995943886570767)
    ·
      refine ⟨645830729720993915829856151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430553819813995943886570767 645830729720993915829856151)
      ·
        refine ⟨968746094581490873744784227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645830729720993915829856151 968746094581490873744784227)
        ·
          refine ⟨1453119141872236310617176341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968746094581490873744784227 1453119141872236310617176341)
          ·
            refine ⟨68114959775261077060180141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1453119141872236310617176341 68114959775261077060180141)
            ·
              refine ⟨25543109915722903897567553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68114959775261077060180141 25543109915722903897567553)
              ·
                refine ⟨19157332436792177923175665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25543109915722903897567553 19157332436792177923175665)
                ·
                  refine ⟨14367999327594133442381749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19157332436792177923175665 14367999327594133442381749)
                  ·
                    refine ⟨1346999936961950010223289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14367999327594133442381749 1346999936961950010223289)
                    ·
                      rfl

theorem cell23_7869819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 5].length) (baseStart_7869819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869819 prefixEnd_7869819 := by exact prefixLift 7869819
  have htrace : WordTrace (prefixWord ++ tailWord_7869819) baseStart_7869819 baseEnd_7869819 := by
    simpa [prefixWord, tailWord_7869819, baseEnd_7869819] using wordTrace_append hprefix tailTrace_7869819
  have hstable : (prefixWord ++ tailWord_7869819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869819).length < 2 ^ (prefixWord ++ tailWord_7869819).sum := by decide
  have hdescent : baseEnd_7869819 < baseStart_7869819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869856 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4]
def baseStart_7869856 : Nat := 118140960795 + 7869856 * 2 ^ 59
def prefixEnd_7869856 : Nat := 4983230072969 + 3 ^ 40 * 7869856 * 2
def baseEnd_7869856 : Nat := 4041018809670066385907197

theorem tailTrace_7869856 : CollatzResearch.WordTrace tailWord_7869856 prefixEnd_7869856 4041018809670066385907197 := by
  unfold tailWord_7869856
  simp only [CollatzResearch.WordTrace]
  refine ⟨143518614688431625621738711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191358152917908834162318281 143518614688431625621738711)
  ·
    refine ⟨215277922032647438432608067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143518614688431625621738711 215277922032647438432608067)
    ·
      refine ⟨322916883048971157648912101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215277922032647438432608067 322916883048971157648912101)
      ·
        refine ⟨60546915571682092059171019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322916883048971157648912101 60546915571682092059171019)
        ·
          refine ⟨90820373357523138088756529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60546915571682092059171019 90820373357523138088756529)
          ·
            refine ⟨68115280018142353566567397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90820373357523138088756529 68115280018142353566567397)
            ·
              refine ⟨12771615003401691293731387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68115280018142353566567397 12771615003401691293731387)
              ·
                refine ⟨19157422505102536940597081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12771615003401691293731387 19157422505102536940597081)
                ·
                  refine ⟨14368066878826902705447811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19157422505102536940597081 14368066878826902705447811)
                  ·
                    refine ⟨21552100318240354058171717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14368066878826902705447811 21552100318240354058171717)
                    ·
                      refine ⟨4041018809670066385907197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21552100318240354058171717 4041018809670066385907197)
                      ·
                        rfl

theorem cell23_7869856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_7869856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869856 prefixEnd_7869856 := by exact prefixLift 7869856
  have htrace : WordTrace (prefixWord ++ tailWord_7869856) baseStart_7869856 baseEnd_7869856 := by
    simpa [prefixWord, tailWord_7869856, baseEnd_7869856] using wordTrace_append hprefix tailTrace_7869856
  have hstable : (prefixWord ++ tailWord_7869856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869856).length < 2 ^ (prefixWord ++ tailWord_7869856).sum := by decide
  have hdescent : baseEnd_7869856 < baseStart_7869856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869910 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_7869910 : Nat := 118140960795 + 7869910 * 2 ^ 59
def prefixEnd_7869910 : Nat := 4983230072969 + 3 ^ 40 * 7869910 * 2
def baseEnd_7869910 : Nat := 4041046537625409174631949

theorem tailTrace_7869910 : CollatzResearch.WordTrace tailWord_7869910 prefixEnd_7869910 4041046537625409174631949 := by
  unfold tailWord_7869910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17939949932416726154121449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191359465945778412310628789 17939949932416726154121449)
  ·
    refine ⟨13454962449312544615591087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17939949932416726154121449 13454962449312544615591087)
    ·
      refine ⟨20182443673968816923386631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13454962449312544615591087 20182443673968816923386631)
      ·
        refine ⟨30273665510953225385079947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20182443673968816923386631 30273665510953225385079947)
        ·
          refine ⟨45410498266429838077619921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30273665510953225385079947 45410498266429838077619921)
          ·
            refine ⟨34057873699822378558214941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45410498266429838077619921 34057873699822378558214941)
            ·
              refine ⟨12771702637433391959330603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34057873699822378558214941 12771702637433391959330603)
              ·
                refine ⟨19157553956150087938995905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12771702637433391959330603 19157553956150087938995905)
                ·
                  refine ⟨14368165467112565954246929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19157553956150087938995905 14368165467112565954246929)
                  ·
                    refine ⟨10776124100334424465685197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14368165467112565954246929 10776124100334424465685197)
                    ·
                      refine ⟨4041046537625409174631949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10776124100334424465685197 4041046537625409174631949)
                      ·
                        rfl

theorem cell23_7869910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_7869910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869910 prefixEnd_7869910 := by exact prefixLift 7869910
  have htrace : WordTrace (prefixWord ++ tailWord_7869910) baseStart_7869910 baseEnd_7869910 := by
    simpa [prefixWord, tailWord_7869910, baseEnd_7869910] using wordTrace_append hprefix tailTrace_7869910
  have hstable : (prefixWord ++ tailWord_7869910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869910).length < 2 ^ (prefixWord ++ tailWord_7869910).sum := by decide
  have hdescent : baseEnd_7869910 < baseStart_7869910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869930 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 6]
def baseStart_7869930 : Nat := 118140960795 + 7869930 * 2 ^ 59
def prefixEnd_7869930 : Nat := 4983230072969 + 3 ^ 40 * 7869930 * 2
def baseEnd_7869930 : Nat := 449006311915388788486873

theorem tailTrace_7869930 : CollatzResearch.WordTrace tailWord_7869930 prefixEnd_7869930 449006311915388788486873 := by
  unfold tailWord_7869930
  simp only [CollatzResearch.WordTrace]
  refine ⟨71759982094648790470417811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191359952252396774587780829 71759982094648790470417811)
  ·
    refine ⟨107639973141973185705626717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71759982094648790470417811 107639973141973185705626717)
    ·
      refine ⟨40364989928239944639610019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107639973141973185705626717 40364989928239944639610019)
      ·
        refine ⟨60547484892359916959415029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40364989928239944639610019 60547484892359916959415029)
        ·
          refine ⟨5676326708658742214945159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60547484892359916959415029 5676326708658742214945159)
          ·
            refine ⟨8514490062988113322417739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676326708658742214945159 8514490062988113322417739)
            ·
              refine ⟨12771735094482169983626609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514490062988113322417739 12771735094482169983626609)
              ·
                refine ⟨9578801320861627487719957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12771735094482169983626609 9578801320861627487719957)
                ·
                  refine ⟨449006311915388788486873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9578801320861627487719957 449006311915388788486873)
                  ·
                    rfl

theorem cell23_7869930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_7869930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869930 prefixEnd_7869930 := by exact prefixLift 7869930
  have htrace : WordTrace (prefixWord ++ tailWord_7869930) baseStart_7869930 baseEnd_7869930 := by
    simpa [prefixWord, tailWord_7869930, baseEnd_7869930] using wordTrace_append hprefix tailTrace_7869930
  have hstable : (prefixWord ++ tailWord_7869930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869930).length < 2 ^ (prefixWord ++ tailWord_7869930).sum := by decide
  have hdescent : baseEnd_7869930 < baseStart_7869930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869969 : List Nat := [1, 2, 2, 1, 1, 2, 5, 9]
def baseStart_7869969 : Nat := 118140960795 + 7869969 * 2 ^ 59
def prefixEnd_7869969 : Nat := 4983230072969 + 3 ^ 40 * 7869969 * 2
def baseEnd_7869969 : Nat := 149669512332741646066451

theorem tailTrace_7869969 : CollatzResearch.WordTrace tailWord_7869969 prefixEnd_7869969 149669512332741646066451 := by
  unfold tailWord_7869969
  simp only [CollatzResearch.WordTrace]
  refine ⟨287041350825453871542340961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191360900550302581028227307 287041350825453871542340961)
  ·
    refine ⟨215281013119090403656755721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287041350825453871542340961 215281013119090403656755721)
    ·
      refine ⟨161460759839317802742566791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215281013119090403656755721 161460759839317802742566791)
      ·
        refine ⟨242191139758976704113850187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161460759839317802742566791 242191139758976704113850187)
        ·
          refine ⟨363286709638465056170775281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242191139758976704113850187 363286709638465056170775281)
          ·
            refine ⟨272465032228848792128081461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363286709638465056170775281 272465032228848792128081461)
            ·
              refine ⟨25543596771454574262007637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272465032228848792128081461 25543596771454574262007637)
              ·
                refine ⟨149669512332741646066451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25543596771454574262007637 149669512332741646066451)
                ·
                  rfl

theorem cell23_7869969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 9].length) (baseStart_7869969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869969 prefixEnd_7869969 := by exact prefixLift 7869969
  have htrace : WordTrace (prefixWord ++ tailWord_7869969) baseStart_7869969 baseEnd_7869969 := by
    simpa [prefixWord, tailWord_7869969, baseEnd_7869969] using wordTrace_append hprefix tailTrace_7869969
  have hstable : (prefixWord ++ tailWord_7869969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869969).length < 2 ^ (prefixWord ++ tailWord_7869969).sum := by decide
  have hdescent : baseEnd_7869969 < baseStart_7869969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7869983 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 3]
def baseStart_7869983 : Nat := 118140960795 + 7869983 * 2 ^ 59
def prefixEnd_7869983 : Nat := 4983230072969 + 3 ^ 40 * 7869983 * 2
def baseEnd_7869983 : Nat := 4041084021713187389019113

theorem tailTrace_7869983 : CollatzResearch.WordTrace tailWord_7869983 prefixEnd_7869983 4041084021713187389019113 := by
  unfold tailWord_7869983
  simp only [CollatzResearch.WordTrace]
  refine ⟨287041861447403151933350603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191361240964935434622233735 287041861447403151933350603)
  ·
    refine ⟨430562792171104727900025905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287041861447403151933350603 430562792171104727900025905)
    ·
      refine ⟨322922094128328545925019429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430562792171104727900025905 322922094128328545925019429)
      ·
        refine ⟨60547892649061602360941143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322922094128328545925019429 60547892649061602360941143)
        ·
          refine ⟨90821838973592403541411715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60547892649061602360941143 90821838973592403541411715)
          ·
            refine ⟨136232758460388605312117573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90821838973592403541411715 136232758460388605312117573)
            ·
              refine ⟨25543642211322863496022045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136232758460388605312117573 25543642211322863496022045)
              ·
                refine ⟨9578865829246073811008267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25543642211322863496022045 9578865829246073811008267)
                ·
                  refine ⟨14368298743869110716512401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9578865829246073811008267 14368298743869110716512401)
                  ·
                    refine ⟨10776224057901833037384301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14368298743869110716512401 10776224057901833037384301)
                    ·
                      refine ⟨4041084021713187389019113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10776224057901833037384301 4041084021713187389019113)
                      ·
                        rfl

theorem cell23_7869983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_7869983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7869983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7869983 prefixEnd_7869983 := by exact prefixLift 7869983
  have htrace : WordTrace (prefixWord ++ tailWord_7869983) baseStart_7869983 baseEnd_7869983 := by
    simpa [prefixWord, tailWord_7869983, baseEnd_7869983] using wordTrace_append hprefix tailTrace_7869983
  have hstable : (prefixWord ++ tailWord_7869983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7869983).length < 2 ^ (prefixWord ++ tailWord_7869983).sum := by decide
  have hdescent : baseEnd_7869983 < baseStart_7869983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7869983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870019 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10]
def baseStart_7870019 : Nat := 118140960795 + 7870019 * 2 ^ 59
def prefixEnd_7870019 : Nat := 4983230072969 + 3 ^ 40 * 7870019 * 2
def baseEnd_7870019 : Nat := 4041102507016749248168947

theorem tailTrace_7870019 : CollatzResearch.WordTrace tailWord_7870019 prefixEnd_7870019 4041102507016749248168947 := by
  unfold tailWord_7870019
  simp only [CollatzResearch.WordTrace]
  refine ⟨287043174475272730081661111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191362116316848486721107407 287043174475272730081661111)
  ·
    refine ⟨430564761712909095122491667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287043174475272730081661111 430564761712909095122491667)
    ·
      refine ⟨645847142569363642683737501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430564761712909095122491667 645847142569363642683737501)
      ·
        refine ⟨242192678463511366006401563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645847142569363642683737501 242192678463511366006401563)
        ·
          refine ⟨363289017695267049009602345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242192678463511366006401563 363289017695267049009602345)
          ·
            refine ⟨272466763271450286757201759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363289017695267049009602345 272466763271450286757201759)
            ·
              refine ⟨408700144907175430135802639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272466763271450286757201759 408700144907175430135802639)
              ·
                refine ⟨613050217360763145203703959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408700144907175430135802639 613050217360763145203703959)
                ·
                  refine ⟨919575326041144717805555939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613050217360763145203703959 919575326041144717805555939)
                  ·
                    refine ⟨1379362989061717076708333909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 919575326041144717805555939 1379362989061717076708333909)
                    ·
                      refine ⟨4041102507016749248168947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1379362989061717076708333909 4041102507016749248168947)
                      ·
                        rfl

theorem cell23_7870019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_7870019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870019 prefixEnd_7870019 := by exact prefixLift 7870019
  have htrace : WordTrace (prefixWord ++ tailWord_7870019) baseStart_7870019 baseEnd_7870019 := by
    simpa [prefixWord, tailWord_7870019, baseEnd_7870019] using wordTrace_append hprefix tailTrace_7870019
  have hstable : (prefixWord ++ tailWord_7870019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870019).length < 2 ^ (prefixWord ++ tailWord_7870019).sum := by decide
  have hdescent : baseEnd_7870019 < baseStart_7870019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870103 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_7870103 : Nat := 118140960795 + 7870103 * 2 ^ 59
def prefixEnd_7870103 : Nat := 4983230072969 + 3 ^ 40 * 7870103 * 2
def baseEnd_7870103 : Nat := 4041145639391726919518561

theorem tailTrace_7870103 : CollatzResearch.WordTrace tailWord_7870103 prefixEnd_7870103 4041145639391726919518561 := by
  unfold tailWord_7870103
  simp only [CollatzResearch.WordTrace]
  refine ⟨287046238206968412427718963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191364158804645608285145975 287046238206968412427718963)
  ·
    refine ⟨430569357310452618641578445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287046238206968412427718963 430569357310452618641578445)
    ·
      refine ⟨161463508991419731990591917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430569357310452618641578445 161463508991419731990591917)
      ·
        refine ⟨60548815871782399496471969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161463508991419731990591917 60548815871782399496471969)
        ·
          refine ⟨45411611903836799622353977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60548815871782399496471969 45411611903836799622353977)
          ·
            refine ⟨34058708927877599716765483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45411611903836799622353977 34058708927877599716765483)
            ·
              refine ⟨51088063391816399575148225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34058708927877599716765483 51088063391816399575148225)
              ·
                refine ⟨38316047543862299681361169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51088063391816399575148225 38316047543862299681361169)
                ·
                  refine ⟨28737035657896724761020877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38316047543862299681361169 28737035657896724761020877)
                  ·
                    refine ⟨10776388371711271785382829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28737035657896724761020877 10776388371711271785382829)
                    ·
                      refine ⟨4041145639391726919518561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10776388371711271785382829 4041145639391726919518561)
                      ·
                        rfl

theorem cell23_7870103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_7870103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870103 prefixEnd_7870103 := by exact prefixLift 7870103
  have htrace : WordTrace (prefixWord ++ tailWord_7870103) baseStart_7870103 baseEnd_7870103 := by
    simpa [prefixWord, tailWord_7870103, baseEnd_7870103] using wordTrace_append hprefix tailTrace_7870103
  have hstable : (prefixWord ++ tailWord_7870103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870103).length < 2 ^ (prefixWord ++ tailWord_7870103).sum := by decide
  have hdescent : baseEnd_7870103 < baseStart_7870103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870104 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 2, 2, 2]
def baseStart_7870104 : Nat := 118140960795 + 7870104 * 2 ^ 59
def prefixEnd_7870104 : Nat := 4983230072969 + 3 ^ 40 * 7870104 * 2
def baseEnd_7870104 : Nat := 4041146152872381415606057

theorem tailTrace_7870104 : CollatzResearch.WordTrace tailWord_7870104 prefixEnd_7870104 4041146152872381415606057 := by
  unfold tailWord_7870104
  simp only [CollatzResearch.WordTrace]
  refine ⟨143523137339982394799252683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191364183119976526399003577 143523137339982394799252683)
  ·
    refine ⟨215284706009973592198879025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143523137339982394799252683 215284706009973592198879025)
    ·
      refine ⟨161463529507480194149159269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215284706009973592198879025 161463529507480194149159269)
      ·
        refine ⟨30274411782652536402967363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161463529507480194149159269 30274411782652536402967363)
        ·
          refine ⟨45411617673978804604451045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30274411782652536402967363 45411617673978804604451045)
          ·
            refine ⟨8514678313871025863334571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45411617673978804604451045 8514678313871025863334571)
            ·
              refine ⟨12772017470806538795001857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514678313871025863334571 12772017470806538795001857)
              ·
                refine ⟨9579013103104904096251393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12772017470806538795001857 9579013103104904096251393)
                ·
                  refine ⟨7184259827328678072188545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9579013103104904096251393 7184259827328678072188545)
                  ·
                    refine ⟨5388194870496508554141409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7184259827328678072188545 5388194870496508554141409)
                    ·
                      refine ⟨4041146152872381415606057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388194870496508554141409 4041146152872381415606057)
                      ·
                        rfl

theorem cell23_7870104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_7870104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870104 prefixEnd_7870104 := by exact prefixLift 7870104
  have htrace : WordTrace (prefixWord ++ tailWord_7870104) baseStart_7870104 baseEnd_7870104 := by
    simpa [prefixWord, tailWord_7870104, baseEnd_7870104] using wordTrace_append hprefix tailTrace_7870104
  have hstable : (prefixWord ++ tailWord_7870104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870104).length < 2 ^ (prefixWord ++ tailWord_7870104).sum := by decide
  have hdescent : baseEnd_7870104 < baseStart_7870104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870110 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_7870110 : Nat := 118140960795 + 7870110 * 2 ^ 59
def prefixEnd_7870110 : Nat := 4983230072969 + 3 ^ 40 * 7870110 * 2
def baseEnd_7870110 : Nat := 449016581528478710236781

theorem tailTrace_7870110 : CollatzResearch.WordTrace tailWord_7870110 prefixEnd_7870110 449016581528478710236781 := by
  unfold tailWord_7870110
  simp only [CollatzResearch.WordTrace]
  refine ⟨35880811689742881577902973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191364329011962035082149189 35880811689742881577902973)
  ·
    refine ⟨13455304383653580591713615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35880811689742881577902973 13455304383653580591713615)
    ·
      refine ⟨20182956575480370887570423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455304383653580591713615 20182956575480370887570423)
      ·
        refine ⟨30274434863220556331355635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20182956575480370887570423 30274434863220556331355635)
        ·
          refine ⟨45411652294830834497033453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30274434863220556331355635 45411652294830834497033453)
          ·
            refine ⟨17029369610561562936387545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45411652294830834497033453 17029369610561562936387545)
            ·
              refine ⟨12772027207921172202290659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17029369610561562936387545 12772027207921172202290659)
              ·
                refine ⟨19158040811881758303435989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12772027207921172202290659 19158040811881758303435989)
                ·
                  refine ⟨449016581528478710236781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19158040811881758303435989 449016581528478710236781)
                  ·
                    rfl

theorem cell23_7870110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_7870110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870110 prefixEnd_7870110 := by exact prefixLift 7870110
  have htrace : WordTrace (prefixWord ++ tailWord_7870110) baseStart_7870110 baseEnd_7870110 := by
    simpa [prefixWord, tailWord_7870110, baseEnd_7870110] using wordTrace_append hprefix tailTrace_7870110
  have hstable : (prefixWord ++ tailWord_7870110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870110).length < 2 ^ (prefixWord ++ tailWord_7870110).sum := by decide
  have hdescent : baseEnd_7870110 < baseStart_7870110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870143 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_7870143 : Nat := 118140960795 + 7870143 * 2 ^ 59
def prefixEnd_7870143 : Nat := 4983230072969 + 3 ^ 40 * 7870143 * 2
def baseEnd_7870143 : Nat := 4041166178617906763018377

theorem tailTrace_7870143 : CollatzResearch.WordTrace tailWord_7870143 prefixEnd_7870143 4041166178617906763018377 := by
  unfold tailWord_7870143
  simp only [CollatzResearch.WordTrace]
  refine ⟨287047697126823499259175083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191365131417882332839450055 287047697126823499259175083)
  ·
    refine ⟨430571545690235248888762625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287047697126823499259175083 430571545690235248888762625)
    ·
      refine ⟨322928659267676436666571969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430571545690235248888762625 322928659267676436666571969)
      ·
        refine ⟨242196494450757327499928977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322928659267676436666571969 242196494450757327499928977)
        ·
          refine ⟨181647370838067995624946733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242196494450757327499928977 181647370838067995624946733)
          ·
            refine ⟨68117764064275498359355025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181647370838067995624946733 68117764064275498359355025)
            ·
              refine ⟨51088323048206623769516269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68117764064275498359355025 51088323048206623769516269)
              ·
                refine ⟨19158121143077483913568601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51088323048206623769516269 19158121143077483913568601)
                ·
                  refine ⟨14368590857308112935176451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19158121143077483913568601 14368590857308112935176451)
                  ·
                    refine ⟨21552886285962169402764677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14368590857308112935176451 21552886285962169402764677)
                    ·
                      refine ⟨4041166178617906763018377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21552886285962169402764677 4041166178617906763018377)
                      ·
                        rfl

theorem cell23_7870143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_7870143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870143 prefixEnd_7870143 := by exact prefixLift 7870143
  have htrace : WordTrace (prefixWord ++ tailWord_7870143) baseStart_7870143 baseEnd_7870143 := by
    simpa [prefixWord, tailWord_7870143, baseEnd_7870143] using wordTrace_append hprefix tailTrace_7870143
  have hstable : (prefixWord ++ tailWord_7870143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870143).length < 2 ^ (prefixWord ++ tailWord_7870143).sum := by decide
  have hdescent : baseEnd_7870143 < baseStart_7870143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870157 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_7870157 : Nat := 118140960795 + 7870157 * 2 ^ 59
def prefixEnd_7870157 : Nat := 4983230072969 + 3 ^ 40 * 7870157 * 2
def baseEnd_7870157 : Nat := 1347057789115689902747771

theorem tailTrace_7870157 : CollatzResearch.WordTrace tailWord_7870157 prefixEnd_7870157 1347057789115689902747771 := by
  unfold tailWord_7870157
  simp only [CollatzResearch.WordTrace]
  refine ⟨287048207748772779650184725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191365471832515186433456483 287048207748772779650184725)
  ·
    refine ⟨13455384738223724046102409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287048207748772779650184725 13455384738223724046102409)
    ·
      refine ⟨10091538553667793034576807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13455384738223724046102409 10091538553667793034576807)
      ·
        refine ⟨15137307830501689551865211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091538553667793034576807 15137307830501689551865211)
        ·
          refine ⟨22705961745752534327797817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15137307830501689551865211 22705961745752534327797817)
          ·
            refine ⟨17029471309314400745848363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22705961745752534327797817 17029471309314400745848363)
            ·
              refine ⟨25544206963971601118772545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17029471309314400745848363 25544206963971601118772545)
              ·
                refine ⟨19158155222978700839079409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25544206963971601118772545 19158155222978700839079409)
                ·
                  refine ⟨14368616417234025629309557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19158155222978700839079409 14368616417234025629309557)
                  ·
                    refine ⟨1347057789115689902747771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14368616417234025629309557 1347057789115689902747771)
                    ·
                      rfl

theorem cell23_7870157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_7870157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870157 prefixEnd_7870157 := by exact prefixLift 7870157
  have htrace : WordTrace (prefixWord ++ tailWord_7870157) baseStart_7870157 baseEnd_7870157 := by
    simpa [prefixWord, tailWord_7870157, baseEnd_7870157] using wordTrace_append hprefix tailTrace_7870157
  have hstable : (prefixWord ++ tailWord_7870157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870157).length < 2 ^ (prefixWord ++ tailWord_7870157).sum := by decide
  have hdescent : baseEnd_7870157 < baseStart_7870157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870170 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_7870170 : Nat := 118140960795 + 7870170 * 2 ^ 59
def prefixEnd_7870170 : Nat := 4983230072969 + 3 ^ 40 * 7870170 * 2
def baseEnd_7870170 : Nat := 1347060014198526052460251

theorem tailTrace_7870170 : CollatzResearch.WordTrace tailWord_7870170 prefixEnd_7870170 1347060014198526052460251 := by
  unfold tailWord_7870170
  simp only [CollatzResearch.WordTrace]
  refine ⟨71762170474431420717601991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191365787931817121913605309 71762170474431420717601991)
  ·
    refine ⟨107643255711647131076402987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71762170474431420717601991 107643255711647131076402987)
    ·
      refine ⟨161464883567470696614604481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107643255711647131076402987 161464883567470696614604481)
      ·
        refine ⟨121098662675603022460953361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161464883567470696614604481 121098662675603022460953361)
        ·
          refine ⟨90823997006702266845715021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121098662675603022460953361 90823997006702266845715021)
          ·
            refine ⟨34058998877513350067143133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90823997006702266845715021 34058998877513350067143133)
            ·
              refine ⟨12772124579067506275178675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34058998877513350067143133 12772124579067506275178675)
              ·
                refine ⟨19158186868601259412768013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12772124579067506275178675 19158186868601259412768013)
                ·
                  refine ⟨7184320075725472279788005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19158186868601259412768013 7184320075725472279788005)
                  ·
                    refine ⟨1347060014198526052460251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7184320075725472279788005 1347060014198526052460251)
                    ·
                      rfl

theorem cell23_7870170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_7870170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870170 prefixEnd_7870170 := by exact prefixLift 7870170
  have htrace : WordTrace (prefixWord ++ tailWord_7870170) baseStart_7870170 baseEnd_7870170 := by
    simpa [prefixWord, tailWord_7870170, baseEnd_7870170] using wordTrace_append hprefix tailTrace_7870170
  have hstable : (prefixWord ++ tailWord_7870170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870170).length < 2 ^ (prefixWord ++ tailWord_7870170).sum := by decide
  have hdescent : baseEnd_7870170 < baseStart_7870170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870243 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 1, 6]
def baseStart_7870243 : Nat := 118140960795 + 7870243 * 2 ^ 59
def prefixEnd_7870243 : Nat := 4983230072969 + 3 ^ 40 * 7870243 * 2
def baseEnd_7870243 : Nat := 1347072508894452123922639

theorem tailTrace_7870243 : CollatzResearch.WordTrace tailWord_7870243 prefixEnd_7870243 1347072508894452123922639 := by
  unfold tailWord_7870243
  simp only [CollatzResearch.WordTrace]
  refine ⟨287051344426461216337815383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191367562950974144225210255 287051344426461216337815383)
  ·
    refine ⟨430577016639691824506723075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287051344426461216337815383 430577016639691824506723075)
    ·
      refine ⟨645865524959537736760084613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430577016639691824506723075 645865524959537736760084613)
      ·
        refine ⟨121099785929913325642515865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 645865524959537736760084613 121099785929913325642515865)
        ·
          refine ⟨90824839447434994231886899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121099785929913325642515865 90824839447434994231886899)
          ·
            refine ⟨136237259171152491347830349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90824839447434994231886899 136237259171152491347830349)
            ·
              refine ⟨51088972189182184255436381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136237259171152491347830349 51088972189182184255436381)
              ·
                refine ⟨19158364570943319095788643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51088972189182184255436381 19158364570943319095788643)
                ·
                  refine ⟨28737546856414978643682965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19158364570943319095788643 28737546856414978643682965)
                  ·
                    refine ⟨1347072508894452123922639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28737546856414978643682965 1347072508894452123922639)
                    ·
                      rfl

theorem cell23_7870243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 6].length) (baseStart_7870243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870243 prefixEnd_7870243 := by exact prefixLift 7870243
  have htrace : WordTrace (prefixWord ++ tailWord_7870243) baseStart_7870243 baseEnd_7870243 := by
    simpa [prefixWord, tailWord_7870243, baseEnd_7870243] using wordTrace_append hprefix tailTrace_7870243
  have hstable : (prefixWord ++ tailWord_7870243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870243).length < 2 ^ (prefixWord ++ tailWord_7870243).sum := by decide
  have hdescent : baseEnd_7870243 < baseStart_7870243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870254 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7870254 : Nat := 118140960795 + 7870254 * 2 ^ 59
def prefixEnd_7870254 : Nat := 4983230072969 + 3 ^ 40 * 7870254 * 2
def baseEnd_7870254 : Nat := 4041223174970555828730367

theorem tailTrace_7870254 : CollatzResearch.WordTrace tailWord_7870254 prefixEnd_7870254 4041223174970555828730367 := by
  unfold tailWord_7870254
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881468203677670652058227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191367830419614243477643877 35881468203677670652058227)
  ·
    refine ⟨53822202305516505978087341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35881468203677670652058227 53822202305516505978087341)
    ·
      refine ⟨20183325864568689741782753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53822202305516505978087341 20183325864568689741782753)
      ·
        refine ⟨15137494398426517306337065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20183325864568689741782753 15137494398426517306337065)
        ·
          refine ⟨11353120798819887979752799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15137494398426517306337065 11353120798819887979752799)
          ·
            refine ⟨17029681198229831969629199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11353120798819887979752799 17029681198229831969629199)
            ·
              refine ⟨25544521797344747954443799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17029681198229831969629199 25544521797344747954443799)
              ·
                refine ⟨38316782696017121931665699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25544521797344747954443799 38316782696017121931665699)
                ·
                  refine ⟨57475174044025682897498549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38316782696017121931665699 57475174044025682897498549)
                  ·
                    refine ⟨5388297566627407771640489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57475174044025682897498549 5388297566627407771640489)
                    ·
                      refine ⟨4041223174970555828730367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388297566627407771640489 4041223174970555828730367)
                      ·
                        rfl

theorem cell23_7870254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7870254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870254 prefixEnd_7870254 := by exact prefixLift 7870254
  have htrace : WordTrace (prefixWord ++ tailWord_7870254) baseStart_7870254 baseEnd_7870254 := by
    simpa [prefixWord, tailWord_7870254, baseEnd_7870254] using wordTrace_append hprefix tailTrace_7870254
  have hstable : (prefixWord ++ tailWord_7870254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870254).length < 2 ^ (prefixWord ++ tailWord_7870254).sum := by decide
  have hdescent : baseEnd_7870254 < baseStart_7870254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870261 : List Nat := [1, 3, 3, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_7870261 : Nat := 118140960795 + 7870261 * 2 ^ 59
def prefixEnd_7870261 : Nat := 4983230072969 + 3 ^ 40 * 7870261 * 2
def baseEnd_7870261 : Nat := 4041226769335137301342835

theorem tailTrace_7870261 : CollatzResearch.WordTrace tailWord_7870261 prefixEnd_7870261 4041226769335137301342835 := by
  unfold tailWord_7870261
  simp only [CollatzResearch.WordTrace]
  refine ⟨287052000940396005411970637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191368000626930670274647091 287052000940396005411970637)
  ·
    refine ⟨107644500352648502029488989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287052000940396005411970637 107644500352648502029488989)
    ·
      refine ⟨40366687632243188261058371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107644500352648502029488989 40366687632243188261058371)
      ·
        refine ⟨60550031448364782391587557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40366687632243188261058371 60550031448364782391587557)
        ·
          refine ⟨11353130896568396698422667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60550031448364782391587557 11353130896568396698422667)
          ·
            refine ⟨17029696344852595047634001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11353130896568396698422667 17029696344852595047634001)
            ·
              refine ⟨12772272258639446285725501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17029696344852595047634001 12772272258639446285725501)
              ·
                refine ⟨4789602096989792357147063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12772272258639446285725501 4789602096989792357147063)
                ·
                  refine ⟨7184403145484688535720595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789602096989792357147063 7184403145484688535720595)
                  ·
                    refine ⟨10776604718227032803580893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7184403145484688535720595 10776604718227032803580893)
                    ·
                      refine ⟨4041226769335137301342835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10776604718227032803580893 4041226769335137301342835)
                      ·
                        rfl

theorem cell23_7870261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_7870261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870261 prefixEnd_7870261 := by exact prefixLift 7870261
  have htrace : WordTrace (prefixWord ++ tailWord_7870261) baseStart_7870261 baseEnd_7870261 := by
    simpa [prefixWord, tailWord_7870261, baseEnd_7870261] using wordTrace_append hprefix tailTrace_7870261
  have hstable : (prefixWord ++ tailWord_7870261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870261).length < 2 ^ (prefixWord ++ tailWord_7870261).sum := by decide
  have hdescent : baseEnd_7870261 < baseStart_7870261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870263 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_7870263 : Nat := 118140960795 + 7870263 * 2 ^ 59
def prefixEnd_7870263 : Nat := 4983230072969 + 3 ^ 40 * 7870263 * 2
def baseEnd_7870263 : Nat := 4041227796296446293517825

theorem tailTrace_7870263 : CollatzResearch.WordTrace tailWord_7870263 prefixEnd_7870263 4041227796296446293517825 := by
  unfold tailWord_7870263
  simp only [CollatzResearch.WordTrace]
  refine ⟨287052073886388759753543443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191368049257592506502362295 287052073886388759753543443)
  ·
    refine ⟨430578110829583139630315165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287052073886388759753543443 430578110829583139630315165)
    ·
      refine ⟨161466791561093677361368187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430578110829583139630315165 161466791561093677361368187)
      ·
        refine ⟨242200187341640516042052281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161466791561093677361368187 242200187341640516042052281)
        ·
          refine ⟨181650140506230387031539211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242200187341640516042052281 181650140506230387031539211)
          ·
            refine ⟨272475210759345580547308817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181650140506230387031539211 272475210759345580547308817)
            ·
              refine ⟨204356408069509185410481613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272475210759345580547308817 204356408069509185410481613)
              ·
                refine ⟨76633653026065944528930605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204356408069509185410481613 76633653026065944528930605)
                ·
                  refine ⟨28737619884774729198348977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76633653026065944528930605 28737619884774729198348977)
                  ·
                    refine ⟨21553214913581046898761733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28737619884774729198348977 21553214913581046898761733)
                    ·
                      refine ⟨4041227796296446293517825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21553214913581046898761733 4041227796296446293517825)
                      ·
                        rfl

theorem cell23_7870263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_7870263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870263 prefixEnd_7870263 := by exact prefixLift 7870263
  have htrace : WordTrace (prefixWord ++ tailWord_7870263) baseStart_7870263 baseEnd_7870263 := by
    simpa [prefixWord, tailWord_7870263, baseEnd_7870263] using wordTrace_append hprefix tailTrace_7870263
  have hstable : (prefixWord ++ tailWord_7870263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870263).length < 2 ^ (prefixWord ++ tailWord_7870263).sum := by decide
  have hdescent : baseEnd_7870263 < baseStart_7870263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870278 : List Nat := [6, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7870278 : Nat := 118140960795 + 7870278 * 2 ^ 59
def prefixEnd_7870278 : Nat := 4983230072969 + 3 ^ 40 * 7870278 * 2
def baseEnd_7870278 : Nat := 4041235498506263734830257

theorem tailTrace_7870278 : CollatzResearch.WordTrace tailWord_7870278 prefixEnd_7870278 4041235498506263734830257 := by
  unfold tailWord_7870278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970394405666700541104359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191368413987556278210226325 8970394405666700541104359)
  ·
    refine ⟨13455591608500050811656539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8970394405666700541104359 13455591608500050811656539)
    ·
      refine ⟨20183387412750076217484809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455591608500050811656539 20183387412750076217484809)
      ·
        refine ⟨15137540559562557163113607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20183387412750076217484809 15137540559562557163113607)
        ·
          refine ⟨22706310839343835744670411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15137540559562557163113607 22706310839343835744670411)
          ·
            refine ⟨34059466259015753617005617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22706310839343835744670411 34059466259015753617005617)
            ·
              refine ⟨25544599694261815212754213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34059466259015753617005617 25544599694261815212754213)
              ·
                refine ⟨4789612442674090352391415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25544599694261815212754213 4789612442674090352391415)
                ·
                  refine ⟨7184418664011135528587123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789612442674090352391415 7184418664011135528587123)
                  ·
                    refine ⟨10776627996016703292880685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7184418664011135528587123 10776627996016703292880685)
                    ·
                      refine ⟨4041235498506263734830257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10776627996016703292880685 4041235498506263734830257)
                      ·
                        rfl

theorem cell23_7870278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7870278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870278 prefixEnd_7870278 := by exact prefixLift 7870278
  have htrace : WordTrace (prefixWord ++ tailWord_7870278) baseStart_7870278 baseEnd_7870278 := by
    simpa [prefixWord, tailWord_7870278, baseEnd_7870278] using wordTrace_append hprefix tailTrace_7870278
  have hstable : (prefixWord ++ tailWord_7870278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870278).length < 2 ^ (prefixWord ++ tailWord_7870278).sum := by decide
  have hdescent : baseEnd_7870278 < baseStart_7870278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870283 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 3]
def baseStart_7870283 : Nat := 118140960795 + 7870283 * 2 ^ 59
def prefixEnd_7870283 : Nat := 4983230072969 + 3 ^ 40 * 7870283 * 2
def baseEnd_7870283 : Nat := 4041238065909536215267733

theorem tailTrace_7870283 : CollatzResearch.WordTrace tailWord_7870283 prefixEnd_7870283 4041238065909536215267733 := by
  unfold tailWord_7870283
  simp only [CollatzResearch.WordTrace]
  refine ⟨287052803346316303169271503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191368535564210868779514335 287052803346316303169271503)
  ·
    refine ⟨430579205019474454753907255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287052803346316303169271503 430579205019474454753907255)
    ·
      refine ⟨645868807529211682130860883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430579205019474454753907255 645868807529211682130860883)
      ·
        refine ⟨968803211293817523196291325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645868807529211682130860883 968803211293817523196291325)
        ·
          refine ⟨363301204235181571198609247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968803211293817523196291325 363301204235181571198609247)
          ·
            refine ⟨544951806352772356797913871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363301204235181571198609247 544951806352772356797913871)
            ·
              refine ⟨817427709529158535196870807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544951806352772356797913871 817427709529158535196870807)
              ·
                refine ⟨1226141564293737802795306211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817427709529158535196870807 1226141564293737802795306211)
                ·
                  refine ⟨1839212346440606704192959317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226141564293737802795306211 1839212346440606704192959317)
                  ·
                    refine ⟨10776634842425429907380621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1839212346440606704192959317 10776634842425429907380621)
                    ·
                      refine ⟨4041238065909536215267733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10776634842425429907380621 4041238065909536215267733)
                      ·
                        rfl

theorem cell23_7870283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 3].length) (baseStart_7870283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870283 prefixEnd_7870283 := by exact prefixLift 7870283
  have htrace : WordTrace (prefixWord ++ tailWord_7870283) baseStart_7870283 baseEnd_7870283 := by
    simpa [prefixWord, tailWord_7870283, baseEnd_7870283] using wordTrace_append hprefix tailTrace_7870283
  have hstable : (prefixWord ++ tailWord_7870283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870283).length < 2 ^ (prefixWord ++ tailWord_7870283).sum := by decide
  have hdescent : baseEnd_7870283 < baseStart_7870283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870307 : List Nat := [1, 1, 1, 5, 4, 2, 2, 7]
def baseStart_7870307 : Nat := 118140960795 + 7870307 * 2 ^ 59
def prefixEnd_7870307 : Nat := 4983230072969 + 3 ^ 40 * 7870307 * 2
def baseEnd_7870307 : Nat := 149675940349823856346949

theorem tailTrace_7870307 : CollatzResearch.WordTrace tailWord_7870307 prefixEnd_7870307 149675940349823856346949 := by
  unfold tailWord_7870307
  simp only [CollatzResearch.WordTrace]
  refine ⟨287053678698229355268145175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191369119132152903512096783 287053678698229355268145175)
  ·
    refine ⟨430580518047344032902217763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287053678698229355268145175 430580518047344032902217763)
    ·
      refine ⟨645870777071016049353326645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430580518047344032902217763 645870777071016049353326645)
      ·
        refine ⟨60550385350407754626874373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 645870777071016049353326645 60550385350407754626874373)
        ·
          refine ⟨11353197253201453992538945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60550385350407754626874373 11353197253201453992538945)
          ·
            refine ⟨8514897939901090494404209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11353197253201453992538945 8514897939901090494404209)
            ·
              refine ⟨6386173454925817870803157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8514897939901090494404209 6386173454925817870803157)
              ·
                refine ⟨149675940349823856346949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6386173454925817870803157 149675940349823856346949)
                ·
                  rfl

theorem cell23_7870307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 7].length) (baseStart_7870307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870307 prefixEnd_7870307 := by exact prefixLift 7870307
  have htrace : WordTrace (prefixWord ++ tailWord_7870307) baseStart_7870307 baseEnd_7870307 := by
    simpa [prefixWord, tailWord_7870307, baseEnd_7870307] using wordTrace_append hprefix tailTrace_7870307
  have hstable : (prefixWord ++ tailWord_7870307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870307).length < 2 ^ (prefixWord ++ tailWord_7870307).sum := by decide
  have hdescent : baseEnd_7870307 < baseStart_7870307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870317 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_7870317 : Nat := 118140960795 + 7870317 * 2 ^ 59
def prefixEnd_7870317 : Nat := 4983230072969 + 3 ^ 40 * 7870317 * 2
def baseEnd_7870317 : Nat := 4041255524251789082242577

theorem tailTrace_7870317 : CollatzResearch.WordTrace tailWord_7870317 prefixEnd_7870317 4041255524251789082242577 := by
  unfold tailWord_7870317
  simp only [CollatzResearch.WordTrace]
  refine ⟨287054043428193126976009205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191369362285462084650672803 287054043428193126976009205)
  ·
    refine ⟨26911316571393105654000863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287054043428193126976009205 26911316571393105654000863)
    ·
      refine ⟨40366974857089658481001295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26911316571393105654000863 40366974857089658481001295)
      ·
        refine ⟨60550462285634487721501943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40366974857089658481001295 60550462285634487721501943)
        ·
          refine ⟨90825693428451731582252915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60550462285634487721501943 90825693428451731582252915)
          ·
            refine ⟨136238540142677597373379373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90825693428451731582252915 136238540142677597373379373)
            ·
              refine ⟨51089452553504099015017265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136238540142677597373379373 51089452553504099015017265)
              ·
                refine ⟨38317089415128074261262949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51089452553504099015017265 38317089415128074261262949)
                ·
                  refine ⟨7184454265336513923986803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38317089415128074261262949 7184454265336513923986803)
                  ·
                    refine ⟨10776681398004770885980205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7184454265336513923986803 10776681398004770885980205)
                    ·
                      refine ⟨4041255524251789082242577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10776681398004770885980205 4041255524251789082242577)
                      ·
                        rfl

theorem cell23_7870317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_7870317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870317 prefixEnd_7870317 := by exact prefixLift 7870317
  have htrace : WordTrace (prefixWord ++ tailWord_7870317) baseStart_7870317 baseEnd_7870317 := by
    simpa [prefixWord, tailWord_7870317, baseEnd_7870317] using wordTrace_append hprefix tailTrace_7870317
  have hstable : (prefixWord ++ tailWord_7870317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870317).length < 2 ^ (prefixWord ++ tailWord_7870317).sum := by decide
  have hdescent : baseEnd_7870317 < baseStart_7870317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870318 : List Nat := [4, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7870318 : Nat := 118140960795 + 7870318 * 2 ^ 59
def prefixEnd_7870318 : Nat := 4983230072969 + 3 ^ 40 * 7870318 * 2
def baseEnd_7870318 : Nat := 4041256037732443578330073

theorem tailTrace_7870318 : CollatzResearch.WordTrace tailWord_7870318 prefixEnd_7870318 4041256037732443578330073 := by
  unfold tailWord_7870318
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881759987648688018349451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191369386600793002764530405 35881759987648688018349451)
  ·
    refine ⟨53822639981473032027524177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35881759987648688018349451 53822639981473032027524177)
    ·
      refine ⟨40366979986104774020643133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53822639981473032027524177 40366979986104774020643133)
      ·
        refine ⟨15137617494789290257741175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40366979986104774020643133 15137617494789290257741175)
        ·
          refine ⟨22706426242183935386611763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15137617494789290257741175 22706426242183935386611763)
          ·
            refine ⟨34059639363275903079917645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22706426242183935386611763 34059639363275903079917645)
            ·
              refine ⟨12772364761228463654969117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34059639363275903079917645 12772364761228463654969117)
              ·
                refine ⟨4789636785460673870613419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12772364761228463654969117 4789636785460673870613419)
                ·
                  refine ⟨7184455178191010805920129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789636785460673870613419 7184455178191010805920129)
                  ·
                    refine ⟨5388341383643258104440097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7184455178191010805920129 5388341383643258104440097)
                    ·
                      refine ⟨4041256037732443578330073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388341383643258104440097 4041256037732443578330073)
                      ·
                        rfl

theorem cell23_7870318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7870318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870318 prefixEnd_7870318 := by exact prefixLift 7870318
  have htrace : WordTrace (prefixWord ++ tailWord_7870318) baseStart_7870318 baseEnd_7870318 := by
    simpa [prefixWord, tailWord_7870318, baseEnd_7870318] using wordTrace_append hprefix tailTrace_7870318
  have hstable : (prefixWord ++ tailWord_7870318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870318).length < 2 ^ (prefixWord ++ tailWord_7870318).sum := by decide
  have hdescent : baseEnd_7870318 < baseStart_7870318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870323 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4]
def baseStart_7870323 : Nat := 118140960795 + 7870323 * 2 ^ 59
def prefixEnd_7870323 : Nat := 4983230072969 + 3 ^ 40 * 7870323 * 2
def baseEnd_7870323 : Nat := 4041258605135716058767549

theorem tailTrace_7870323 : CollatzResearch.WordTrace tailWord_7870323 prefixEnd_7870323 4041258605135716058767549 := by
  unfold tailWord_7870323
  simp only [CollatzResearch.WordTrace]
  refine ⟨287054262266171390000727623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191369508177447593333818415 287054262266171390000727623)
  ·
    refine ⟨430581393399257085001091435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287054262266171390000727623 430581393399257085001091435)
    ·
      refine ⟨645872090098885627501637153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430581393399257085001091435 645872090098885627501637153)
      ·
        refine ⟨484404067574164220626227865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645872090098885627501637153 484404067574164220626227865)
        ·
          refine ⟨363303050680623165469670899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484404067574164220626227865 363303050680623165469670899)
          ·
            refine ⟨544954576020934748204506349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363303050680623165469670899 544954576020934748204506349)
            ·
              refine ⟨204357966007850530576689881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544954576020934748204506349 204357966007850530576689881)
              ·
                refine ⟨153268474505887897932517411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204357966007850530576689881 153268474505887897932517411)
                ·
                  refine ⟨229902711758831846898776117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153268474505887897932517411 229902711758831846898776117)
                  ·
                    refine ⟨21553379227390485646760261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229902711758831846898776117 21553379227390485646760261)
                    ·
                      refine ⟨4041258605135716058767549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21553379227390485646760261 4041258605135716058767549)
                      ·
                        rfl

theorem cell23_7870323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_7870323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870323 prefixEnd_7870323 := by exact prefixLift 7870323
  have htrace : WordTrace (prefixWord ++ tailWord_7870323) baseStart_7870323 baseEnd_7870323 := by
    simpa [prefixWord, tailWord_7870323, baseEnd_7870323] using wordTrace_append hprefix tailTrace_7870323
  have hstable : (prefixWord ++ tailWord_7870323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870323).length < 2 ^ (prefixWord ++ tailWord_7870323).sum := by decide
  have hdescent : baseEnd_7870323 < baseStart_7870323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870357 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_7870357 : Nat := 118140960795 + 7870357 * 2 ^ 59
def prefixEnd_7870357 : Nat := 4983230072969 + 3 ^ 40 * 7870357 * 2
def baseEnd_7870357 : Nat := 4041276063477968925742393

theorem tailTrace_7870357 : CollatzResearch.WordTrace tailWord_7870357 prefixEnd_7870357 4041276063477968925742393 := by
  unfold tailWord_7870357
  simp only [CollatzResearch.WordTrace]
  refine ⟨287055502348048213807465325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191370334898698809204976883 287055502348048213807465325)
  ·
    refine ⟨107645813380518080177799497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287055502348048213807465325 107645813380518080177799497)
    ·
      refine ⟨80734360035388560133349623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107645813380518080177799497 80734360035388560133349623)
      ·
        refine ⟨121101540053082840200024435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80734360035388560133349623 121101540053082840200024435)
        ·
          refine ⟨181652310079624260300036653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121101540053082840200024435 181652310079624260300036653)
          ·
            refine ⟨68119616279859097612513745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181652310079624260300036653 68119616279859097612513745)
            ·
              refine ⟨51089712209894323209385309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68119616279859097612513745 51089712209894323209385309)
              ·
                refine ⟨19158642078710371203519491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51089712209894323209385309 19158642078710371203519491)
                ·
                  refine ⟨28737963118065556805279237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19158642078710371203519491 28737963118065556805279237)
                  ·
                    refine ⟨5388368084637291900989857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28737963118065556805279237 5388368084637291900989857)
                    ·
                      refine ⟨4041276063477968925742393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388368084637291900989857 4041276063477968925742393)
                      ·
                        rfl

theorem cell23_7870357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_7870357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870357 prefixEnd_7870357 := by exact prefixLift 7870357
  have htrace : WordTrace (prefixWord ++ tailWord_7870357) baseStart_7870357 baseEnd_7870357 := by
    simpa [prefixWord, tailWord_7870357, baseEnd_7870357] using wordTrace_append hprefix tailTrace_7870357
  have hstable : (prefixWord ++ tailWord_7870357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870357).length < 2 ^ (prefixWord ++ tailWord_7870357).sum := by decide
  have hdescent : baseEnd_7870357 < baseStart_7870357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870410 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_7870410 : Nat := 118140960795 + 7870410 * 2 ^ 59
def prefixEnd_7870410 : Nat := 4983230072969 + 3 ^ 40 * 7870410 * 2
def baseEnd_7870410 : Nat := 1347101092650885739459883

theorem tailTrace_7870410 : CollatzResearch.WordTrace tailWord_7870410 prefixEnd_7870410 1347101092650885739459883 := by
  unfold tailWord_7870410
  simp only [CollatzResearch.WordTrace]
  refine ⟨71764358854214050964786171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191371623611237469239429789 71764358854214050964786171)
  ·
    refine ⟨107646538281321076447179257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71764358854214050964786171 107646538281321076447179257)
    ·
      refine ⟨80734903710990807335384443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107646538281321076447179257 80734903710990807335384443)
      ·
        refine ⟨121102355566486211003076665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80734903710990807335384443 121102355566486211003076665)
        ·
          refine ⟨90826766674864658252307499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121102355566486211003076665 90826766674864658252307499)
          ·
            refine ⟨136240150012296987378461249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90826766674864658252307499 136240150012296987378461249)
            ·
              refine ⟨102180112509222740533845937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136240150012296987378461249 102180112509222740533845937)
              ·
                refine ⟨76635084381917055400384453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102180112509222740533845937 76635084381917055400384453)
                ·
                  refine ⟨14369078321609447887572085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76635084381917055400384453 14369078321609447887572085)
                  ·
                    refine ⟨1347101092650885739459883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14369078321609447887572085 1347101092650885739459883)
                    ·
                      rfl

theorem cell23_7870410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_7870410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870410 prefixEnd_7870410 := by exact prefixLift 7870410
  have htrace : WordTrace (prefixWord ++ tailWord_7870410) baseStart_7870410 baseEnd_7870410 := by
    simpa [prefixWord, tailWord_7870410, baseEnd_7870410] using wordTrace_append hprefix tailTrace_7870410
  have hstable : (prefixWord ++ tailWord_7870410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870410).length < 2 ^ (prefixWord ++ tailWord_7870410).sum := by decide
  have hdescent : baseEnd_7870410 < baseStart_7870410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870447 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 4, 4, 2]
def baseStart_7870447 : Nat := 118140960795 + 7870447 * 2 ^ 59
def prefixEnd_7870447 : Nat := 4983230072969 + 3 ^ 40 * 7870447 * 2
def baseEnd_7870447 : Nat := 4041322276736873573616979

theorem tailTrace_7870447 : CollatzResearch.WordTrace tailWord_7870447 prefixEnd_7870447 4041322276736873573616979 := by
  unfold tailWord_7870447
  simp only [CollatzResearch.WordTrace]
  refine ⟨287058784917722159178241595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191372523278481439452161063 287058784917722159178241595)
  ·
    refine ⟨430588177376583238767362393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287058784917722159178241595 430588177376583238767362393)
    ·
      refine ⟨322941133032437429075521795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430588177376583238767362393 322941133032437429075521795)
      ·
        refine ⟨484411699548656143613282693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322941133032437429075521795 484411699548656143613282693)
        ·
          refine ⟨90827193665373026927490505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484411699548656143613282693 90827193665373026927490505)
          ·
            refine ⟨68120395249029770195617879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90827193665373026927490505 68120395249029770195617879)
            ·
              refine ⟨102180592873544655293426819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68120395249029770195617879 102180592873544655293426819)
              ·
                refine ⟨153270889310316982940140229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102180592873544655293426819 153270889310316982940140229)
                ·
                  refine ⟨28738291745684434301276293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153270889310316982940140229 28738291745684434301276293)
                  ·
                    refine ⟨5388429702315831431489305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28738291745684434301276293 5388429702315831431489305)
                    ·
                      refine ⟨4041322276736873573616979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388429702315831431489305 4041322276736873573616979)
                      ·
                        rfl

theorem cell23_7870447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4, 2].length) (baseStart_7870447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870447 prefixEnd_7870447 := by exact prefixLift 7870447
  have htrace : WordTrace (prefixWord ++ tailWord_7870447) baseStart_7870447 baseEnd_7870447 := by
    simpa [prefixWord, tailWord_7870447, baseEnd_7870447] using wordTrace_append hprefix tailTrace_7870447
  have hstable : (prefixWord ++ tailWord_7870447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870447).length < 2 ^ (prefixWord ++ tailWord_7870447).sum := by decide
  have hdescent : baseEnd_7870447 < baseStart_7870447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870457 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 3, 4]
def baseStart_7870457 : Nat := 118140960795 + 7870457 * 2 ^ 59
def prefixEnd_7870457 : Nat := 4983230072969 + 3 ^ 40 * 7870457 * 2
def baseEnd_7870457 : Nat := 1347109137181139511497311

theorem tailTrace_7870457 : CollatzResearch.WordTrace tailWord_7870457 prefixEnd_7870457 1347109137181139511497311 := by
  unfold tailWord_7870457
  simp only [CollatzResearch.WordTrace]
  refine ⟨287059149647685930886105625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191372766431790620590737083 287059149647685930886105625)
  ·
    refine ⟨215294362235764448164579219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287059149647685930886105625 215294362235764448164579219)
    ·
      refine ⟨322941543353646672246868829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215294362235764448164579219 322941543353646672246868829)
      ·
        refine ⟨121103078757617502092575811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322941543353646672246868829 121103078757617502092575811)
        ·
          refine ⟨181654618136426253138863717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121103078757617502092575811 181654618136426253138863717)
          ·
            refine ⟨34060240900579922463536947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181654618136426253138863717 34060240900579922463536947)
            ·
              refine ⟨51090361350869883695305421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34060240900579922463536947 51090361350869883695305421)
              ·
                refine ⟨19158885506576206385739533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51090361350869883695305421 19158885506576206385739533)
                ·
                  refine ⟨7184582064966077394652325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19158885506576206385739533 7184582064966077394652325)
                  ·
                    refine ⟨1347109137181139511497311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7184582064966077394652325 1347109137181139511497311)
                    ·
                      rfl

theorem cell23_7870457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_7870457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870457 prefixEnd_7870457 := by exact prefixLift 7870457
  have htrace : WordTrace (prefixWord ++ tailWord_7870457) baseStart_7870457 baseEnd_7870457 := by
    simpa [prefixWord, tailWord_7870457, baseEnd_7870457] using wordTrace_append hprefix tailTrace_7870457
  have hstable : (prefixWord ++ tailWord_7870457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870457).length < 2 ^ (prefixWord ++ tailWord_7870457).sum := by decide
  have hdescent : baseEnd_7870457 < baseStart_7870457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870460 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_7870460 : Nat := 118140960795 + 7870460 * 2 ^ 59
def prefixEnd_7870460 : Nat := 4983230072969 + 3 ^ 40 * 7870460 * 2
def baseEnd_7870460 : Nat := 4041328951985382022754419

theorem tailTrace_7870460 : CollatzResearch.WordTrace tailWord_7870460 prefixEnd_7870460 4041328951985382022754419 := by
  unfold tailWord_7870460
  simp only [CollatzResearch.WordTrace]
  refine ⟨143529629533337531199232417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191372839377783374932309889 143529629533337531199232417)
  ·
    refine ⟨107647222150003148399424313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143529629533337531199232417 107647222150003148399424313)
    ·
      refine ⟨80735416612502361299568235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107647222150003148399424313 80735416612502361299568235)
      ·
        refine ⟨121103124918753541949352353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80735416612502361299568235 121103124918753541949352353)
        ·
          refine ⟨90827343689065156462014265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121103124918753541949352353 90827343689065156462014265)
          ·
            refine ⟨68120507766798867346510699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90827343689065156462014265 68120507766798867346510699)
            ·
              refine ⟨102180761650198301019766049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68120507766798867346510699 102180761650198301019766049)
              ·
                refine ⟨76635571237648725764824537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102180761650198301019766049 76635571237648725764824537)
                ·
                  refine ⟨57476678428236544323618403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76635571237648725764824537 57476678428236544323618403)
                  ·
                    refine ⟨86215017642354816485427605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57476678428236544323618403 86215017642354816485427605)
                    ·
                      refine ⟨4041328951985382022754419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86215017642354816485427605 4041328951985382022754419)
                      ·
                        rfl

theorem cell23_7870460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_7870460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870460 prefixEnd_7870460 := by exact prefixLift 7870460
  have htrace : WordTrace (prefixWord ++ tailWord_7870460) baseStart_7870460 baseEnd_7870460 := by
    simpa [prefixWord, tailWord_7870460, baseEnd_7870460] using wordTrace_append hprefix tailTrace_7870460
  have hstable : (prefixWord ++ tailWord_7870460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870460).length < 2 ^ (prefixWord ++ tailWord_7870460).sum := by decide
  have hdescent : baseEnd_7870460 < baseStart_7870460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870507 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 3, 5, 2]
def baseStart_7870507 : Nat := 118140960795 + 7870507 * 2 ^ 59
def prefixEnd_7870507 : Nat := 4983230072969 + 3 ^ 40 * 7870507 * 2
def baseEnd_7870507 : Nat := 4041353085576143338866703

theorem tailTrace_7870507 : CollatzResearch.WordTrace tailWord_7870507 prefixEnd_7870507 4041353085576143338866703 := by
  unfold tailWord_7870507
  simp only [CollatzResearch.WordTrace]
  refine ⟨287060973297504789425425775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191373982198336526283617183 287060973297504789425425775)
  ·
    refine ⟨430591459946257184138138663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287060973297504789425425775 430591459946257184138138663)
    ·
      refine ⟨645887189919385776207207995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430591459946257184138138663 645887189919385776207207995)
      ·
        refine ⟨968830784879078664310811993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645887189919385776207207995 968830784879078664310811993)
        ·
          refine ⟨726623088659308998233108995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968830784879078664310811993 726623088659308998233108995)
          ·
            refine ⟨1089934632988963497349663493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726623088659308998233108995 1089934632988963497349663493)
            ·
              refine ⟨204362743685430655753061905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1089934632988963497349663493 204362743685430655753061905)
              ·
                refine ⟨153272057764072991814796429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204362743685430655753061905 153272057764072991814796429)
                ·
                  refine ⟨57477021661527371930548661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153272057764072991814796429 57477021661527371930548661)
                  ·
                    refine ⟨5388470780768191118488937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57477021661527371930548661 5388470780768191118488937)
                    ·
                      refine ⟨4041353085576143338866703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388470780768191118488937 4041353085576143338866703)
                      ·
                        rfl

theorem cell23_7870507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5, 2].length) (baseStart_7870507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870507 prefixEnd_7870507 := by exact prefixLift 7870507
  have htrace : WordTrace (prefixWord ++ tailWord_7870507) baseStart_7870507 baseEnd_7870507 := by
    simpa [prefixWord, tailWord_7870507, baseEnd_7870507] using wordTrace_append hprefix tailTrace_7870507
  have hstable : (prefixWord ++ tailWord_7870507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870507).length < 2 ^ (prefixWord ++ tailWord_7870507).sum := by decide
  have hdescent : baseEnd_7870507 < baseStart_7870507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870521 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 6]
def baseStart_7870521 : Nat := 118140960795 + 7870521 * 2 ^ 59
def prefixEnd_7870521 : Nat := 4983230072969 + 3 ^ 40 * 7870521 * 2
def baseEnd_7870521 : Nat := 449040030478367364899071

theorem tailTrace_7870521 : CollatzResearch.WordTrace tailWord_7870521 prefixEnd_7870521 449040030478367364899071 := by
  unfold tailWord_7870521
  simp only [CollatzResearch.WordTrace]
  refine ⟨287061483919454069816435417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191374322612969379877623611 287061483919454069816435417)
  ·
    refine ⟨215296112939590552362326563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287061483919454069816435417 215296112939590552362326563)
    ·
      refine ⟨322944169409385828543489845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215296112939590552362326563 322944169409385828543489845)
      ·
        refine ⟨30276015882129921425952173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322944169409385828543489845 30276015882129921425952173)
        ·
          refine ⟨11353505955798720534732065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30276015882129921425952173 11353505955798720534732065)
          ·
            refine ⟨8515129466849040401049049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11353505955798720534732065 8515129466849040401049049)
            ·
              refine ⟨6386347100136780300786787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8515129466849040401049049 6386347100136780300786787)
              ·
                refine ⟨9579520650205170451180181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386347100136780300786787 9579520650205170451180181)
                ·
                  refine ⟨449040030478367364899071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9579520650205170451180181 449040030478367364899071)
                  ·
                    rfl

theorem cell23_7870521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 6].length) (baseStart_7870521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870521 prefixEnd_7870521 := by exact prefixLift 7870521
  have htrace : WordTrace (prefixWord ++ tailWord_7870521) baseStart_7870521 baseEnd_7870521 := by
    simpa [prefixWord, tailWord_7870521, baseEnd_7870521] using wordTrace_append hprefix tailTrace_7870521
  have hstable : (prefixWord ++ tailWord_7870521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870521).length < 2 ^ (prefixWord ++ tailWord_7870521).sum := by decide
  have hdescent : baseEnd_7870521 < baseStart_7870521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870524 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_7870524 : Nat := 118140960795 + 7870524 * 2 ^ 59
def prefixEnd_7870524 : Nat := 4983230072969 + 3 ^ 40 * 7870524 * 2
def baseEnd_7870524 : Nat := 4041361814747269772354125

theorem tailTrace_7870524 : CollatzResearch.WordTrace tailWord_7870524 prefixEnd_7870524 4041361814747269772354125 := by
  unfold tailWord_7870524
  simp only [CollatzResearch.WordTrace]
  refine ⟨143530796669221600664397313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191374395558962134219196417 143530796669221600664397313)
  ·
    refine ⟨107648097501916200498297985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143530796669221600664397313 107648097501916200498297985)
    ·
      refine ⟨80736073126437150373723489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107648097501916200498297985 80736073126437150373723489)
      ·
        refine ⟨60552054844827862780292617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80736073126437150373723489 60552054844827862780292617)
        ·
          refine ⟨45414041133620897085219463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60552054844827862780292617 45414041133620897085219463)
          ·
            refine ⟨68121061700431345627829195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45414041133620897085219463 68121061700431345627829195)
            ·
              refine ⟨102181592550647018441743793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68121061700431345627829195 102181592550647018441743793)
              ·
                refine ⟨76636194412985263831307845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102181592550647018441743793 76636194412985263831307845)
                ·
                  refine ⟨14369286452434736968370221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76636194412985263831307845 14369286452434736968370221)
                  ·
                    refine ⟨5388482419663026363138833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14369286452434736968370221 5388482419663026363138833)
                    ·
                      refine ⟨4041361814747269772354125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388482419663026363138833 4041361814747269772354125)
                      ·
                        rfl

theorem cell23_7870524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_7870524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870524 prefixEnd_7870524 := by exact prefixLift 7870524
  have htrace : WordTrace (prefixWord ++ tailWord_7870524) baseStart_7870524 baseEnd_7870524 := by
    simpa [prefixWord, tailWord_7870524, baseEnd_7870524] using wordTrace_append hprefix tailTrace_7870524
  have hstable : (prefixWord ++ tailWord_7870524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870524).length < 2 ^ (prefixWord ++ tailWord_7870524).sum := by decide
  have hdescent : baseEnd_7870524 < baseStart_7870524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870537 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_7870537 : Nat := 118140960795 + 7870537 * 2 ^ 59
def prefixEnd_7870537 : Nat := 4983230072969 + 3 ^ 40 * 7870537 * 2
def baseEnd_7870537 : Nat := 4041368489995778221491565

theorem tailTrace_7870537 : CollatzResearch.WordTrace tailWord_7870537 prefixEnd_7870537 4041368489995778221491565 := by
  unfold tailWord_7870537
  simp only [CollatzResearch.WordTrace]
  refine ⟨287062067487396104549017865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191374711658264069699345243 287062067487396104549017865)
  ·
    refine ⟨215296550615547078411763399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287062067487396104549017865 215296550615547078411763399)
    ·
      refine ⟨322944825923320617617645099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215296550615547078411763399 322944825923320617617645099)
      ·
        refine ⟨484417238884980926426467649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322944825923320617617645099 484417238884980926426467649)
        ·
          refine ⟨363312929163735694819850737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484417238884980926426467649 363312929163735694819850737)
          ·
            refine ⟨272484696872801771114888053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363312929163735694819850737 272484696872801771114888053)
            ·
              refine ⟨25545440331825166042020755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272484696872801771114888053 25545440331825166042020755)
              ·
                refine ⟨38318160497737749063031133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25545440331825166042020755 38318160497737749063031133)
                ·
                  refine ⟨14369310186651655898636675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38318160497737749063031133 14369310186651655898636675)
                  ·
                    refine ⟨21553965279977483847955013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14369310186651655898636675 21553965279977483847955013)
                    ·
                      refine ⟨4041368489995778221491565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21553965279977483847955013 4041368489995778221491565)
                      ·
                        rfl

theorem cell23_7870537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_7870537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870537 prefixEnd_7870537 := by exact prefixLift 7870537
  have htrace : WordTrace (prefixWord ++ tailWord_7870537) baseStart_7870537 baseEnd_7870537 := by
    simpa [prefixWord, tailWord_7870537, baseEnd_7870537] using wordTrace_append hprefix tailTrace_7870537
  have hstable : (prefixWord ++ tailWord_7870537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870537).length < 2 ^ (prefixWord ++ tailWord_7870537).sum := by decide
  have hdescent : baseEnd_7870537 < baseStart_7870537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870560 : List Nat := [2, 1, 1, 3, 2, 14]
def baseStart_7870560 : Nat := 118140960795 + 7870560 * 2 ^ 59
def prefixEnd_7870560 : Nat := 4983230072969 + 3 ^ 40 * 7870560 * 2
def baseEnd_7870560 : Nat := 16631194650414944985613

theorem tailTrace_7870560 : CollatzResearch.WordTrace tailWord_7870560 prefixEnd_7870560 16631194650414944985613 := by
  unfold tailWord_7870560
  simp only [CollatzResearch.WordTrace]
  refine ⟨143531453183156389738552567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191375270910875186318070089 143531453183156389738552567)
  ·
    refine ⟨215297179774734584607828851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143531453183156389738552567 215297179774734584607828851)
    ·
      refine ⟨322945769662101876911743277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215297179774734584607828851 322945769662101876911743277)
      ·
        refine ⟨121104663623288203841903729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322945769662101876911743277 121104663623288203841903729)
        ·
          refine ⟨90828497717466152881427797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121104663623288203841903729 90828497717466152881427797)
          ·
            refine ⟨16631194650414944985613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 90828497717466152881427797 16631194650414944985613)
            ·
              rfl

theorem cell23_7870560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 14].length) (baseStart_7870560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870560 prefixEnd_7870560 := by exact prefixLift 7870560
  have htrace : WordTrace (prefixWord ++ tailWord_7870560) baseStart_7870560 baseEnd_7870560 := by
    simpa [prefixWord, tailWord_7870560, baseEnd_7870560] using wordTrace_append hprefix tailTrace_7870560
  have hstable : (prefixWord ++ tailWord_7870560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870560).length < 2 ^ (prefixWord ++ tailWord_7870560).sum := by decide
  have hdescent : baseEnd_7870560 < baseStart_7870560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870564 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_7870564 : Nat := 118140960795 + 7870564 * 2 ^ 59
def prefixEnd_7870564 : Nat := 4983230072969 + 3 ^ 40 * 7870564 * 2
def baseEnd_7870564 : Nat := 1347127451324483205284647

theorem tailTrace_7870564 : CollatzResearch.WordTrace tailWord_7870564 prefixEnd_7870564 1347127451324483205284647 := by
  unfold tailWord_7870564
  simp only [CollatzResearch.WordTrace]
  refine ⟨143531526129149144080125373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191375368172198858773500497 143531526129149144080125373)
  ·
    refine ⟨53824322298430929030047015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143531526129149144080125373 53824322298430929030047015)
    ·
      refine ⟨80736483447646393545070523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53824322298430929030047015 80736483447646393545070523)
      ·
        refine ⟨121104725171469590317605785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80736483447646393545070523 121104725171469590317605785)
        ·
          refine ⟨90828543878602192738204339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121104725171469590317605785 90828543878602192738204339)
          ·
            refine ⟨136242815817903289107306509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90828543878602192738204339 136242815817903289107306509)
            ·
              refine ⟨51091055931713733415239941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136242815817903289107306509 51091055931713733415239941)
              ·
                refine ⟨9579572987196325015357489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51091055931713733415239941 9579572987196325015357489)
                ·
                  refine ⟨7184679740397243761518117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9579572987196325015357489 7184679740397243761518117)
                  ·
                    refine ⟨1347127451324483205284647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7184679740397243761518117 1347127451324483205284647)
                    ·
                      rfl

theorem cell23_7870564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_7870564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870564 prefixEnd_7870564 := by exact prefixLift 7870564
  have htrace : WordTrace (prefixWord ++ tailWord_7870564) baseStart_7870564 baseEnd_7870564 := by
    simpa [prefixWord, tailWord_7870564, baseEnd_7870564] using wordTrace_append hprefix tailTrace_7870564
  have hstable : (prefixWord ++ tailWord_7870564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870564).length < 2 ^ (prefixWord ++ tailWord_7870564).sum := by decide
  have hdescent : baseEnd_7870564 < baseStart_7870564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870565 : List Nat := [1, 3, 1, 3, 2, 4, 2, 2, 1, 1, 3]
def baseStart_7870565 : Nat := 118140960795 + 7870565 * 2 ^ 59
def prefixEnd_7870565 : Nat := 4983230072969 + 3 ^ 40 * 7870565 * 2
def baseEnd_7870565 : Nat := 4041382867454104111941437

theorem tailTrace_7870565 : CollatzResearch.WordTrace tailWord_7870565 prefixEnd_7870565 4041382867454104111941437 := by
  unfold tailWord_7870565
  simp only [CollatzResearch.WordTrace]
  refine ⟨287063088731294665331037149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191375392487529776887358099 287063088731294665331037149)
  ·
    refine ⟨107648658274235499499138931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287063088731294665331037149 107648658274235499499138931)
    ·
      refine ⟨161472987411353249248708397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107648658274235499499138931 161472987411353249248708397)
      ·
        refine ⟨60552370279257468468265649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161472987411353249248708397 60552370279257468468265649)
        ·
          refine ⟨45414277709443101351199237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60552370279257468468265649 45414277709443101351199237)
          ·
            refine ⟨8515177070520581503349857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45414277709443101351199237 8515177070520581503349857)
            ·
              refine ⟨6386382802890436127512393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8515177070520581503349857 6386382802890436127512393)
              ·
                refine ⟨4789787102167827095634295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386382802890436127512393 4789787102167827095634295)
                ·
                  refine ⟨7184680653251740643451443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789787102167827095634295 7184680653251740643451443)
                  ·
                    refine ⟨10777020979877610965177165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7184680653251740643451443 10777020979877610965177165)
                    ·
                      refine ⟨4041382867454104111941437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10777020979877610965177165 4041382867454104111941437)
                      ·
                        rfl

theorem cell23_7870565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_7870565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870565 prefixEnd_7870565 := by exact prefixLift 7870565
  have htrace : WordTrace (prefixWord ++ tailWord_7870565) baseStart_7870565 baseEnd_7870565 := by
    simpa [prefixWord, tailWord_7870565, baseEnd_7870565] using wordTrace_append hprefix tailTrace_7870565
  have hstable : (prefixWord ++ tailWord_7870565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870565).length < 2 ^ (prefixWord ++ tailWord_7870565).sum := by decide
  have hdescent : baseEnd_7870565 < baseStart_7870565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870567 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_7870567 : Nat := 118140960795 + 7870567 * 2 ^ 59
def prefixEnd_7870567 : Nat := 4983230072969 + 3 ^ 40 * 7870567 * 2
def baseEnd_7870567 : Nat := 4041383894415413104116427

theorem tailTrace_7870567 : CollatzResearch.WordTrace tailWord_7870567 prefixEnd_7870567 4041383894415413104116427 := by
  unfold tailWord_7870567
  simp only [CollatzResearch.WordTrace]
  refine ⟨287063161677287419672609955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191375441118191613115073303 287063161677287419672609955)
  ·
    refine ⟨430594742515931129508914933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287063161677287419672609955 430594742515931129508914933)
    ·
      refine ⟨40368257110868543391460775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430594742515931129508914933 40368257110868543391460775)
      ·
        refine ⟨60552385666302815087191163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40368257110868543391460775 60552385666302815087191163)
        ·
          refine ⟨90828578499454222630786745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60552385666302815087191163 90828578499454222630786745)
          ·
            refine ⟨68121433874590666973090059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90828578499454222630786745 68121433874590666973090059)
            ·
              refine ⟨102182150811886000459635089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68121433874590666973090059 102182150811886000459635089)
              ·
                refine ⟨76636613108914500344726317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102182150811886000459635089 76636613108914500344726317)
                ·
                  refine ⟨28738729915842937629272369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76636613108914500344726317 28738729915842937629272369)
                  ·
                    refine ⟨21554047436882203221954277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28738729915842937629272369 21554047436882203221954277)
                    ·
                      refine ⟨4041383894415413104116427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21554047436882203221954277 4041383894415413104116427)
                      ·
                        rfl

theorem cell23_7870567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_7870567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870567 prefixEnd_7870567 := by exact prefixLift 7870567
  have htrace : WordTrace (prefixWord ++ tailWord_7870567) baseStart_7870567 baseEnd_7870567 := by
    simpa [prefixWord, tailWord_7870567, baseEnd_7870567] using wordTrace_append hprefix tailTrace_7870567
  have hstable : (prefixWord ++ tailWord_7870567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870567).length < 2 ^ (prefixWord ++ tailWord_7870567).sum := by decide
  have hdescent : baseEnd_7870567 < baseStart_7870567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870574 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_7870574 : Nat := 118140960795 + 7870574 * 2 ^ 59
def prefixEnd_7870574 : Nat := 4983230072969 + 3 ^ 40 * 7870574 * 2
def baseEnd_7870574 : Nat := 4041387488779994576728895

theorem tailTrace_7870574 : CollatzResearch.WordTrace tailWord_7870574 prefixEnd_7870574 4041387488779994576728895 := by
  unfold tailWord_7870574
  simp only [CollatzResearch.WordTrace]
  refine ⟨35882927123532757483514347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191375611325508039912076517 35882927123532757483514347)
  ·
    refine ⟨53824390685299136225271521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35882927123532757483514347 53824390685299136225271521)
    ·
      refine ⟨40368293013974352168953641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53824390685299136225271521 40368293013974352168953641)
      ·
        refine ⟨30276219760480764126715231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40368293013974352168953641 30276219760480764126715231)
        ·
          refine ⟨45414329640721146190072847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30276219760480764126715231 45414329640721146190072847)
          ·
            refine ⟨68121494461081719285109271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45414329640721146190072847 68121494461081719285109271)
            ·
              refine ⟨102182241691622578927663907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68121494461081719285109271 102182241691622578927663907)
              ·
                refine ⟨153273362537433868391495861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102182241691622578927663907 153273362537433868391495861)
                ·
                  refine ⟨14369377737884425161702737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153273362537433868391495861 14369377737884425161702737)
                  ·
                    refine ⟨10777033303413318871277053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14369377737884425161702737 10777033303413318871277053)
                    ·
                      refine ⟨4041387488779994576728895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10777033303413318871277053 4041387488779994576728895)
                      ·
                        rfl

theorem cell23_7870574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_7870574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870574 prefixEnd_7870574 := by exact prefixLift 7870574
  have htrace : WordTrace (prefixWord ++ tailWord_7870574) baseStart_7870574 baseEnd_7870574 := by
    simpa [prefixWord, tailWord_7870574, baseEnd_7870574] using wordTrace_append hprefix tailTrace_7870574
  have hstable : (prefixWord ++ tailWord_7870574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870574).length < 2 ^ (prefixWord ++ tailWord_7870574).sum := by decide
  have hdescent : baseEnd_7870574 < baseStart_7870574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870621 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_7870621 : Nat := 118140960795 + 7870621 * 2 ^ 59
def prefixEnd_7870621 : Nat := 4983230072969 + 3 ^ 40 * 7870621 * 2
def baseEnd_7870621 : Nat := 4041411622370755892841179

theorem tailTrace_7870621 : CollatzResearch.WordTrace tailWord_7870621 prefixEnd_7870621 4041411622370755892841179 := by
  unfold tailWord_7870621
  simp only [CollatzResearch.WordTrace]
  refine ⟨287065131219091786895075717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191376754146061191263383811 287065131219091786895075717)
  ·
    refine ⟨53824712103579710042826697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287065131219091786895075717 53824712103579710042826697)
    ·
      refine ⟨40368534077684782532120023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53824712103579710042826697 40368534077684782532120023)
      ·
        refine ⟨60552801116527173798180035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40368534077684782532120023 60552801116527173798180035)
        ·
          refine ⟨90829201674790760697270053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60552801116527173798180035 90829201674790760697270053)
          ·
            refine ⟨17030475314023267630738135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90829201674790760697270053 17030475314023267630738135)
            ·
              refine ⟨25545712971034901446107203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17030475314023267630738135 25545712971034901446107203)
              ·
                refine ⟨38318569456552352169160805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25545712971034901446107203 38318569456552352169160805)
                ·
                  refine ⟨7184731773103566031717651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38318569456552352169160805 7184731773103566031717651)
                  ·
                    refine ⟨10777097659655349047576477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7184731773103566031717651 10777097659655349047576477)
                    ·
                      refine ⟨4041411622370755892841179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10777097659655349047576477 4041411622370755892841179)
                      ·
                        rfl

theorem cell23_7870621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_7870621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870621 prefixEnd_7870621 := by exact prefixLift 7870621
  have htrace : WordTrace (prefixWord ++ tailWord_7870621) baseStart_7870621 baseEnd_7870621 := by
    simpa [prefixWord, tailWord_7870621, baseEnd_7870621] using wordTrace_append hprefix tailTrace_7870621
  have hstable : (prefixWord ++ tailWord_7870621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870621).length < 2 ^ (prefixWord ++ tailWord_7870621).sum := by decide
  have hdescent : baseEnd_7870621 < baseStart_7870621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870661 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 4, 2, 2]
def baseStart_7870661 : Nat := 118140960795 + 7870661 * 2 ^ 59
def prefixEnd_7870661 : Nat := 4983230072969 + 3 ^ 40 * 7870661 * 2
def baseEnd_7870661 : Nat := 4041432161596935736340995

theorem tailTrace_7870661 : CollatzResearch.WordTrace tailWord_7870661 prefixEnd_7870661 4041432161596935736340995 := by
  unfold tailWord_7870661
  simp only [CollatzResearch.WordTrace]
  refine ⟨287066590138946873726531837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191377726759297915817687891 287066590138946873726531837)
  ·
    refine ⟨107649971302105077647449439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287066590138946873726531837 107649971302105077647449439)
    ·
      refine ⟨161474956953157616471174159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107649971302105077647449439 161474956953157616471174159)
      ·
        refine ⟨242212435429736424706761239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161474956953157616471174159 242212435429736424706761239)
        ·
          refine ⟨363318653144604637060141859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242212435429736424706761239 363318653144604637060141859)
          ·
            refine ⟨544977979716906955590212789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363318653144604637060141859 544977979716906955590212789)
            ·
              refine ⟨51091685598460027086582449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 544977979716906955590212789 51091685598460027086582449)
              ·
                refine ⟨38318764198845020314936837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51091685598460027086582449 38318764198845020314936837)
                ·
                  refine ⟨7184768287283441309050657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38318764198845020314936837 7184768287283441309050657)
                  ·
                    refine ⟨5388576215462580981787993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7184768287283441309050657 5388576215462580981787993)
                    ·
                      refine ⟨4041432161596935736340995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388576215462580981787993 4041432161596935736340995)
                      ·
                        rfl

theorem cell23_7870661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_7870661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870661 prefixEnd_7870661 := by exact prefixLift 7870661
  have htrace : WordTrace (prefixWord ++ tailWord_7870661) baseStart_7870661 baseEnd_7870661 := by
    simpa [prefixWord, tailWord_7870661, baseEnd_7870661] using wordTrace_append hprefix tailTrace_7870661
  have hstable : (prefixWord ++ tailWord_7870661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870661).length < 2 ^ (prefixWord ++ tailWord_7870661).sum := by decide
  have hdescent : baseEnd_7870661 < baseStart_7870661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870695 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7870695 : Nat := 118140960795 + 7870695 * 2 ^ 59
def prefixEnd_7870695 : Nat := 4983230072969 + 3 ^ 40 * 7870695 * 2
def baseEnd_7870695 : Nat := 4041449619939188603315839

theorem tailTrace_7870695 : CollatzResearch.WordTrace tailWord_7870695 prefixEnd_7870695 4041449619939188603315839 := by
  unfold tailWord_7870695
  simp only [CollatzResearch.WordTrace]
  refine ⟨287067830220823697533269539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191378553480549131688846359 287067830220823697533269539)
  ·
    refine ⟨430601745331235546299904309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287067830220823697533269539 430601745331235546299904309)
    ·
      refine ⟨40368913624803332465616029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430601745331235546299904309 40368913624803332465616029)
      ·
        refine ⟨15138342609301249674606011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40368913624803332465616029 15138342609301249674606011)
        ·
          refine ⟨22707513913951874511909017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15138342609301249674606011 22707513913951874511909017)
          ·
            refine ⟨17030635435463905883931763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22707513913951874511909017 17030635435463905883931763)
            ·
              refine ⟨25545953153195858825897645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17030635435463905883931763 25545953153195858825897645)
              ·
                refine ⟨9579732432448447059711617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25545953153195858825897645 9579732432448447059711617)
                ·
                  refine ⟨7184799324336335294783713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9579732432448447059711617 7184799324336335294783713)
                  ·
                    refine ⟨5388599493252251471087785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7184799324336335294783713 5388599493252251471087785)
                    ·
                      refine ⟨4041449619939188603315839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388599493252251471087785 4041449619939188603315839)
                      ·
                        rfl

theorem cell23_7870695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7870695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870695 prefixEnd_7870695 := by exact prefixLift 7870695
  have htrace : WordTrace (prefixWord ++ tailWord_7870695) baseStart_7870695 baseEnd_7870695 := by
    simpa [prefixWord, tailWord_7870695, baseEnd_7870695] using wordTrace_append hprefix tailTrace_7870695
  have hstable : (prefixWord ++ tailWord_7870695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870695).length < 2 ^ (prefixWord ++ tailWord_7870695).sum := by decide
  have hdescent : baseEnd_7870695 < baseStart_7870695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870707 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7]
def baseStart_7870707 : Nat := 118140960795 + 7870707 * 2 ^ 59
def prefixEnd_7870707 : Nat := 4983230072969 + 3 ^ 40 * 7870707 * 2
def baseEnd_7870707 : Nat := 4041455781707042556365783

theorem tailTrace_7870707 : CollatzResearch.WordTrace tailWord_7870707 prefixEnd_7870707 4041455781707042556365783 := by
  unfold tailWord_7870707
  simp only [CollatzResearch.WordTrace]
  refine ⟨287068267896780223582706375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191378845264520149055137583 287068267896780223582706375)
  ·
    refine ⟨430602401845170335374059563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287068267896780223582706375 430602401845170335374059563)
    ·
      refine ⟨645903602767755503061089345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430602401845170335374059563 645903602767755503061089345)
      ·
        refine ⟨484427702075816627295817009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645903602767755503061089345 484427702075816627295817009)
        ·
          refine ⟨363320776556862470471862757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484427702075816627295817009 363320776556862470471862757)
          ·
            refine ⟨68122645604411713213474267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 363320776556862470471862757 68122645604411713213474267)
            ·
              refine ⟨102183968406617569820211401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68122645604411713213474267 102183968406617569820211401)
              ·
                refine ⟨76637976304963177365158551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102183968406617569820211401 76637976304963177365158551)
                ·
                  refine ⟨114956964457444766047737827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76637976304963177365158551 114956964457444766047737827)
                  ·
                    refine ⟨172435446686167149071606741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114956964457444766047737827 172435446686167149071606741)
                    ·
                      refine ⟨4041455781707042556365783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172435446686167149071606741 4041455781707042556365783)
                      ·
                        rfl

theorem cell23_7870707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_7870707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870707 prefixEnd_7870707 := by exact prefixLift 7870707
  have htrace : WordTrace (prefixWord ++ tailWord_7870707) baseStart_7870707 baseEnd_7870707 := by
    simpa [prefixWord, tailWord_7870707, baseEnd_7870707] using wordTrace_append hprefix tailTrace_7870707
  have hstable : (prefixWord ++ tailWord_7870707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870707).length < 2 ^ (prefixWord ++ tailWord_7870707).sum := by decide
  have hdescent : baseEnd_7870707 < baseStart_7870707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870714 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_7870714 : Nat := 118140960795 + 7870714 * 2 ^ 59
def prefixEnd_7870714 : Nat := 4983230072969 + 3 ^ 40 * 7870714 * 2
def baseEnd_7870714 : Nat := 1347153125357208009659417

theorem tailTrace_7870714 : CollatzResearch.WordTrace tailWord_7870714 prefixEnd_7870714 1347153125357208009659417 := by
  unfold tailWord_7870714
  simp only [CollatzResearch.WordTrace]
  refine ⟨71767130801938715944552799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191379015471836575852140797 71767130801938715944552799)
  ·
    refine ⟨107650696202908073916829199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71767130801938715944552799 107650696202908073916829199)
    ·
      refine ⟨161476044304362110875243799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107650696202908073916829199 161476044304362110875243799)
      ·
        refine ⟨242214066456543166312865699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161476044304362110875243799 242214066456543166312865699)
        ·
          refine ⟨363321099684814749469298549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242214066456543166312865699 363321099684814749469298549)
          ·
            refine ⟨34061353095451382762746739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 363321099684814749469298549 34061353095451382762746739)
            ·
              refine ⟨51092029643177074144120109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34061353095451382762746739 51092029643177074144120109)
              ·
                refine ⟨19159511116191402804045041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51092029643177074144120109 19159511116191402804045041)
                ·
                  refine ⟨14369633337143552103033781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19159511116191402804045041 14369633337143552103033781)
                  ·
                    refine ⟨1347153125357208009659417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14369633337143552103033781 1347153125357208009659417)
                    ·
                      rfl

theorem cell23_7870714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_7870714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870714 prefixEnd_7870714 := by exact prefixLift 7870714
  have htrace : WordTrace (prefixWord ++ tailWord_7870714) baseStart_7870714 baseEnd_7870714 := by
    simpa [prefixWord, tailWord_7870714, baseEnd_7870714] using wordTrace_append hprefix tailTrace_7870714
  have hstable : (prefixWord ++ tailWord_7870714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870714).length < 2 ^ (prefixWord ++ tailWord_7870714).sum := by decide
  have hdescent : baseEnd_7870714 < baseStart_7870714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870751 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 1, 6, 2]
def baseStart_7870751 : Nat := 118140960795 + 7870751 * 2 ^ 59
def prefixEnd_7870751 : Nat := 4983230072969 + 3 ^ 40 * 7870751 * 2
def baseEnd_7870751 : Nat := 4041478374855840384215581

theorem tailTrace_7870751 : CollatzResearch.WordTrace tailWord_7870751 prefixEnd_7870751 4041478374855840384215581 := by
  unfold tailWord_7870751
  simp only [CollatzResearch.WordTrace]
  refine ⟨287069872708620819097308107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191379915139080546064872071 287069872708620819097308107)
  ·
    refine ⟨430604809062931228645962161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287069872708620819097308107 430604809062931228645962161)
    ·
      refine ⟨322953606797198421484471621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430604809062931228645962161 322953606797198421484471621)
      ·
        refine ⟨60553801274474704028338429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322953606797198421484471621 60553801274474704028338429)
        ·
          refine ⟨22707675477928014010626911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60553801274474704028338429 22707675477928014010626911)
          ·
            refine ⟨34061513216892021015940367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22707675477928014010626911 34061513216892021015940367)
            ·
              refine ⟨51092269825338031523910551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34061513216892021015940367 51092269825338031523910551)
              ·
                refine ⟨76638404738007047285865827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51092269825338031523910551 76638404738007047285865827)
                ·
                  refine ⟨114957607107010570928798741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76638404738007047285865827 114957607107010570928798741)
                  ·
                    refine ⟨5388637833141120512287441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114957607107010570928798741 5388637833141120512287441)
                    ·
                      refine ⟨4041478374855840384215581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388637833141120512287441 4041478374855840384215581)
                      ·
                        rfl

theorem cell23_7870751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_7870751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870751 prefixEnd_7870751 := by exact prefixLift 7870751
  have htrace : WordTrace (prefixWord ++ tailWord_7870751) baseStart_7870751 baseEnd_7870751 := by
    simpa [prefixWord, tailWord_7870751, baseEnd_7870751] using wordTrace_append hprefix tailTrace_7870751
  have hstable : (prefixWord ++ tailWord_7870751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870751).length < 2 ^ (prefixWord ++ tailWord_7870751).sum := by decide
  have hdescent : baseEnd_7870751 < baseStart_7870751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870765 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7870765 : Nat := 118140960795 + 7870765 * 2 ^ 59
def prefixEnd_7870765 : Nat := 4983230072969 + 3 ^ 40 * 7870765 * 2
def baseEnd_7870765 : Nat := 1347161854528334443146839

theorem tailTrace_7870765 : CollatzResearch.WordTrace tailWord_7870765 prefixEnd_7870765 1347161854528334443146839 := by
  unfold tailWord_7870765
  simp only [CollatzResearch.WordTrace]
  refine ⟨287070383330570099488317749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191380255553713399658878499 287070383330570099488317749)
  ·
    refine ⟨26912848437240946827029789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287070383330570099488317749 26912848437240946827029789)
    ·
      refine ⟨10092318163965355060136171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26912848437240946827029789 10092318163965355060136171)
      ·
        refine ⟨15138477245948032590204257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10092318163965355060136171 15138477245948032590204257)
        ·
          refine ⟨11353857934461024442653193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15138477245948032590204257 11353857934461024442653193)
          ·
            refine ⟨8515393450845768331989895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11353857934461024442653193 8515393450845768331989895)
            ·
              refine ⟨12773090176268652497984843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515393450845768331989895 12773090176268652497984843)
              ·
                refine ⟨19159635264402978746977265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773090176268652497984843 19159635264402978746977265)
                ·
                  refine ⟨14369726448302234060232949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19159635264402978746977265 14369726448302234060232949)
                  ·
                    refine ⟨1347161854528334443146839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14369726448302234060232949 1347161854528334443146839)
                    ·
                      rfl

theorem cell23_7870765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7870765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870765 prefixEnd_7870765 := by exact prefixLift 7870765
  have htrace : WordTrace (prefixWord ++ tailWord_7870765) baseStart_7870765 baseEnd_7870765 := by
    simpa [prefixWord, tailWord_7870765, baseEnd_7870765] using wordTrace_append hprefix tailTrace_7870765
  have hstable : (prefixWord ++ tailWord_7870765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870765).length < 2 ^ (prefixWord ++ tailWord_7870765).sum := by decide
  have hdescent : baseEnd_7870765 < baseStart_7870765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870778 : List Nat := [3, 1, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_7870778 : Nat := 118140960795 + 7870778 * 2 ^ 59
def prefixEnd_7870778 : Nat := 4983230072969 + 3 ^ 40 * 7870778 * 2
def baseEnd_7870778 : Nat := 1347164079611170592859319

theorem tailTrace_7870778 : CollatzResearch.WordTrace tailWord_7870778 prefixEnd_7870778 1347164079611170592859319 := by
  unfold tailWord_7870778
  simp only [CollatzResearch.WordTrace]
  refine ⟨71767714369880750677135247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191380571653015335139027325 71767714369880750677135247)
  ·
    refine ⟨107651571554821126015702871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71767714369880750677135247 107651571554821126015702871)
    ·
      refine ⟨161477357332231689023554307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107651571554821126015702871 161477357332231689023554307)
      ·
        refine ⟨242216035998347533535331461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161477357332231689023554307 242216035998347533535331461)
        ·
          refine ⟨45415506749690162537874649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242216035998347533535331461 45415506749690162537874649)
          ·
            refine ⟨34061630062267621903405987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45415506749690162537874649 34061630062267621903405987)
            ·
              refine ⟨51092445093401432855108981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34061630062267621903405987 51092445093401432855108981)
              ·
                refine ⟨4789916727506384330166467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51092445093401432855108981 4789916727506384330166467)
                ·
                  refine ⟨7184875091259576495249701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789916727506384330166467 7184875091259576495249701)
                  ·
                    refine ⟨1347164079611170592859319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7184875091259576495249701 1347164079611170592859319)
                    ·
                      rfl

theorem cell23_7870778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_7870778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870778 prefixEnd_7870778 := by exact prefixLift 7870778
  have htrace : WordTrace (prefixWord ++ tailWord_7870778) baseStart_7870778 baseEnd_7870778 := by
    simpa [prefixWord, tailWord_7870778, baseEnd_7870778] using wordTrace_append hprefix tailTrace_7870778
  have hstable : (prefixWord ++ tailWord_7870778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870778).length < 2 ^ (prefixWord ++ tailWord_7870778).sum := by decide
  have hdescent : baseEnd_7870778 < baseStart_7870778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870821 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_7870821 : Nat := 118140960795 + 7870821 * 2 ^ 59
def prefixEnd_7870821 : Nat := 4983230072969 + 3 ^ 40 * 7870821 * 2
def baseEnd_7870821 : Nat := 1347171439500551703446753

theorem tailTrace_7870821 : CollatzResearch.WordTrace tailWord_7870821 prefixEnd_7870821 1347171439500551703446753 := by
  unfold tailWord_7870821
  simp only [CollatzResearch.WordTrace]
  refine ⟨287072425818367221052356317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191381617212244814034904211 287072425818367221052356317)
  ·
    refine ⟨107652159681887707894633619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287072425818367221052356317 107652159681887707894633619)
    ·
      refine ⟨161478239522831561841950429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107652159681887707894633619 161478239522831561841950429)
      ·
        refine ⟨60554339821061835690731411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161478239522831561841950429 60554339821061835690731411)
        ·
          refine ⟨90831509731592753536097117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60554339821061835690731411 90831509731592753536097117)
          ·
            refine ⟨34061816149347282576036419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90831509731592753536097117 34061816149347282576036419)
            ·
              refine ⟨51092724224020923864054629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34061816149347282576036419 51092724224020923864054629)
              ·
                refine ⟨9579885792003923224510243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51092724224020923864054629 9579885792003923224510243)
                ·
                  refine ⟨14369828688005884836765365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9579885792003923224510243 14369828688005884836765365)
                  ·
                    refine ⟨1347171439500551703446753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14369828688005884836765365 1347171439500551703446753)
                    ·
                      rfl

theorem cell23_7870821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_7870821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870821 prefixEnd_7870821 := by exact prefixLift 7870821
  have htrace : WordTrace (prefixWord ++ tailWord_7870821) baseStart_7870821 baseEnd_7870821 := by
    simpa [prefixWord, tailWord_7870821, baseEnd_7870821] using wordTrace_append hprefix tailTrace_7870821
  have hstable : (prefixWord ++ tailWord_7870821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870821).length < 2 ^ (prefixWord ++ tailWord_7870821).sum := by decide
  have hdescent : baseEnd_7870821 < baseStart_7870821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870852 : List Nat := [2, 3, 2, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_7870852 : Nat := 118140960795 + 7870852 * 2 ^ 59
def prefixEnd_7870852 : Nat := 4983230072969 + 3 ^ 40 * 7870852 * 2
def baseEnd_7870852 : Nat := 4041530236401944489052617

theorem tailTrace_7870852 : CollatzResearch.WordTrace tailWord_7870852 prefixEnd_7870852 4041530236401944489052617 := by
  unfold tailWord_7870852
  simp only [CollatzResearch.WordTrace]
  refine ⟨143536778240627456673367405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191382370987503275564489873 143536778240627456673367405)
  ·
    refine ⟨53826291840235296252512777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143536778240627456673367405 53826291840235296252512777)
    ·
      refine ⟨40369718880176472189384583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53826291840235296252512777 40369718880176472189384583)
      ·
        refine ⟨60554578320264708284076875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40369718880176472189384583 60554578320264708284076875)
        ·
          refine ⟨90831867480397062426115313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60554578320264708284076875 90831867480397062426115313)
          ·
            refine ⟨68123900610297796819586485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90831867480397062426115313 68123900610297796819586485)
            ·
              refine ⟨6386615682215418451836233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68123900610297796819586485 6386615682215418451836233)
              ·
                refine ⟨4789961761661563838877175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386615682215418451836233 4789961761661563838877175)
                ·
                  refine ⟨7184942642492345758315763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789961761661563838877175 7184942642492345758315763)
                  ·
                    refine ⟨10777413963738518637473645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7184942642492345758315763 10777413963738518637473645)
                    ·
                      refine ⟨4041530236401944489052617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10777413963738518637473645 4041530236401944489052617)
                      ·
                        rfl

theorem cell23_7870852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_7870852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870852 prefixEnd_7870852 := by exact prefixLift 7870852
  have htrace : WordTrace (prefixWord ++ tailWord_7870852) baseStart_7870852 baseEnd_7870852 := by
    simpa [prefixWord, tailWord_7870852, baseEnd_7870852] using wordTrace_append hprefix tailTrace_7870852
  have hstable : (prefixWord ++ tailWord_7870852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870852).length < 2 ^ (prefixWord ++ tailWord_7870852).sum := by decide
  have hdescent : baseEnd_7870852 < baseStart_7870852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870888 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7870888 : Nat := 118140960795 + 7870888 * 2 ^ 59
def prefixEnd_7870888 : Nat := 4983230072969 + 3 ^ 40 * 7870888 * 2
def baseEnd_7870888 : Nat := 4041548721705506348202451

theorem tailTrace_7870888 : CollatzResearch.WordTrace tailWord_7870888 prefixEnd_7870888 4041548721705506348202451 := by
  unfold tailWord_7870888
  simp only [CollatzResearch.WordTrace]
  refine ⟨143537434754562245747522659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191383246339416327663363545 143537434754562245747522659)
  ·
    refine ⟨215306152131843368621283989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143537434754562245747522659 215306152131843368621283989)
    ·
      refine ⟨10092475881180157904122687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215306152131843368621283989 10092475881180157904122687)
      ·
        refine ⟨15138713821770236856184031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10092475881180157904122687 15138713821770236856184031)
        ·
          refine ⟨22708070732655355284276047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15138713821770236856184031 22708070732655355284276047)
          ·
            refine ⟨34062106098983032926414071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22708070732655355284276047 34062106098983032926414071)
            ·
              refine ⟨51093159148474549389621107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34062106098983032926414071 51093159148474549389621107)
              ·
                refine ⟨76639738722711824084431661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51093159148474549389621107 76639738722711824084431661)
                ·
                  refine ⟨28739902021016934031661873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76639738722711824084431661 28739902021016934031661873)
                  ·
                    refine ⟨21554926515762700523746405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28739902021016934031661873 21554926515762700523746405)
                    ·
                      refine ⟨4041548721705506348202451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21554926515762700523746405 4041548721705506348202451)
                      ·
                        rfl

theorem cell23_7870888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7870888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870888 prefixEnd_7870888 := by exact prefixLift 7870888
  have htrace : WordTrace (prefixWord ++ tailWord_7870888) baseStart_7870888 baseEnd_7870888 := by
    simpa [prefixWord, tailWord_7870888, baseEnd_7870888] using wordTrace_append hprefix tailTrace_7870888
  have hstable : (prefixWord ++ tailWord_7870888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870888).length < 2 ^ (prefixWord ++ tailWord_7870888).sum := by decide
  have hdescent : baseEnd_7870888 < baseStart_7870888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870909 : List Nat := [1, 4, 1, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_7870909 : Nat := 118140960795 + 7870909 * 2 ^ 59
def prefixEnd_7870909 : Nat := 4983230072969 + 3 ^ 40 * 7870909 * 2
def baseEnd_7870909 : Nat := 4041559504799250766039855

theorem tailTrace_7870909 : CollatzResearch.WordTrace tailWord_7870909 prefixEnd_7870909 4041559504799250766039855 := by
  unfold tailWord_7870909
  simp only [CollatzResearch.WordTrace]
  refine ⟨287075635442048412081559781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191383756961365608054373187 287075635442048412081559781)
  ·
    refine ⟨53826681645384077265292459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287075635442048412081559781 53826681645384077265292459)
    ·
      refine ⟨80740022468076115897938689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53826681645384077265292459 80740022468076115897938689)
      ·
        refine ⟨60555016851057086923454017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80740022468076115897938689 60555016851057086923454017)
        ·
          refine ⟨45416262638292815192590513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60555016851057086923454017 45416262638292815192590513)
          ·
            refine ⟨34062196978719611394442885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45416262638292815192590513 34062196978719611394442885)
            ·
              refine ⟨6386661933509927136458041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34062196978719611394442885 6386661933509927136458041)
              ·
                refine ⟨4789996450132445352343531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386661933509927136458041 4789996450132445352343531)
                ·
                  refine ⟨7184994675198668028515297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789996450132445352343531 7184994675198668028515297)
                  ·
                    refine ⟨5388746006399001021386473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7184994675198668028515297 5388746006399001021386473)
                    ·
                      refine ⟨4041559504799250766039855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388746006399001021386473 4041559504799250766039855)
                      ·
                        rfl

theorem cell23_7870909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_7870909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870909 prefixEnd_7870909 := by exact prefixLift 7870909
  have htrace : WordTrace (prefixWord ++ tailWord_7870909) baseStart_7870909 baseEnd_7870909 := by
    simpa [prefixWord, tailWord_7870909, baseEnd_7870909] using wordTrace_append hprefix tailTrace_7870909
  have hstable : (prefixWord ++ tailWord_7870909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870909).length < 2 ^ (prefixWord ++ tailWord_7870909).sum := by decide
  have hdescent : baseEnd_7870909 < baseStart_7870909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870941 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7870941 : Nat := 118140960795 + 7870941 * 2 ^ 59
def prefixEnd_7870941 : Nat := 4983230072969 + 3 ^ 40 * 7870941 * 2
def baseEnd_7870941 : Nat := 1347191978726731546946569

theorem tailTrace_7870941 : CollatzResearch.WordTrace tailWord_7870941 prefixEnd_7870941 1347191978726731546946569 := by
  unfold tailWord_7870941
  simp only [CollatzResearch.WordTrace]
  refine ⟨287076802577932481546724677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191384535051954987697816451 287076802577932481546724677)
  ·
    refine ⟨53826900483362340290010877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287076802577932481546724677 53826900483362340290010877)
    ·
      refine ⟨20185087681260877608754079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53826900483362340290010877 20185087681260877608754079)
      ·
        refine ⟨30277631521891316413131119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20185087681260877608754079 30277631521891316413131119)
        ·
          refine ⟨45416447282836974619696679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30277631521891316413131119 45416447282836974619696679)
          ·
            refine ⟨68124670924255461929545019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45416447282836974619696679 68124670924255461929545019)
            ·
              refine ⟨102187006386383192894317529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68124670924255461929545019 102187006386383192894317529)
              ·
                refine ⟨76640254789787394670738147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102187006386383192894317529 76640254789787394670738147)
                ·
                  refine ⟨114960382184681092006107221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76640254789787394670738147 114960382184681092006107221)
                  ·
                    refine ⟨1347191978726731546946569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114960382184681092006107221 1347191978726731546946569)
                    ·
                      rfl

theorem cell23_7870941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7870941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870941 prefixEnd_7870941 := by exact prefixLift 7870941
  have htrace : WordTrace (prefixWord ++ tailWord_7870941) baseStart_7870941 baseEnd_7870941 := by
    simpa [prefixWord, tailWord_7870941, baseEnd_7870941] using wordTrace_append hprefix tailTrace_7870941
  have hstable : (prefixWord ++ tailWord_7870941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870941).length < 2 ^ (prefixWord ++ tailWord_7870941).sum := by decide
  have hdescent : baseEnd_7870941 < baseStart_7870941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870946 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7870946 : Nat := 118140960795 + 7870946 * 2 ^ 59
def prefixEnd_7870946 : Nat := 4983230072969 + 3 ^ 40 * 7870946 * 2
def baseEnd_7870946 : Nat := 4041578503583467121277185

theorem tailTrace_7870946 : CollatzResearch.WordTrace tailWord_7870946 prefixEnd_7870946 4041578503583467121277185 := by
  unfold tailWord_7870946
  simp only [CollatzResearch.WordTrace]
  refine ⟨71769246235728591850164173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191384656628609578267104461 71769246235728591850164173)
  ·
    refine ⟨26913467338398221943811565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71769246235728591850164173 26913467338398221943811565)
    ·
      refine ⟨10092550251899333228929337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26913467338398221943811565 10092550251899333228929337)
      ·
        refine ⟨7569412688924499921697003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10092550251899333228929337 7569412688924499921697003)
        ·
          refine ⟨11354119033386749882545505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7569412688924499921697003 11354119033386749882545505)
          ·
            refine ⟨8515589275040062411909129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11354119033386749882545505 8515589275040062411909129)
            ·
              refine ⟨6386691956280046808931847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8515589275040062411909129 6386691956280046808931847)
              ·
                refine ⟨9580037934420070213397771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386691956280046808931847 9580037934420070213397771)
                ·
                  refine ⟨14370056901630105320096657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9580037934420070213397771 14370056901630105320096657)
                  ·
                    refine ⟨10777542676222578990072493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14370056901630105320096657 10777542676222578990072493)
                    ·
                      refine ⟨4041578503583467121277185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10777542676222578990072493 4041578503583467121277185)
                      ·
                        rfl

theorem cell23_7870946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7870946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870946 prefixEnd_7870946 := by exact prefixLift 7870946
  have htrace : WordTrace (prefixWord ++ tailWord_7870946) baseStart_7870946 baseEnd_7870946 := by
    simpa [prefixWord, tailWord_7870946, baseEnd_7870946] using wordTrace_append hprefix tailTrace_7870946
  have hstable : (prefixWord ++ tailWord_7870946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870946).length < 2 ^ (prefixWord ++ tailWord_7870946).sum := by decide
  have hdescent : baseEnd_7870946 < baseStart_7870946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870951 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7870951 : Nat := 118140960795 + 7870951 * 2 ^ 59
def prefixEnd_7870951 : Nat := 4983230072969 + 3 ^ 40 * 7870951 * 2
def baseEnd_7870951 : Nat := 4041581070986739601714661

theorem tailTrace_7870951 : CollatzResearch.WordTrace tailWord_7870951 prefixEnd_7870951 4041581070986739601714661 := by
  unfold tailWord_7870951
  simp only [CollatzResearch.WordTrace]
  refine ⟨287077167307896253254588707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191384778205264168836392471 287077167307896253254588707)
  ·
    refine ⟨430615750961844379881883061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287077167307896253254588707 430615750961844379881883061)
    ·
      refine ⟨40370226652672910613926537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430615750961844379881883061 40370226652672910613926537)
      ·
        refine ⟨30277669989504682960444903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40370226652672910613926537 30277669989504682960444903)
        ·
          refine ⟨45416504984257024440667355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30277669989504682960444903 45416504984257024440667355)
          ·
            refine ⟨68124757476385536661001033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45416504984257024440667355 68124757476385536661001033)
            ·
              refine ⟨51093568107289152495750775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68124757476385536661001033 51093568107289152495750775)
              ·
                refine ⟨76640352160933728743626163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51093568107289152495750775 76640352160933728743626163)
                ·
                  refine ⟨114960528241400593115439245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76640352160933728743626163 114960528241400593115439245)
                  ·
                    refine ⟨43110198090525222418289717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114960528241400593115439245 43110198090525222418289717)
                    ·
                      refine ⟨4041581070986739601714661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43110198090525222418289717 4041581070986739601714661)
                      ·
                        rfl

theorem cell23_7870951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7870951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870951 prefixEnd_7870951 := by exact prefixLift 7870951
  have htrace : WordTrace (prefixWord ++ tailWord_7870951) baseStart_7870951 baseEnd_7870951 := by
    simpa [prefixWord, tailWord_7870951, baseEnd_7870951] using wordTrace_append hprefix tailTrace_7870951
  have hstable : (prefixWord ++ tailWord_7870951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870951).length < 2 ^ (prefixWord ++ tailWord_7870951).sum := by decide
  have hdescent : baseEnd_7870951 < baseStart_7870951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870952 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_7870952 : Nat := 118140960795 + 7870952 * 2 ^ 59
def prefixEnd_7870952 : Nat := 4983230072969 + 3 ^ 40 * 7870952 * 2
def baseEnd_7870952 : Nat := 4041581584467394097802157

theorem tailTrace_7870952 : CollatzResearch.WordTrace tailWord_7870952 prefixEnd_7870952 4041581584467394097802157 := by
  unfold tailWord_7870952
  simp only [CollatzResearch.WordTrace]
  refine ⟨143538601890446315212687555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191384802520595086950250073 143538601890446315212687555)
  ·
    refine ⟨215307902835669472819031333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143538601890446315212687555 215307902835669472819031333)
    ·
      refine ⟨40370231781688026153568375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215307902835669472819031333 40370231781688026153568375)
      ·
        refine ⟨60555347672532039230352563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40370231781688026153568375 60555347672532039230352563)
        ·
          refine ⟨90833021508798058845528845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60555347672532039230352563 90833021508798058845528845)
          ·
            refine ⟨34062383065799272067073317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90833021508798058845528845 34062383065799272067073317)
            ·
              refine ⟨6386696824837363512576247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34062383065799272067073317 6386696824837363512576247)
              ·
                refine ⟨9580045237256045268864371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386696824837363512576247 9580045237256045268864371)
                ·
                  refine ⟨14370067855884067903296557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9580045237256045268864371 14370067855884067903296557)
                  ·
                    refine ⟨5388775445956525463736209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14370067855884067903296557 5388775445956525463736209)
                    ·
                      refine ⟨4041581584467394097802157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388775445956525463736209 4041581584467394097802157)
                      ·
                        rfl

theorem cell23_7870952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_7870952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870952 prefixEnd_7870952 := by exact prefixLift 7870952
  have htrace : WordTrace (prefixWord ++ tailWord_7870952) baseStart_7870952 baseEnd_7870952 := by
    simpa [prefixWord, tailWord_7870952, baseEnd_7870952] using wordTrace_append hprefix tailTrace_7870952
  have hstable : (prefixWord ++ tailWord_7870952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870952).length < 2 ^ (prefixWord ++ tailWord_7870952).sum := by decide
  have hdescent : baseEnd_7870952 < baseStart_7870952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7870961 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_7870961 : Nat := 118140960795 + 7870961 * 2 ^ 59
def prefixEnd_7870961 : Nat := 4983230072969 + 3 ^ 40 * 7870961 * 2
def baseEnd_7870961 : Nat := 4041586205793284562589615

theorem tailTrace_7870961 : CollatzResearch.WordTrace tailWord_7870961 prefixEnd_7870961 4041586205793284562589615 := by
  unfold tailWord_7870961
  simp only [CollatzResearch.WordTrace]
  refine ⟨287077532037860024962452737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191385021358573349974968491 287077532037860024962452737)
  ·
    refine ⟨215308149028395018721839553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287077532037860024962452737 215308149028395018721839553)
    ·
      refine ⟨161481111771296264041379665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215308149028395018721839553 161481111771296264041379665)
      ·
        refine ⟨121110833828472198031034749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161481111771296264041379665 121110833828472198031034749)
        ·
          refine ⟨45416562685677074261638031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121110833828472198031034749 45416562685677074261638031)
          ·
            refine ⟨68124844028515611392457047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45416562685677074261638031 68124844028515611392457047)
            ·
              refine ⟨102187266042773417088685571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68124844028515611392457047 102187266042773417088685571)
              ·
                refine ⟨153280899064160125633028357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102187266042773417088685571 153280899064160125633028357)
                ·
                  refine ⟨28740168574530023556192817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153280899064160125633028357 28740168574530023556192817)
                  ·
                    refine ⟨21555126430897517667144613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28740168574530023556192817 21555126430897517667144613)
                    ·
                      refine ⟨4041586205793284562589615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21555126430897517667144613 4041586205793284562589615)
                      ·
                        rfl

theorem cell23_7870961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_7870961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7870961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7870961 prefixEnd_7870961 := by exact prefixLift 7870961
  have htrace : WordTrace (prefixWord ++ tailWord_7870961) baseStart_7870961 baseEnd_7870961 := by
    simpa [prefixWord, tailWord_7870961, baseEnd_7870961] using wordTrace_append hprefix tailTrace_7870961
  have hstable : (prefixWord ++ tailWord_7870961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7870961).length < 2 ^ (prefixWord ++ tailWord_7870961).sum := by decide
  have hdescent : baseEnd_7870961 < baseStart_7870961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7870961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871005 : List Nat := [1, 4, 2, 2, 1, 2, 3, 3, 5]
def baseStart_7871005 : Nat := 118140960795 + 7871005 * 2 ^ 59
def prefixEnd_7871005 : Nat := 4983230072969 + 3 ^ 40 * 7871005 * 2
def baseEnd_7871005 : Nat := 449067644326898043382157

theorem tailTrace_7871005 : CollatzResearch.WordTrace tailWord_7871005 prefixEnd_7871005 449067644326898043382157 := by
  unfold tailWord_7871005
  simp only [CollatzResearch.WordTrace]
  refine ⟨287079136849700620477054469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191386091233133746984702979 287079136849700620477054469)
  ·
    refine ⟨53827338159318866339447713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287079136849700620477054469 53827338159318866339447713)
    ·
      refine ⟨40370503619489149754585785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53827338159318866339447713 40370503619489149754585785)
      ·
        refine ⟨30277877714616862315939339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40370503619489149754585785 30277877714616862315939339)
        ·
          refine ⟨45416816571925293473909009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30277877714616862315939339 45416816571925293473909009)
          ·
            refine ⟨34062612428943970105431757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45416816571925293473909009 34062612428943970105431757)
            ·
              refine ⟨12773479660853988789536909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34062612428943970105431757 12773479660853988789536909)
              ·
                refine ⟨4790054872820245796076341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12773479660853988789536909 4790054872820245796076341)
                ·
                  refine ⟨449067644326898043382157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4790054872820245796076341 449067644326898043382157)
                  ·
                    rfl

theorem cell23_7871005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_7871005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871005 prefixEnd_7871005 := by exact prefixLift 7871005
  have htrace : WordTrace (prefixWord ++ tailWord_7871005) baseStart_7871005 baseEnd_7871005 := by
    simpa [prefixWord, tailWord_7871005, baseEnd_7871005] using wordTrace_append hprefix tailTrace_7871005
  have hstable : (prefixWord ++ tailWord_7871005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871005).length < 2 ^ (prefixWord ++ tailWord_7871005).sum := by decide
  have hdescent : baseEnd_7871005 < baseStart_7871005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871018 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_7871018 : Nat := 118140960795 + 7871018 * 2 ^ 59
def prefixEnd_7871018 : Nat := 4983230072969 + 3 ^ 40 * 7871018 * 2
def baseEnd_7871018 : Nat := 1347205158063530279858951

theorem tailTrace_7871018 : CollatzResearch.WordTrace tailWord_7871018 prefixEnd_7871018 1347205158063530279858951 := by
  unfold tailWord_7871018
  simp only [CollatzResearch.WordTrace]
  refine ⟨71769902749663380924319427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191386407332435682464851805 71769902749663380924319427)
  ·
    refine ⟨107654854124495071386479141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71769902749663380924319427 107654854124495071386479141)
    ·
      refine ⟨20185285148342825884964839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107654854124495071386479141 20185285148342825884964839)
      ·
        refine ⟨30277927722514238827447259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20185285148342825884964839 30277927722514238827447259)
        ·
          refine ⟨45416891583771358241170889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30277927722514238827447259 45416891583771358241170889)
          ·
            refine ⟨34062668687828518680878167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45416891583771358241170889 34062668687828518680878167)
            ·
              refine ⟨51094003031742778021317251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34062668687828518680878167 51094003031742778021317251)
              ·
                refine ⟨76641004547614167031975877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51094003031742778021317251 76641004547614167031975877)
                ·
                  refine ⟨14370188352677656318495477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76641004547614167031975877 14370188352677656318495477)
                  ·
                    refine ⟨1347205158063530279858951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14370188352677656318495477 1347205158063530279858951)
                    ·
                      rfl

theorem cell23_7871018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_7871018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871018 prefixEnd_7871018 := by exact prefixLift 7871018
  have htrace : WordTrace (prefixWord ++ tailWord_7871018) baseStart_7871018 baseEnd_7871018 := by
    simpa [prefixWord, tailWord_7871018, baseEnd_7871018] using wordTrace_append hprefix tailTrace_7871018
  have hstable : (prefixWord ++ tailWord_7871018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871018).length < 2 ^ (prefixWord ++ tailWord_7871018).sum := by decide
  have hdescent : baseEnd_7871018 < baseStart_7871018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871022 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_7871022 : Nat := 118140960795 + 7871022 * 2 ^ 59
def prefixEnd_7871022 : Nat := 4983230072969 + 3 ^ 40 * 7871022 * 2
def baseEnd_7871022 : Nat := 449068614234800980436315

theorem tailTrace_7871022 : CollatzResearch.WordTrace tailWord_7871022 prefixEnd_7871022 449068614234800980436315 := by
  unfold tailWord_7871022
  simp only [CollatzResearch.WordTrace]
  refine ⟨35884969611329879047552915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191386504593759354920282213 35884969611329879047552915)
  ·
    refine ⟨53827454416994818571329373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35884969611329879047552915 53827454416994818571329373)
    ·
      refine ⟨20185295406373056964248515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53827454416994818571329373 20185295406373056964248515)
      ·
        refine ⟨30277943109559585446372773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20185295406373056964248515 30277943109559585446372773)
        ·
          refine ⟨5677114333042422271194895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30277943109559585446372773 5677114333042422271194895)
          ·
            refine ⟨8515671499563633406792343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677114333042422271194895 8515671499563633406792343)
            ·
              refine ⟨12773507249345450110188515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515671499563633406792343 12773507249345450110188515)
              ·
                refine ⟨19160260874018175165282773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773507249345450110188515 19160260874018175165282773)
                ·
                  refine ⟨449068614234800980436315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19160260874018175165282773 449068614234800980436315)
                  ·
                    rfl

theorem cell23_7871022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_7871022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871022 prefixEnd_7871022 := by exact prefixLift 7871022
  have htrace : WordTrace (prefixWord ++ tailWord_7871022) baseStart_7871022 baseEnd_7871022 := by
    simpa [prefixWord, tailWord_7871022, baseEnd_7871022] using wordTrace_append hprefix tailTrace_7871022
  have hstable : (prefixWord ++ tailWord_7871022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871022).length < 2 ^ (prefixWord ++ tailWord_7871022).sum := by decide
  have hdescent : baseEnd_7871022 < baseStart_7871022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871048 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 3, 4]
def baseStart_7871048 : Nat := 118140960795 + 7871048 * 2 ^ 59
def prefixEnd_7871048 : Nat := 4983230072969 + 3 ^ 40 * 7871048 * 2
def baseEnd_7871048 : Nat := 1347210292870075240733905

theorem tailTrace_7871048 : CollatzResearch.WordTrace tailWord_7871048 prefixEnd_7871048 1347210292870075240733905 := by
  unfold tailWord_7871048
  simp only [CollatzResearch.WordTrace]
  refine ⟨143540352594272419410434899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191387136792363225880579865 143540352594272419410434899)
  ·
    refine ⟨215310528891408629115652349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143540352594272419410434899 215310528891408629115652349)
    ·
      refine ⟨80741448334278235918369631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215310528891408629115652349 80741448334278235918369631)
      ·
        refine ⟨121112172501417353877554447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80741448334278235918369631 121112172501417353877554447)
        ·
          refine ⟨181668258752126030816331671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121112172501417353877554447 181668258752126030816331671)
          ·
            refine ⟨272502388128189046224497507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181668258752126030816331671 272502388128189046224497507)
            ·
              refine ⟨408753582192283569336746261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272502388128189046224497507 408753582192283569336746261)
              ·
                refine ⟨19160324165263292312659981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 408753582192283569336746261 19160324165263292312659981)
                ·
                  refine ⟨7185121561973734617247493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19160324165263292312659981 7185121561973734617247493)
                  ·
                    refine ⟨1347210292870075240733905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7185121561973734617247493 1347210292870075240733905)
                    ·
                      rfl

theorem cell23_7871048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_7871048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871048 prefixEnd_7871048 := by exact prefixLift 7871048
  have htrace : WordTrace (prefixWord ++ tailWord_7871048) baseStart_7871048 baseEnd_7871048 := by
    simpa [prefixWord, tailWord_7871048, baseEnd_7871048] using wordTrace_append hprefix tailTrace_7871048
  have hstable : (prefixWord ++ tailWord_7871048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871048).length < 2 ^ (prefixWord ++ tailWord_7871048).sum := by decide
  have hdescent : baseEnd_7871048 < baseStart_7871048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871051 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4]
def baseStart_7871051 : Nat := 118140960795 + 7871051 * 2 ^ 59
def prefixEnd_7871051 : Nat := 4983230072969 + 3 ^ 40 * 7871051 * 2
def baseEnd_7871051 : Nat := 4041632419052189210464201

theorem tailTrace_7871051 : CollatzResearch.WordTrace tailWord_7871051 prefixEnd_7871051 4041632419052189210464201 := by
  unfold tailWord_7871051
  simp only [CollatzResearch.WordTrace]
  refine ⟨287080814607533970333229007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191387209738355980222152671 287080814607533970333229007)
  ·
    refine ⟨430621221911300955499843511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287080814607533970333229007 430621221911300955499843511)
    ·
      refine ⟨645931832866951433249765267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430621221911300955499843511 645931832866951433249765267)
      ·
        refine ⟨968897749300427149874647901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645931832866951433249765267 968897749300427149874647901)
        ·
          refine ⟨363336655987660181202992963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968897749300427149874647901 363336655987660181202992963)
          ·
            refine ⟨545004983981490271804489445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363336655987660181202992963 545004983981490271804489445)
            ·
              refine ⟨102188434496529425963341771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545004983981490271804489445 102188434496529425963341771)
              ·
                refine ⟨153282651744794138945012657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102188434496529425963341771 153282651744794138945012657)
                ·
                  refine ⟨114961988808595604208759493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153282651744794138945012657 114961988808595604208759493)
                  ·
                    refine ⟨21555372901611675789142405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114961988808595604208759493 21555372901611675789142405)
                    ·
                      refine ⟨4041632419052189210464201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21555372901611675789142405 4041632419052189210464201)
                      ·
                        rfl

theorem cell23_7871051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_7871051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871051 prefixEnd_7871051 := by exact prefixLift 7871051
  have htrace : WordTrace (prefixWord ++ tailWord_7871051) baseStart_7871051 baseEnd_7871051 := by
    simpa [prefixWord, tailWord_7871051, baseEnd_7871051] using wordTrace_append hprefix tailTrace_7871051
  have hstable : (prefixWord ++ tailWord_7871051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871051).length < 2 ^ (prefixWord ++ tailWord_7871051).sum := by decide
  have hdescent : baseEnd_7871051 < baseStart_7871051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871061 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 10]
def baseStart_7871061 : Nat := 118140960795 + 7871061 * 2 ^ 59
def prefixEnd_7871061 : Nat := 4983230072969 + 3 ^ 40 * 7871061 * 2
def baseEnd_7871061 : Nat := 449070839317637130148795

theorem tailTrace_7871061 : CollatzResearch.WordTrace tailWord_7871061 prefixEnd_7871061 449070839317637130148795 := by
  unfold tailWord_7871061
  simp only [CollatzResearch.WordTrace]
  refine ⟨287081179337497742041093037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191387452891665161360728691 287081179337497742041093037)
  ·
    refine ⟨107655442251561653265409889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287081179337497742041093037 107655442251561653265409889)
    ·
      refine ⟨80741581688671239949057417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107655442251561653265409889 80741581688671239949057417)
      ·
        refine ⟨60556186266503429961793063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80741581688671239949057417 60556186266503429961793063)
        ·
          refine ⟨90834279399755144942689595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60556186266503429961793063 90834279399755144942689595)
          ·
            refine ⟨136251419099632717414034393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90834279399755144942689595 136251419099632717414034393)
            ·
              refine ⟨102188564324724538060525795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136251419099632717414034393 102188564324724538060525795)
              ·
                refine ⟨153282846487086807090788693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102188564324724538060525795 153282846487086807090788693)
                ·
                  refine ⟨449070839317637130148795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153282846487086807090788693 449070839317637130148795)
                  ·
                    rfl

theorem cell23_7871061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_7871061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871061 prefixEnd_7871061 := by exact prefixLift 7871061
  have htrace : WordTrace (prefixWord ++ tailWord_7871061) baseStart_7871061 baseEnd_7871061 := by
    simpa [prefixWord, tailWord_7871061, baseEnd_7871061] using wordTrace_append hprefix tailTrace_7871061
  have hstable : (prefixWord ++ tailWord_7871061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871061).length < 2 ^ (prefixWord ++ tailWord_7871061).sum := by decide
  have hdescent : baseEnd_7871061 < baseStart_7871061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871081 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_7871081 : Nat := 118140960795 + 7871081 * 2 ^ 59
def prefixEnd_7871081 : Nat := 4983230072969 + 3 ^ 40 * 7871081 * 2
def baseEnd_7871081 : Nat := 4041647823471824093089063

theorem tailTrace_7871081 : CollatzResearch.WordTrace tailWord_7871081 prefixEnd_7871081 4041647823471824093089063 := by
  unfold tailWord_7871081
  simp only [CollatzResearch.WordTrace]
  refine ⟨287081908797425285456821097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191387939198283523637880731 287081908797425285456821097)
  ·
    refine ⟨215311431598068964092615823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287081908797425285456821097 215311431598068964092615823)
    ·
      refine ⟨322967147397103446138923735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215311431598068964092615823 322967147397103446138923735)
      ·
        refine ⟨484450721095655169208385603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322967147397103446138923735 484450721095655169208385603)
        ·
          refine ⟨726676081643482753812578405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484450721095655169208385603 726676081643482753812578405)
          ·
            refine ⟨136251765308153016339858451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 726676081643482753812578405 136251765308153016339858451)
            ·
              refine ⟨204377647962229524509787677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136251765308153016339858451 204377647962229524509787677)
              ·
                refine ⟨76641617985836071691170379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204377647962229524509787677 76641617985836071691170379)
                ·
                  refine ⟨114962426978754107536755569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76641617985836071691170379 114962426978754107536755569)
                  ·
                    refine ⟨86221820234065580652566677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114962426978754107536755569 86221820234065580652566677)
                    ·
                      refine ⟨4041647823471824093089063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86221820234065580652566677 4041647823471824093089063)
                      ·
                        rfl

theorem cell23_7871081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_7871081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871081 prefixEnd_7871081 := by exact prefixLift 7871081
  have htrace : WordTrace (prefixWord ++ tailWord_7871081) baseStart_7871081 baseEnd_7871081 := by
    simpa [prefixWord, tailWord_7871081, baseEnd_7871081] using wordTrace_append hprefix tailTrace_7871081
  have hstable : (prefixWord ++ tailWord_7871081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871081).length < 2 ^ (prefixWord ++ tailWord_7871081).sum := by decide
  have hdescent : baseEnd_7871081 < baseStart_7871081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871082 : List Nat := [3, 1, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_7871082 : Nat := 118140960795 + 7871082 * 2 ^ 59
def prefixEnd_7871082 : Nat := 4983230072969 + 3 ^ 40 * 7871082 * 2
def baseEnd_7871082 : Nat := 1347216112317492863058853

theorem tailTrace_7871082 : CollatzResearch.WordTrace tailWord_7871082 prefixEnd_7871082 1347216112317492863058853 := by
  unfold tailWord_7871082
  simp only [CollatzResearch.WordTrace]
  refine ⟨71770486317605415656901875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191387963513614441751738333 71770486317605415656901875)
  ·
    refine ⟨107655729476408123485352813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71770486317605415656901875 107655729476408123485352813)
    ·
      refine ⟨40370898553653046307007305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107655729476408123485352813 40370898553653046307007305)
      ·
        refine ⟨30278173915239784730255479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40370898553653046307007305 30278173915239784730255479)
        ·
          refine ⟨45417260872859677095383219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30278173915239784730255479 45417260872859677095383219)
          ·
            refine ⟨68125891309289515643074829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45417260872859677095383219 68125891309289515643074829)
            ·
              refine ⟨25547209240983568366153061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68125891309289515643074829 25547209240983568366153061)
              ·
                refine ⟨4790101732684419068653699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25547209240983568366153061 4790101732684419068653699)
                ·
                  refine ⟨7185152599026628602980549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790101732684419068653699 7185152599026628602980549)
                  ·
                    refine ⟨1347216112317492863058853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7185152599026628602980549 1347216112317492863058853)
                    ·
                      rfl

theorem cell23_7871082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_7871082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871082 prefixEnd_7871082 := by exact prefixLift 7871082
  have htrace : WordTrace (prefixWord ++ tailWord_7871082) baseStart_7871082 baseEnd_7871082 := by
    simpa [prefixWord, tailWord_7871082, baseEnd_7871082] using wordTrace_append hprefix tailTrace_7871082
  have hstable : (prefixWord ++ tailWord_7871082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871082).length < 2 ^ (prefixWord ++ tailWord_7871082).sum := by decide
  have hdescent : baseEnd_7871082 < baseStart_7871082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871115 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 2, 3, 2]
def baseStart_7871115 : Nat := 118140960795 + 7871115 * 2 ^ 59
def prefixEnd_7871115 : Nat := 4983230072969 + 3 ^ 40 * 7871115 * 2
def baseEnd_7871115 : Nat := 4041665281814076960063907

theorem tailTrace_7871115 : CollatzResearch.WordTrace tailWord_7871115 prefixEnd_7871115 4041665281814076960063907 := by
  unfold tailWord_7871115
  simp only [CollatzResearch.WordTrace]
  refine ⟨287083148879302109263558799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191388765919534739509039199 287083148879302109263558799)
  ·
    refine ⟨430624723318953163895338199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287083148879302109263558799 430624723318953163895338199)
    ·
      refine ⟨645937084978429745843007299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430624723318953163895338199 645937084978429745843007299)
      ·
        refine ⟨968905627467644618764510949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645937084978429745843007299 968905627467644618764510949)
        ·
          refine ⟨181669805150183366018345803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 968905627467644618764510949 181669805150183366018345803)
          ·
            refine ⟨272504707725275049027518705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181669805150183366018345803 272504707725275049027518705)
            ·
              refine ⟨204378530793956286770639029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272504707725275049027518705 204378530793956286770639029)
              ·
                refine ⟨19160487261933401884747409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204378530793956286770639029 19160487261933401884747409)
                ·
                  refine ⟨14370365446450051413560557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19160487261933401884747409 14370365446450051413560557)
                  ·
                    refine ⟨5388887042418769280085209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14370365446450051413560557 5388887042418769280085209)
                    ·
                      refine ⟨4041665281814076960063907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388887042418769280085209 4041665281814076960063907)
                      ·
                        rfl

theorem cell23_7871115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3, 2].length) (baseStart_7871115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871115 prefixEnd_7871115 := by exact prefixLift 7871115
  have htrace : WordTrace (prefixWord ++ tailWord_7871115) baseStart_7871115 baseEnd_7871115 := by
    simpa [prefixWord, tailWord_7871115, baseEnd_7871115] using wordTrace_append hprefix tailTrace_7871115
  have hstable : (prefixWord ++ tailWord_7871115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871115).length < 2 ^ (prefixWord ++ tailWord_7871115).sum := by decide
  have hdescent : baseEnd_7871115 < baseStart_7871115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871121 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 10]
def baseStart_7871121 : Nat := 118140960795 + 7871121 * 2 ^ 59
def prefixEnd_7871121 : Nat := 4983230072969 + 3 ^ 40 * 7871121 * 2
def baseEnd_7871121 : Nat := 1347222787566001312196293

theorem tailTrace_7871121 : CollatzResearch.WordTrace tailWord_7871121 prefixEnd_7871121 1347222787566001312196293 := by
  unfold tailWord_7871121
  simp only [CollatzResearch.WordTrace]
  refine ⟨287083367717280372288277217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191388911811520248192184811 287083367717280372288277217)
  ·
    refine ⟨215312525787960279216207913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287083367717280372288277217 215312525787960279216207913)
    ·
      refine ⟨161484394340970209412155935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215312525787960279216207913 161484394340970209412155935)
      ·
        refine ⟨242226591511455314118233903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161484394340970209412155935 242226591511455314118233903)
        ·
          refine ⟨363339887267182971177350855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242226591511455314118233903 363339887267182971177350855)
          ·
            refine ⟨545009830900774456766026283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363339887267182971177350855 545009830900774456766026283)
            ·
              refine ⟨817514746351161685149039425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545009830900774456766026283 817514746351161685149039425)
              ·
                refine ⟨613136059763371263861779569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817514746351161685149039425 613136059763371263861779569)
                ·
                  refine ⟨459852044822528447896334677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613136059763371263861779569 459852044822528447896334677)
                  ·
                    refine ⟨1347222787566001312196293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 459852044822528447896334677 1347222787566001312196293)
                    ·
                      rfl

theorem cell23_7871121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_7871121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871121 prefixEnd_7871121 := by exact prefixLift 7871121
  have htrace : WordTrace (prefixWord ++ tailWord_7871121) baseStart_7871121 baseEnd_7871121 := by
    simpa [prefixWord, tailWord_7871121, baseEnd_7871121] using wordTrace_append hprefix tailTrace_7871121
  have hstable : (prefixWord ++ tailWord_7871121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871121).length < 2 ^ (prefixWord ++ tailWord_7871121).sum := by decide
  have hdescent : baseEnd_7871121 < baseStart_7871121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871155 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 1, 6]
def baseStart_7871155 : Nat := 118140960795 + 7871155 * 2 ^ 59
def prefixEnd_7871155 : Nat := 4983230072969 + 3 ^ 40 * 7871155 * 2
def baseEnd_7871155 : Nat := 1347228607013418934521241

theorem tailTrace_7871155 : CollatzResearch.WordTrace tailWord_7871155 prefixEnd_7871155 1347228607013418934521241 := by
  unfold tailWord_7871155
  simp only [CollatzResearch.WordTrace]
  refine ⟨287084607799157196095014919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191389738532771464063343279 287084607799157196095014919)
  ·
    refine ⟨430626911698735794142522379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287084607799157196095014919 430626911698735794142522379)
    ·
      refine ⟨645940367548103691213783569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430626911698735794142522379 645940367548103691213783569)
      ·
        refine ⟨484455275661077768410337677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645940367548103691213783569 484455275661077768410337677)
        ·
          refine ⟨181670728372904163153876629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484455275661077768410337677 181670728372904163153876629)
          ·
            refine ⟨8515815392479882647837967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181670728372904163153876629 8515815392479882647837967)
            ·
              refine ⟨12773723088719823971756951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515815392479882647837967 12773723088719823971756951)
              ·
                refine ⟨19160584633079735957635427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773723088719823971756951 19160584633079735957635427)
                ·
                  refine ⟨28740876949619603936453141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19160584633079735957635427 28740876949619603936453141)
                  ·
                    refine ⟨1347228607013418934521241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28740876949619603936453141 1347228607013418934521241)
                    ·
                      rfl

theorem cell23_7871155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 6].length) (baseStart_7871155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871155 prefixEnd_7871155 := by exact prefixLift 7871155
  have htrace : WordTrace (prefixWord ++ tailWord_7871155) baseStart_7871155 baseEnd_7871155 := by
    simpa [prefixWord, tailWord_7871155, baseEnd_7871155] using wordTrace_append hprefix tailTrace_7871155
  have hstable : (prefixWord ++ tailWord_7871155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871155).length < 2 ^ (prefixWord ++ tailWord_7871155).sum := by decide
  have hdescent : baseEnd_7871155 < baseStart_7871155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871162 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2]
def baseStart_7871162 : Nat := 118140960795 + 7871162 * 2 ^ 59
def prefixEnd_7871162 : Nat := 4983230072969 + 3 ^ 40 * 7871162 * 2
def baseEnd_7871162 : Nat := 4041689415404838276176191

theorem tailTrace_7871162 : CollatzResearch.WordTrace tailWord_7871162 prefixEnd_7871162 4041689415404838276176191 := by
  unfold tailWord_7871162
  simp only [CollatzResearch.WordTrace]
  refine ⟨71771215777532959072629935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191389908740087890860346493 71771215777532959072629935)
  ·
    refine ⟨107656823666299438608944903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71771215777532959072629935 107656823666299438608944903)
    ·
      refine ⟨161485235499449157913417355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107656823666299438608944903 161485235499449157913417355)
      ·
        refine ⟨242227853249173736870126033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161485235499449157913417355 242227853249173736870126033)
        ·
          refine ⟨181670889936880302652594525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242227853249173736870126033 181670889936880302652594525)
          ·
            refine ⟨68126583726330113494722947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181670889936880302652594525 68126583726330113494722947)
            ·
              refine ⟨102189875589495170242084421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68126583726330113494722947 102189875589495170242084421)
              ·
                refine ⟨19160601673030344420390829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102189875589495170242084421 19160601673030344420390829)
                ·
                  refine ⟨7185225627386379157646561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19160601673030344420390829 7185225627386379157646561)
                  ·
                    refine ⟨5388919220539784368234921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7185225627386379157646561 5388919220539784368234921)
                    ·
                      refine ⟨4041689415404838276176191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388919220539784368234921 4041689415404838276176191)
                      ·
                        rfl

theorem cell23_7871162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_7871162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871162 prefixEnd_7871162 := by exact prefixLift 7871162
  have htrace : WordTrace (prefixWord ++ tailWord_7871162) baseStart_7871162 baseEnd_7871162 := by
    simpa [prefixWord, tailWord_7871162, baseEnd_7871162] using wordTrace_append hprefix tailTrace_7871162
  have hstable : (prefixWord ++ tailWord_7871162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871162).length < 2 ^ (prefixWord ++ tailWord_7871162).sum := by decide
  have hdescent : baseEnd_7871162 < baseStart_7871162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871168 : List Nat := [2, 1, 1, 2, 4, 3, 1, 9]
def baseStart_7871168 : Nat := 118140960795 + 7871168 * 2 ^ 59
def prefixEnd_7871168 : Nat := 4983230072969 + 3 ^ 40 * 7871168 * 2
def baseEnd_7871168 : Nat := 149692314677361676025969

theorem tailTrace_7871168 : CollatzResearch.WordTrace tailWord_7871168 prefixEnd_7871168 149692314677361676025969 := by
  unfold tailWord_7871168
  simp only [CollatzResearch.WordTrace]
  refine ⟨143542540974055049657619079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191390054632073399543492105 143542540974055049657619079)
  ·
    refine ⟨215313811461082574486428619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143542540974055049657619079 215313811461082574486428619)
    ·
      refine ⟨322970717191623861729642929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215313811461082574486428619 322970717191623861729642929)
      ·
        refine ⟨242228037893717896297232197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322970717191623861729642929 242228037893717896297232197)
        ·
          refine ⟨45417757105072105555731037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242228037893717896297232197 45417757105072105555731037)
          ·
            refine ⟨17031658914402039583399139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45417757105072105555731037 17031658914402039583399139)
            ·
              refine ⟨25547488371603059375098709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17031658914402039583399139 25547488371603059375098709)
              ·
                refine ⟨149692314677361676025969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25547488371603059375098709 149692314677361676025969)
                ·
                  rfl

theorem cell23_7871168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 9].length) (baseStart_7871168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871168 prefixEnd_7871168 := by exact prefixLift 7871168
  have htrace : WordTrace (prefixWord ++ tailWord_7871168) baseStart_7871168 baseEnd_7871168 := by
    simpa [prefixWord, tailWord_7871168, baseEnd_7871168] using wordTrace_append hprefix tailTrace_7871168
  have hstable : (prefixWord ++ tailWord_7871168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871168).length < 2 ^ (prefixWord ++ tailWord_7871168).sum := by decide
  have hdescent : baseEnd_7871168 < baseStart_7871168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871182 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_7871182 : Nat := 118140960795 + 7871182 * 2 ^ 59
def prefixEnd_7871182 : Nat := 4983230072969 + 3 ^ 40 * 7871182 * 2
def baseEnd_7871182 : Nat := 4041699685017928197926099

theorem tailTrace_7871182 : CollatzResearch.WordTrace tailWord_7871182 prefixEnd_7871182 4041699685017928197926099 := by
  unfold tailWord_7871182
  simp only [CollatzResearch.WordTrace]
  refine ⟨35885699071257422463280975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191390395046706253137498533 35885699071257422463280975)
  ·
    refine ⟨53828548606886133694921463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35885699071257422463280975 53828548606886133694921463)
    ·
      refine ⟨80742822910329200542382195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53828548606886133694921463 80742822910329200542382195)
      ·
        refine ⟨121114234365493800813573293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80742822910329200542382195 121114234365493800813573293)
        ·
          refine ⟨45417837887060175305089985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121114234365493800813573293 45417837887060175305089985)
          ·
            refine ⟨34063378415295131478817489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45417837887060175305089985 34063378415295131478817489)
            ·
              refine ⟨25547533811471348609113117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34063378415295131478817489 25547533811471348609113117)
              ·
                refine ⟨9580325179301755728417419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25547533811471348609113117 9580325179301755728417419)
                ·
                  refine ⟨14370487768952633592626129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9580325179301755728417419 14370487768952633592626129)
                  ·
                    refine ⟨10777865826714475194469597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14370487768952633592626129 10777865826714475194469597)
                    ·
                      refine ⟨4041699685017928197926099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10777865826714475194469597 4041699685017928197926099)
                      ·
                        rfl

theorem cell23_7871182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_7871182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871182 prefixEnd_7871182 := by exact prefixLift 7871182
  have htrace : WordTrace (prefixWord ++ tailWord_7871182) baseStart_7871182 baseEnd_7871182 := by
    simpa [prefixWord, tailWord_7871182, baseEnd_7871182] using wordTrace_append hprefix tailTrace_7871182
  have hstable : (prefixWord ++ tailWord_7871182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871182).length < 2 ^ (prefixWord ++ tailWord_7871182).sum := by decide
  have hdescent : baseEnd_7871182 < baseStart_7871182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871196 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7871196 : Nat := 118140960795 + 7871196 * 2 ^ 59
def prefixEnd_7871196 : Nat := 4983230072969 + 3 ^ 40 * 7871196 * 2
def baseEnd_7871196 : Nat := 4041706873747091143151035

theorem tailTrace_7871196 : CollatzResearch.WordTrace tailWord_7871196 prefixEnd_7871196 4041706873747091143151035 := by
  unfold tailWord_7871196
  simp only [CollatzResearch.WordTrace]
  refine ⟨143543051596004330048628721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191390735461339106731504961 143543051596004330048628721)
  ·
    refine ⟨107657288697003247536471541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143543051596004330048628721 107657288697003247536471541)
    ·
      refine ⟨10092870815344054456544207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107657288697003247536471541 10092870815344054456544207)
      ·
        refine ⟨15139306223016081684816311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10092870815344054456544207 15139306223016081684816311)
        ·
          refine ⟨22708959334524122527224467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15139306223016081684816311 22708959334524122527224467)
          ·
            refine ⟨34063439001786183790836701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22708959334524122527224467 34063439001786183790836701)
            ·
              refine ⟨12773789625669818921563763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34063439001786183790836701 12773789625669818921563763)
              ·
                refine ⟨19160684438504728382345645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773789625669818921563763 19160684438504728382345645)
                ·
                  refine ⟨7185256664439273143379617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19160684438504728382345645 7185256664439273143379617)
                  ·
                    refine ⟨5388942498329454857534713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7185256664439273143379617 5388942498329454857534713)
                    ·
                      refine ⟨4041706873747091143151035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388942498329454857534713 4041706873747091143151035)
                      ·
                        rfl

theorem cell23_7871196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7871196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871196 prefixEnd_7871196 := by exact prefixLift 7871196
  have htrace : WordTrace (prefixWord ++ tailWord_7871196) baseStart_7871196 baseEnd_7871196 := by
    simpa [prefixWord, tailWord_7871196, baseEnd_7871196] using wordTrace_append hprefix tailTrace_7871196
  have hstable : (prefixWord ++ tailWord_7871196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871196).length < 2 ^ (prefixWord ++ tailWord_7871196).sum := by decide
  have hdescent : baseEnd_7871196 < baseStart_7871196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871265 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7871265 : Nat := 118140960795 + 7871265 * 2 ^ 59
def prefixEnd_7871265 : Nat := 4983230072969 + 3 ^ 40 * 7871265 * 2
def baseEnd_7871265 : Nat := 4041742303912251373188217

theorem tailTrace_7871265 : CollatzResearch.WordTrace tailWord_7871265 prefixEnd_7871265 4041742303912251373188217 := by
  unfold tailWord_7871265
  simp only [CollatzResearch.WordTrace]
  refine ⟨287088619828758684881519249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191392413219172456587679499 287088619828758684881519249)
  ·
    refine ⟨215316464871569013661139437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287088619828758684881519249 215316464871569013661139437)
    ·
      refine ⟨80743674326838380122927289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215316464871569013661139437 80743674326838380122927289)
      ·
        refine ⟨60557755745128785092195467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80743674326838380122927289 60557755745128785092195467)
        ·
          refine ⟨90836633617693177638293201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60557755745128785092195467 90836633617693177638293201)
          ·
            refine ⟨68127475213269883228719901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90836633617693177638293201 68127475213269883228719901)
            ·
              refine ⟨25547803204976206210769963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68127475213269883228719901 25547803204976206210769963)
              ·
                refine ⟨38321704807464309316154945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25547803204976206210769963 38321704807464309316154945)
                ·
                  refine ⟨28741278605598231987116209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38321704807464309316154945 28741278605598231987116209)
                  ·
                    refine ⟨21555958954198673990337157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28741278605598231987116209 21555958954198673990337157)
                    ·
                      refine ⟨4041742303912251373188217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21555958954198673990337157 4041742303912251373188217)
                      ·
                        rfl

theorem cell23_7871265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7871265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871265 prefixEnd_7871265 := by exact prefixLift 7871265
  have htrace : WordTrace (prefixWord ++ tailWord_7871265) baseStart_7871265 baseEnd_7871265 := by
    simpa [prefixWord, tailWord_7871265, baseEnd_7871265] using wordTrace_append hprefix tailTrace_7871265
  have hstable : (prefixWord ++ tailWord_7871265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871265).length < 2 ^ (prefixWord ++ tailWord_7871265).sum := by decide
  have hdescent : baseEnd_7871265 < baseStart_7871265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871269 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 2, 2, 2]
def baseStart_7871269 : Nat := 118140960795 + 7871269 * 2 ^ 59
def prefixEnd_7871269 : Nat := 4983230072969 + 3 ^ 40 * 7871269 * 2
def baseEnd_7871269 : Nat := 4041744357834869357538199

theorem tailTrace_7871269 : CollatzResearch.WordTrace tailWord_7871269 prefixEnd_7871269 4041744357834869357538199 := by
  unfold tailWord_7871269
  simp only [CollatzResearch.WordTrace]
  refine ⟨287088765720744193564664861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191392510480496129043109907 287088765720744193564664861)
  ·
    refine ⟨107658287145279072586749323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287088765720744193564664861 107658287145279072586749323)
    ·
      refine ⟨161487430717918608880123985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107658287145279072586749323 161487430717918608880123985)
      ·
        refine ⟨121115573038438956660092989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161487430717918608880123985 121115573038438956660092989)
        ·
          refine ⟨45418339889414608747534871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121115573038438956660092989 45418339889414608747534871)
          ·
            refine ⟨68127509834121913121302307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45418339889414608747534871 68127509834121913121302307)
            ·
              refine ⟨102191264751182869681953461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68127509834121913121302307 102191264751182869681953461)
              ·
                refine ⟨9580431070423394032683137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102191264751182869681953461 9580431070423394032683137)
                ·
                  refine ⟨7185323302817545524512353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9580431070423394032683137 7185323302817545524512353)
                  ·
                    refine ⟨5388992477113159143384265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7185323302817545524512353 5388992477113159143384265)
                    ·
                      refine ⟨4041744357834869357538199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5388992477113159143384265 4041744357834869357538199)
                      ·
                        rfl

theorem cell23_7871269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_7871269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871269 prefixEnd_7871269 := by exact prefixLift 7871269
  have htrace : WordTrace (prefixWord ++ tailWord_7871269) baseStart_7871269 baseEnd_7871269 := by
    simpa [prefixWord, tailWord_7871269, baseEnd_7871269] using wordTrace_append hprefix tailTrace_7871269
  have hstable : (prefixWord ++ tailWord_7871269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871269).length < 2 ^ (prefixWord ++ tailWord_7871269).sum := by decide
  have hdescent : baseEnd_7871269 < baseStart_7871269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871309 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 7]
def baseStart_7871309 : Nat := 118140960795 + 7871309 * 2 ^ 59
def prefixEnd_7871309 : Nat := 4983230072969 + 3 ^ 40 * 7871309 * 2
def baseEnd_7871309 : Nat := 449084988562338800115335

theorem tailTrace_7871309 : CollatzResearch.WordTrace tailWord_7871309 prefixEnd_7871309 449084988562338800115335 := by
  unfold tailWord_7871309
  simp only [CollatzResearch.WordTrace]
  refine ⟨287090224640599280396120981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191393483093732853597413987 287090224640599280396120981)
  ·
    refine ⟨13457354280028091268568171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287090224640599280396120981 13457354280028091268568171)
    ·
      refine ⟨20186031420042136902852257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13457354280028091268568171 20186031420042136902852257)
      ·
        refine ⟨15139523565031602677139193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20186031420042136902852257 15139523565031602677139193)
        ·
          refine ⟨11354642673773702007854395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15139523565031602677139193 11354642673773702007854395)
          ·
            refine ⟨17031964010660553011781593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11354642673773702007854395 17031964010660553011781593)
            ·
              refine ⟨12773973007995414758836195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17031964010660553011781593 12773973007995414758836195)
              ·
                refine ⟨19160959511993122138254293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773973007995414758836195 19160959511993122138254293)
                ·
                  refine ⟨449084988562338800115335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19160959511993122138254293 449084988562338800115335)
                  ·
                    rfl

theorem cell23_7871309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_7871309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871309 prefixEnd_7871309 := by exact prefixLift 7871309
  have htrace : WordTrace (prefixWord ++ tailWord_7871309) baseStart_7871309 baseEnd_7871309 := by
    simpa [prefixWord, tailWord_7871309, baseEnd_7871309] using wordTrace_append hprefix tailTrace_7871309
  have hstable : (prefixWord ++ tailWord_7871309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871309).length < 2 ^ (prefixWord ++ tailWord_7871309).sum := by decide
  have hdescent : baseEnd_7871309 < baseStart_7871309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871365 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 8]
def baseStart_7871365 : Nat := 118140960795 + 7871365 * 2 ^ 59
def prefixEnd_7871365 : Nat := 4983230072969 + 3 ^ 40 * 7871365 * 2
def baseEnd_7871365 : Nat := 449088183553077886881973

theorem tailTrace_7871365 : CollatzResearch.WordTrace tailWord_7871365 prefixEnd_7871365 449088183553077886881973 := by
  unfold tailWord_7871365
  simp only [CollatzResearch.WordTrace]
  refine ⟨287092267128396401960159549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191394844752264267973439699 287092267128396401960159549)
  ·
    refine ⟨107659600173148650735059831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287092267128396401960159549 107659600173148650735059831)
    ·
      refine ⟨161489400259722976102589747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107659600173148650735059831 161489400259722976102589747)
      ·
        refine ⟨242234100389584464153884621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161489400259722976102589747 242234100389584464153884621)
        ·
          refine ⟨90837787646094174057706733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242234100389584464153884621 90837787646094174057706733)
          ·
            refine ⟨34064170367285315271640025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90837787646094174057706733 34064170367285315271640025)
            ·
              refine ⟨25548127775463986453730019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34064170367285315271640025 25548127775463986453730019)
              ·
                refine ⟨38322191663195979680595029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25548127775463986453730019 38322191663195979680595029)
                ·
                  refine ⟨449088183553077886881973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38322191663195979680595029 449088183553077886881973)
                  ·
                    rfl

theorem cell23_7871365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_7871365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871365 prefixEnd_7871365 := by exact prefixLift 7871365
  have htrace : WordTrace (prefixWord ++ tailWord_7871365) baseStart_7871365 baseEnd_7871365 := by
    simpa [prefixWord, tailWord_7871365, baseEnd_7871365] using wordTrace_append hprefix tailTrace_7871365
  have hstable : (prefixWord ++ tailWord_7871365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871365).length < 2 ^ (prefixWord ++ tailWord_7871365).sum := by decide
  have hdescent : baseEnd_7871365 < baseStart_7871365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871369 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 3, 4]
def baseStart_7871369 : Nat := 118140960795 + 7871369 * 2 ^ 59
def prefixEnd_7871369 : Nat := 4983230072969 + 3 ^ 40 * 7871369 * 2
def baseEnd_7871369 : Nat := 1347265235300106322095913

theorem tailTrace_7871369 : CollatzResearch.WordTrace tailWord_7871369 prefixEnd_7871369 1347265235300106322095913 := by
  unfold tailWord_7871369
  simp only [CollatzResearch.WordTrace]
  refine ⟨287092413020381910643305161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191394942013587940428870107 287092413020381910643305161)
  ·
    refine ⟨215319309765286432982478871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287092413020381910643305161 215319309765286432982478871)
    ·
      refine ⟨322978964647929649473718307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215319309765286432982478871 322978964647929649473718307)
      ·
        refine ⟨484468446971894474210577461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322978964647929649473718307 484468446971894474210577461)
        ·
          refine ⟨45418916903615106957241637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 484468446971894474210577461 45418916903615106957241637)
          ·
            refine ⟨8516046919427832554482807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45418916903615106957241637 8516046919427832554482807)
            ·
              refine ⟨12774070379141748831724211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516046919427832554482807 12774070379141748831724211)
              ·
                refine ⟨19161105568712623247586317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12774070379141748831724211 19161105568712623247586317)
                ·
                  refine ⟨7185414588267233717844869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19161105568712623247586317 7185414588267233717844869)
                  ·
                    refine ⟨1347265235300106322095913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7185414588267233717844869 1347265235300106322095913)
                    ·
                      rfl

theorem cell23_7871369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_7871369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871369 prefixEnd_7871369 := by exact prefixLift 7871369
  have htrace : WordTrace (prefixWord ++ tailWord_7871369) baseStart_7871369 baseEnd_7871369 := by
    simpa [prefixWord, tailWord_7871369, baseEnd_7871369] using wordTrace_append hprefix tailTrace_7871369
  have hstable : (prefixWord ++ tailWord_7871369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871369).length < 2 ^ (prefixWord ++ tailWord_7871369).sum := by decide
  have hdescent : baseEnd_7871369 < baseStart_7871369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871453 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7871453 : Nat := 118140960795 + 7871453 * 2 ^ 59
def prefixEnd_7871453 : Nat := 4983230072969 + 3 ^ 40 * 7871453 * 2
def baseEnd_7871453 : Nat := 4041838838275296637637353

theorem tailTrace_7871453 : CollatzResearch.WordTrace tailWord_7871453 prefixEnd_7871453 4041838838275296637637353 := by
  unfold tailWord_7871453
  simp only [CollatzResearch.WordTrace]
  refine ⟨287095476752077592989363013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191396984501385061992908675 287095476752077592989363013)
  ·
    refine ⟨53830401891014548685505565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287095476752077592989363013 53830401891014548685505565)
    ·
      refine ⟨20186400709130455757064587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53830401891014548685505565 20186400709130455757064587)
      ·
        refine ⟨30279601063695683635596881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20186400709130455757064587 30279601063695683635596881)
        ·
          refine ⟨22709700797771762726697661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30279601063695683635596881 22709700797771762726697661)
          ·
            refine ⟨8516137799164411022511623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22709700797771762726697661 8516137799164411022511623)
            ·
              refine ⟨12774206698746616533767435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516137799164411022511623 12774206698746616533767435)
              ·
                refine ⟨19161310048119924800651153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12774206698746616533767435 19161310048119924800651153)
                ·
                  refine ⟨14370982536089943600488365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19161310048119924800651153 14370982536089943600488365)
                  ·
                    refine ⟨5389118451033728850183137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14370982536089943600488365 5389118451033728850183137)
                    ·
                      refine ⟨4041838838275296637637353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389118451033728850183137 4041838838275296637637353)
                      ·
                        rfl

theorem cell23_7871453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7871453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871453 prefixEnd_7871453 := by exact prefixLift 7871453
  have htrace : WordTrace (prefixWord ++ tailWord_7871453) baseStart_7871453 baseEnd_7871453 := by
    simpa [prefixWord, tailWord_7871453, baseEnd_7871453] using wordTrace_append hprefix tailTrace_7871453
  have hstable : (prefixWord ++ tailWord_7871453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871453).length < 2 ^ (prefixWord ++ tailWord_7871453).sum := by decide
  have hdescent : baseEnd_7871453 < baseStart_7871453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871466 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_7871466 : Nat := 118140960795 + 7871466 * 2 ^ 59
def prefixEnd_7871466 : Nat := 4983230072969 + 3 ^ 40 * 7871466 * 2
def baseEnd_7871466 : Nat := 4041845513523805086774793

theorem tailTrace_7871466 : CollatzResearch.WordTrace tailWord_7871466 prefixEnd_7871466 4041845513523805086774793 := by
  unfold tailWord_7871466
  simp only [CollatzResearch.WordTrace]
  refine ⟨71773987725257624052396563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191397300600686997473057501 71773987725257624052396563)
  ·
    refine ⟨107660981587886436078594845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71773987725257624052396563 107660981587886436078594845)
    ·
      refine ⟨40372868095457413529473067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107660981587886436078594845 40372868095457413529473067)
      ·
        refine ⟨60559302143186120294209601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40372868095457413529473067 60559302143186120294209601)
        ·
          refine ⟨45419476607389590220657201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60559302143186120294209601 45419476607389590220657201)
          ·
            refine ⟨34064607455542192665492901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45419476607389590220657201 34064607455542192665492901)
            ·
              refine ⟨6387113897914161124779919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34064607455542192665492901 6387113897914161124779919)
              ·
                refine ⟨9580670846871241687169879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6387113897914161124779919 9580670846871241687169879)
                ·
                  refine ⟨14371006270306862530754819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9580670846871241687169879 14371006270306862530754819)
                  ·
                    refine ⟨21556509405460293796132229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14371006270306862530754819 21556509405460293796132229)
                    ·
                      refine ⟨4041845513523805086774793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21556509405460293796132229 4041845513523805086774793)
                      ·
                        rfl

theorem cell23_7871466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_7871466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871466 prefixEnd_7871466 := by exact prefixLift 7871466
  have htrace : WordTrace (prefixWord ++ tailWord_7871466) baseStart_7871466 baseEnd_7871466 := by
    simpa [prefixWord, tailWord_7871466, baseEnd_7871466] using wordTrace_append hprefix tailTrace_7871466
  have hstable : (prefixWord ++ tailWord_7871466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871466).length < 2 ^ (prefixWord ++ tailWord_7871466).sum := by decide
  have hdescent : baseEnd_7871466 < baseStart_7871466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871475 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6]
def baseStart_7871475 : Nat := 118140960795 + 7871475 * 2 ^ 59
def prefixEnd_7871475 : Nat := 4983230072969 + 3 ^ 40 * 7871475 * 2
def baseEnd_7871475 : Nat := 4041850134849695551562251

theorem tailTrace_7871475 : CollatzResearch.WordTrace tailWord_7871475 prefixEnd_7871475 4041850134849695551562251 := by
  unfold tailWord_7871475
  simp only [CollatzResearch.WordTrace]
  refine ⟨287096279157997890746663879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191397519438665260497775919 287096279157997890746663879)
  ·
    refine ⟨430644418736996836119995819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287096279157997890746663879 430644418736996836119995819)
    ·
      refine ⟨645966628105495254179993729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430644418736996836119995819 645966628105495254179993729)
      ·
        refine ⟨484474971079121440634995297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645966628105495254179993729 484474971079121440634995297)
        ·
          refine ⟨363356228309341080476246473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484474971079121440634995297 363356228309341080476246473)
          ·
            refine ⟨272517171232005810357184855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363356228309341080476246473 272517171232005810357184855)
            ·
              refine ⟨408775756848008715535777283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272517171232005810357184855 408775756848008715535777283)
              ·
                refine ⟨613163635272013073303665925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408775756848008715535777283 613163635272013073303665925)
                ·
                  refine ⟨114968181613502451244437361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613163635272013073303665925 114968181613502451244437361)
                  ·
                    refine ⟨86226136210126838433328021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114968181613502451244437361 86226136210126838433328021)
                    ·
                      refine ⟨4041850134849695551562251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86226136210126838433328021 4041850134849695551562251)
                      ·
                        rfl

theorem cell23_7871475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_7871475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871475 prefixEnd_7871475 := by exact prefixLift 7871475
  have htrace : WordTrace (prefixWord ++ tailWord_7871475) baseStart_7871475 baseEnd_7871475 := by
    simpa [prefixWord, tailWord_7871475, baseEnd_7871475] using wordTrace_append hprefix tailTrace_7871475
  have hstable : (prefixWord ++ tailWord_7871475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871475).length < 2 ^ (prefixWord ++ tailWord_7871475).sum := by decide
  have hdescent : baseEnd_7871475 < baseStart_7871475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871482 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_7871482 : Nat := 118140960795 + 7871482 * 2 ^ 59
def prefixEnd_7871482 : Nat := 4983230072969 + 3 ^ 40 * 7871482 * 2
def baseEnd_7871482 : Nat := 4041853729214277024174719

theorem tailTrace_7871482 : CollatzResearch.WordTrace tailWord_7871482 prefixEnd_7871482 4041853729214277024174719 := by
  unfold tailWord_7871482
  simp only [CollatzResearch.WordTrace]
  refine ⟨71774133617243132735542175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191397689645981687294779133 71774133617243132735542175)
  ·
    refine ⟨107661200425864699103313263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71774133617243132735542175 107661200425864699103313263)
    ·
      refine ⟨161491800638797048654969895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107661200425864699103313263 161491800638797048654969895)
      ·
        refine ⟨242237700958195572982454843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161491800638797048654969895 242237700958195572982454843)
        ·
          refine ⟨363356551437293359473682265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242237700958195572982454843 363356551437293359473682265)
          ·
            refine ⟨272517413577970019605261699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363356551437293359473682265 272517413577970019605261699)
            ·
              refine ⟨408776120366955029407892549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272517413577970019605261699 408776120366955029407892549)
              ·
                refine ⟨76645522568804068013979853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408776120366955029407892549 76645522568804068013979853)
                ·
                  refine ⟨28742070963301525505242445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76645522568804068013979853 28742070963301525505242445)
                  ·
                    refine ⟨10778276611238072064465917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28742070963301525505242445 10778276611238072064465917)
                    ·
                      refine ⟨4041853729214277024174719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778276611238072064465917 4041853729214277024174719)
                      ·
                        rfl

theorem cell23_7871482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_7871482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871482 prefixEnd_7871482 := by exact prefixLift 7871482
  have htrace : WordTrace (prefixWord ++ tailWord_7871482) baseStart_7871482 baseEnd_7871482 := by
    simpa [prefixWord, tailWord_7871482, baseEnd_7871482] using wordTrace_append hprefix tailTrace_7871482
  have hstable : (prefixWord ++ tailWord_7871482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871482).length < 2 ^ (prefixWord ++ tailWord_7871482).sum := by decide
  have hdescent : baseEnd_7871482 < baseStart_7871482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871486 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7871486 : Nat := 118140960795 + 7871486 * 2 ^ 59
def prefixEnd_7871486 : Nat := 4983230072969 + 3 ^ 40 * 7871486 * 2
def baseEnd_7871486 : Nat := 4041855783136895008524701

theorem tailTrace_7871486 : CollatzResearch.WordTrace tailWord_7871486 prefixEnd_7871486 4041855783136895008524701 := by
  unfold tailWord_7871486
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887085045119754953164289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191397786907305359750209541 35887085045119754953164289)
  ·
    refine ⟨26915313783839816214873217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35887085045119754953164289 26915313783839816214873217)
    ·
      refine ⟨20186485337879862161154913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26915313783839816214873217 20186485337879862161154913)
      ·
        refine ⟨15139864003409896620866185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20186485337879862161154913 15139864003409896620866185)
        ·
          refine ⟨11354898002557422465649639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15139864003409896620866185 11354898002557422465649639)
          ·
            refine ⟨17032347003836133698474459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11354898002557422465649639 17032347003836133698474459)
            ·
              refine ⟨25548520505754200547711689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17032347003836133698474459 25548520505754200547711689)
              ·
                refine ⟨19161390379315650410783767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25548520505754200547711689 19161390379315650410783767)
                ·
                  refine ⟨28742085568973475616175651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19161390379315650410783767 28742085568973475616175651)
                  ·
                    refine ⟨43113128353460213424263477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28742085568973475616175651 43113128353460213424263477)
                    ·
                      refine ⟨4041855783136895008524701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43113128353460213424263477 4041855783136895008524701)
                      ·
                        rfl

theorem cell23_7871486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7871486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871486 prefixEnd_7871486 := by exact prefixLift 7871486
  have htrace : WordTrace (prefixWord ++ tailWord_7871486) baseStart_7871486 baseEnd_7871486 := by
    simpa [prefixWord, tailWord_7871486, baseEnd_7871486] using wordTrace_append hprefix tailTrace_7871486
  have hstable : (prefixWord ++ tailWord_7871486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871486).length < 2 ^ (prefixWord ++ tailWord_7871486).sum := by decide
  have hdescent : baseEnd_7871486 < baseStart_7871486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871499 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 3]
def baseStart_7871499 : Nat := 118140960795 + 7871499 * 2 ^ 59
def prefixEnd_7871499 : Nat := 4983230072969 + 3 ^ 40 * 7871499 * 2
def baseEnd_7871499 : Nat := 4041862458385403457662141

theorem tailTrace_7871499 : CollatzResearch.WordTrace tailWord_7871499 prefixEnd_7871499 4041862458385403457662141 := by
  unfold tailWord_7871499
  simp only [CollatzResearch.WordTrace]
  refine ⟨287097154509910942845537551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191398103006607295230358367 287097154509910942845537551)
  ·
    refine ⟨430645731764866414268306327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287097154509910942845537551 430645731764866414268306327)
    ·
      refine ⟨645968597647299621402459491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430645731764866414268306327 645968597647299621402459491)
      ·
        refine ⟨968952896470949432103689237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645968597647299621402459491 968952896470949432103689237)
        ·
          refine ⟨45419667022075754629860433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 968952896470949432103689237 45419667022075754629860433)
          ·
            refine ⟨34064750266556815972395325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45419667022075754629860433 34064750266556815972395325)
            ·
              refine ⟨12774281349958805989648247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34064750266556815972395325 12774281349958805989648247)
              ·
                refine ⟨19161422024938208984472371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12774281349958805989648247 19161422024938208984472371)
                ·
                  refine ⟨28742133037407313476708557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19161422024938208984472371 28742133037407313476708557)
                  ·
                    refine ⟨10778299889027742553765709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28742133037407313476708557 10778299889027742553765709)
                    ·
                      refine ⟨4041862458385403457662141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778299889027742553765709 4041862458385403457662141)
                      ·
                        rfl

theorem cell23_7871499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 3].length) (baseStart_7871499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871499 prefixEnd_7871499 := by exact prefixLift 7871499
  have htrace : WordTrace (prefixWord ++ tailWord_7871499) baseStart_7871499 baseEnd_7871499 := by
    simpa [prefixWord, tailWord_7871499, baseEnd_7871499] using wordTrace_append hprefix tailTrace_7871499
  have hstable : (prefixWord ++ tailWord_7871499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871499).length < 2 ^ (prefixWord ++ tailWord_7871499).sum := by decide
  have hdescent : baseEnd_7871499 < baseStart_7871499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871512 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_7871512 : Nat := 118140960795 + 7871512 * 2 ^ 59
def prefixEnd_7871512 : Nat := 4983230072969 + 3 ^ 40 * 7871512 * 2
def baseEnd_7871512 : Nat := 4041869133633911906799581

theorem tailTrace_7871512 : CollatzResearch.WordTrace tailWord_7871512 prefixEnd_7871512 4041869133633911906799581 := by
  unfold tailWord_7871512
  simp only [CollatzResearch.WordTrace]
  refine ⟨143548814329431923032880395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191398419105909230710507193 143548814329431923032880395)
  ·
    refine ⟨215323221494147884549320593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143548814329431923032880395 215323221494147884549320593)
    ·
      refine ⟨161492416120610913411990445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215323221494147884549320593 161492416120610913411990445)
      ·
        refine ⟨60559656045229092529496417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161492416120610913411990445 60559656045229092529496417)
        ·
          refine ⟨45419742033921819397122313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60559656045229092529496417 45419742033921819397122313)
          ·
            refine ⟨34064806525441364547841735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45419742033921819397122313 34064806525441364547841735)
            ·
              refine ⟨51097209788162046821762603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34064806525441364547841735 51097209788162046821762603)
              ·
                refine ⟨76645814682243070232643905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51097209788162046821762603 76645814682243070232643905)
                ·
                  refine ⟨57484361011682302674482929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76645814682243070232643905 57484361011682302674482929)
                  ·
                    refine ⟨43113270758761727005862197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57484361011682302674482929 43113270758761727005862197)
                    ·
                      refine ⟨4041869133633911906799581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43113270758761727005862197 4041869133633911906799581)
                      ·
                        rfl

theorem cell23_7871512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_7871512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871512 prefixEnd_7871512 := by exact prefixLift 7871512
  have htrace : WordTrace (prefixWord ++ tailWord_7871512) baseStart_7871512 baseEnd_7871512 := by
    simpa [prefixWord, tailWord_7871512, baseEnd_7871512] using wordTrace_append hprefix tailTrace_7871512
  have hstable : (prefixWord ++ tailWord_7871512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871512).length < 2 ^ (prefixWord ++ tailWord_7871512).sum := by decide
  have hdescent : baseEnd_7871512 < baseStart_7871512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871517 : List Nat := [1, 4, 2, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_7871517 : Nat := 118140960795 + 7871517 * 2 ^ 59
def prefixEnd_7871517 : Nat := 4983230072969 + 3 ^ 40 * 7871517 * 2
def baseEnd_7871517 : Nat := 4041871701037184387237059

theorem tailTrace_7871517 : CollatzResearch.WordTrace tailWord_7871517 prefixEnd_7871517 4041871701037184387237059 := by
  unfold tailWord_7871517
  simp only [CollatzResearch.WordTrace]
  refine ⟨287097811023845731919692805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191398540682563821279795203 287097811023845731919692805)
  ·
    refine ⟨53830839566971074734942401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287097811023845731919692805 53830839566971074734942401)
    ·
      refine ⟨40373129675228306051206801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53830839566971074734942401 40373129675228306051206801)
      ·
        refine ⟨30279847256421229538405101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40373129675228306051206801 30279847256421229538405101)
        ·
          refine ⟨11354942721157961076901913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30279847256421229538405101 11354942721157961076901913)
          ·
            refine ⟨8516207040868470807676435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11354942721157961076901913 8516207040868470807676435)
            ·
              refine ⟨12774310561302706211514653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516207040868470807676435 12774310561302706211514653)
              ·
                refine ⟨4790366460488514829317995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12774310561302706211514653 4790366460488514829317995)
                ·
                  refine ⟨7185549690732772243976993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790366460488514829317995 7185549690732772243976993)
                  ·
                    refine ⟨5389162268049579182982745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7185549690732772243976993 5389162268049579182982745)
                    ·
                      refine ⟨4041871701037184387237059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389162268049579182982745 4041871701037184387237059)
                      ·
                        rfl

theorem cell23_7871517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_7871517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871517 prefixEnd_7871517 := by exact prefixLift 7871517
  have htrace : WordTrace (prefixWord ++ tailWord_7871517) baseStart_7871517 baseEnd_7871517 := by
    simpa [prefixWord, tailWord_7871517, baseEnd_7871517] using wordTrace_append hprefix tailTrace_7871517
  have hstable : (prefixWord ++ tailWord_7871517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871517).length < 2 ^ (prefixWord ++ tailWord_7871517).sum := by decide
  have hdescent : baseEnd_7871517 < baseStart_7871517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871550 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_7871550 : Nat := 118140960795 + 7871550 * 2 ^ 59
def prefixEnd_7871550 : Nat := 4983230072969 + 3 ^ 40 * 7871550 * 2
def baseEnd_7871550 : Nat := 4041888645898782758124407

theorem tailTrace_7871550 : CollatzResearch.WordTrace tailWord_7871550 prefixEnd_7871550 4041888645898782758124407 := by
  unfold tailWord_7871550
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887376829090772319455513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191399343088484119037096069 35887376829090772319455513)
  ·
    refine ⟨26915532621818079239591635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35887376829090772319455513 26915532621818079239591635)
    ·
      refine ⟨40373298932727118859387453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26915532621818079239591635 40373298932727118859387453)
      ·
        refine ⟨15139987099772669572270295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40373298932727118859387453 15139987099772669572270295)
        ·
          refine ⟨22709980649659004358405443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15139987099772669572270295 22709980649659004358405443)
          ·
            refine ⟨34064970974488506537608165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22709980649659004358405443 34064970974488506537608165)
            ·
              refine ⟨6387182057716594975801531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34064970974488506537608165 6387182057716594975801531)
              ·
                refine ⟨9580773086574892463702297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6387182057716594975801531 9580773086574892463702297)
                ·
                  refine ⟨7185579814931169347776723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9580773086574892463702297 7185579814931169347776723)
                  ·
                    refine ⟨10778369722396754021665085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7185579814931169347776723 10778369722396754021665085)
                    ·
                      refine ⟨4041888645898782758124407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778369722396754021665085 4041888645898782758124407)
                      ·
                        rfl

theorem cell23_7871550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_7871550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871550 prefixEnd_7871550 := by exact prefixLift 7871550
  have htrace : WordTrace (prefixWord ++ tailWord_7871550) baseStart_7871550 baseEnd_7871550 := by
    simpa [prefixWord, tailWord_7871550, baseEnd_7871550] using wordTrace_append hprefix tailTrace_7871550
  have hstable : (prefixWord ++ tailWord_7871550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871550).length < 2 ^ (prefixWord ++ tailWord_7871550).sum := by decide
  have hdescent : baseEnd_7871550 < baseStart_7871550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871552 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_7871552 : Nat := 118140960795 + 7871552 * 2 ^ 59
def prefixEnd_7871552 : Nat := 4983230072969 + 3 ^ 40 * 7871552 * 2
def baseEnd_7871552 : Nat := 4041889672860091750299397

theorem tailTrace_7871552 : CollatzResearch.WordTrace tailWord_7871552 prefixEnd_7871552 4041889672860091750299397 := by
  unfold tailWord_7871552
  simp only [CollatzResearch.WordTrace]
  refine ⟨143549543789359466448608455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191399391719145955264811273 143549543789359466448608455)
  ·
    refine ⟨215324315684039199672912683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143549543789359466448608455 215324315684039199672912683)
    ·
      refine ⟨322986473526058799509369025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215324315684039199672912683 322986473526058799509369025)
      ·
        refine ⟨242239855144544099632026769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322986473526058799509369025 242239855144544099632026769)
        ·
          refine ⟨181679891358408074724020077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242239855144544099632026769 181679891358408074724020077)
          ·
            refine ⟨68129959259403028021507529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181679891358408074724020077 68129959259403028021507529)
            ·
              refine ⟨51097469444552271016130647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68129959259403028021507529 51097469444552271016130647)
              ·
                refine ⟨76646204166828406524195971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51097469444552271016130647 76646204166828406524195971)
                ·
                  refine ⟨114969306250242609786293957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76646204166828406524195971 114969306250242609786293957)
                  ·
                    refine ⟨21556744921920489334930117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114969306250242609786293957 21556744921920489334930117)
                    ·
                      refine ⟨4041889672860091750299397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21556744921920489334930117 4041889672860091750299397)
                      ·
                        rfl

theorem cell23_7871552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_7871552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871552 prefixEnd_7871552 := by exact prefixLift 7871552
  have htrace : WordTrace (prefixWord ++ tailWord_7871552) baseStart_7871552 baseEnd_7871552 := by
    simpa [prefixWord, tailWord_7871552, baseEnd_7871552] using wordTrace_append hprefix tailTrace_7871552
  have hstable : (prefixWord ++ tailWord_7871552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871552).length < 2 ^ (prefixWord ++ tailWord_7871552).sum := by decide
  have hdescent : baseEnd_7871552 < baseStart_7871552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871562 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 7]
def baseStart_7871562 : Nat := 118140960795 + 7871562 * 2 ^ 59
def prefixEnd_7871562 : Nat := 4983230072969 + 3 ^ 40 * 7871562 * 2
def baseEnd_7871562 : Nat := 449099423074070745686039

theorem tailTrace_7871562 : CollatzResearch.WordTrace tailWord_7871562 prefixEnd_7871562 449099423074070745686039 := by
  unfold tailWord_7871562
  simp only [CollatzResearch.WordTrace]
  refine ⟨71774863077170676151270235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191399634872455136403387293 71774863077170676151270235)
  ·
    refine ⟨107662294615756014226905353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71774863077170676151270235 107662294615756014226905353)
    ·
      refine ⟨80746720961817010670179015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107662294615756014226905353 80746720961817010670179015)
      ·
        refine ⟨121120081442725516005268523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80746720961817010670179015 121120081442725516005268523)
        ·
          refine ⟨181680122164088274007902785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121120081442725516005268523 181680122164088274007902785)
          ·
            refine ⟨136260091623066205505927089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181680122164088274007902785 136260091623066205505927089)
            ·
              refine ⟨102195068717299654129445317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136260091623066205505927089 102195068717299654129445317)
              ·
                refine ⟨19161575384493685149270997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102195068717299654129445317 19161575384493685149270997)
                ·
                  refine ⟨449099423074070745686039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19161575384493685149270997 449099423074070745686039)
                  ·
                    rfl

theorem cell23_7871562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_7871562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871562 prefixEnd_7871562 := by exact prefixLift 7871562
  have htrace : WordTrace (prefixWord ++ tailWord_7871562) baseStart_7871562 baseEnd_7871562 := by
    simpa [prefixWord, tailWord_7871562, baseEnd_7871562] using wordTrace_append hprefix tailTrace_7871562
  have hstable : (prefixWord ++ tailWord_7871562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871562).length < 2 ^ (prefixWord ++ tailWord_7871562).sum := by decide
  have hdescent : baseEnd_7871562 < baseStart_7871562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871589 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_7871589 : Nat := 118140960795 + 7871589 * 2 ^ 59
def prefixEnd_7871589 : Nat := 4983230072969 + 3 ^ 40 * 7871589 * 2
def baseEnd_7871589 : Nat := 4041908671644308105536727

theorem tailTrace_7871589 : CollatzResearch.WordTrace tailWord_7871589 prefixEnd_7871589 4041908671644308105536727 := by
  unfold tailWord_7871589
  simp only [CollatzResearch.WordTrace]
  refine ⟨287100437079584888216313821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191400291386389925477542547 287100437079584888216313821)
  ·
    refine ⟨107662663904844333081117683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287100437079584888216313821 107662663904844333081117683)
    ·
      refine ⟨161493995857266499621676525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107662663904844333081117683 161493995857266499621676525)
      ·
        refine ⟨60560248446474937358128697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161493995857266499621676525 60560248446474937358128697)
        ·
          refine ⟨45420186334856203018596523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60560248446474937358128697 45420186334856203018596523)
          ·
            refine ⟨68130279502284304527894785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45420186334856203018596523 68130279502284304527894785)
            ·
              refine ⟨51097709626713228395921089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68130279502284304527894785 51097709626713228395921089)
              ·
                refine ⟨38323282220034921296940817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51097709626713228395921089 38323282220034921296940817)
                ·
                  refine ⟨28742461665026190972705613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38323282220034921296940817 28742461665026190972705613)
                  ·
                    refine ⟨10778423124384821614764605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28742461665026190972705613 10778423124384821614764605)
                    ·
                      refine ⟨4041908671644308105536727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778423124384821614764605 4041908671644308105536727)
                      ·
                        rfl

theorem cell23_7871589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_7871589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871589 prefixEnd_7871589 := by exact prefixLift 7871589
  have htrace : WordTrace (prefixWord ++ tailWord_7871589) baseStart_7871589 baseEnd_7871589 := by
    simpa [prefixWord, tailWord_7871589, baseEnd_7871589] using wordTrace_append hprefix tailTrace_7871589
  have hstable : (prefixWord ++ tailWord_7871589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871589).length < 2 ^ (prefixWord ++ tailWord_7871589).sum := by decide
  have hdescent : baseEnd_7871589 < baseStart_7871589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871599 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 7, 2]
def baseStart_7871599 : Nat := 118140960795 + 7871599 * 2 ^ 59
def prefixEnd_7871599 : Nat := 4983230072969 + 3 ^ 40 * 7871599 * 2
def baseEnd_7871599 : Nat := 4041913806450853066411681

theorem tailTrace_7871599 : CollatzResearch.WordTrace tailWord_7871599 prefixEnd_7871599 4041913806450853066411681 := by
  unfold tailWord_7871599
  simp only [CollatzResearch.WordTrace]
  refine ⟨287100801809548659924177851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191400534539699106616118567 287100801809548659924177851)
  ·
    refine ⟨430651202714322989886266777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287100801809548659924177851 430651202714322989886266777)
    ·
      refine ⟨322988402035742242414700083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430651202714322989886266777 322988402035742242414700083)
      ·
        refine ⟨484482603053613363622050125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322988402035742242414700083 484482603053613363622050125)
        ·
          refine ⟨181680976145105011358268797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484482603053613363622050125 181680976145105011358268797)
          ·
            refine ⟨68130366054414379259350799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181680976145105011358268797 68130366054414379259350799)
            ·
              refine ⟨102195549081621568889026199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68130366054414379259350799 102195549081621568889026199)
              ·
                refine ⟨153293323622432353333539299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102195549081621568889026199 153293323622432353333539299)
                ·
                  refine ⟨229939985433648530000308949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153293323622432353333539299 229939985433648530000308949)
                  ·
                    refine ⟨5389218408601137421882241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 229939985433648530000308949 5389218408601137421882241)
                    ·
                      refine ⟨4041913806450853066411681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389218408601137421882241 4041913806450853066411681)
                      ·
                        rfl

theorem cell23_7871599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7, 2].length) (baseStart_7871599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871599 prefixEnd_7871599 := by exact prefixLift 7871599
  have htrace : WordTrace (prefixWord ++ tailWord_7871599) baseStart_7871599 baseEnd_7871599 := by
    simpa [prefixWord, tailWord_7871599, baseEnd_7871599] using wordTrace_append hprefix tailTrace_7871599
  have hstable : (prefixWord ++ tailWord_7871599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871599).length < 2 ^ (prefixWord ++ tailWord_7871599).sum := by decide
  have hdescent : baseEnd_7871599 < baseStart_7871599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871606 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7871606 : Nat := 118140960795 + 7871606 * 2 ^ 59
def prefixEnd_7871606 : Nat := 4983230072969 + 3 ^ 40 * 7871606 * 2
def baseEnd_7871606 : Nat := 4041917400815434539024149

theorem tailTrace_7871606 : CollatzResearch.WordTrace tailWord_7871606 prefixEnd_7871606 4041917400815434539024149 := by
  unfold tailWord_7871606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17943816070032706257480167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191400704747015533413121781 17943816070032706257480167)
  ·
    refine ⟨26915724105049059386220251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17943816070032706257480167 26915724105049059386220251)
    ·
      refine ⟨40373586157573589079330377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26915724105049059386220251 40373586157573589079330377)
      ·
        refine ⟨30280189618180191809497783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40373586157573589079330377 30280189618180191809497783)
        ·
          refine ⟨45420284427270287714246675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30280189618180191809497783 45420284427270287714246675)
          ·
            refine ⟨68130426640905431571370013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45420284427270287714246675 68130426640905431571370013)
            ·
              refine ⟨25548909990339536839263755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68130426640905431571370013 25548909990339536839263755)
              ·
                refine ⟨38323364985509305258895633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25548909990339536839263755 38323364985509305258895633)
                ·
                  refine ⟨28742523739131978944171725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38323364985509305258895633 28742523739131978944171725)
                  ·
                    refine ⟨10778446402174492104064397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28742523739131978944171725 10778446402174492104064397)
                    ·
                      refine ⟨4041917400815434539024149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778446402174492104064397 4041917400815434539024149)
                      ·
                        rfl

theorem cell23_7871606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7871606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871606 prefixEnd_7871606 := by exact prefixLift 7871606
  have htrace : WordTrace (prefixWord ++ tailWord_7871606) baseStart_7871606 baseEnd_7871606 := by
    simpa [prefixWord, tailWord_7871606, baseEnd_7871606] using wordTrace_append hprefix tailTrace_7871606
  have hstable : (prefixWord ++ tailWord_7871606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871606).length < 2 ^ (prefixWord ++ tailWord_7871606).sum := by decide
  have hdescent : baseEnd_7871606 < baseStart_7871606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871632 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_7871632 : Nat := 118140960795 + 7871632 * 2 ^ 59
def prefixEnd_7871632 : Nat := 4983230072969 + 3 ^ 40 * 7871632 * 2
def baseEnd_7871632 : Nat := 4041930751312451437299029

theorem tailTrace_7871632 : CollatzResearch.WordTrace tailWord_7871632 prefixEnd_7871632 4041930751312451437299029 := by
  unfold tailWord_7871632
  simp only [CollatzResearch.WordTrace]
  refine ⟨143551002709214553280064575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191401336945619404373419433 143551002709214553280064575)
  ·
    refine ⟨215326504063821829920096863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143551002709214553280064575 215326504063821829920096863)
    ·
      refine ⟨322989756095732744880145295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215326504063821829920096863 322989756095732744880145295)
      ·
        refine ⟨484484634143599117320217943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322989756095732744880145295 484484634143599117320217943)
        ·
          refine ⟨726726951215398675980326915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484484634143599117320217943 726726951215398675980326915)
          ·
            refine ⟨1090090426823098013970490373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726726951215398675980326915 1090090426823098013970490373)
            ·
              refine ⟨204391955029330877619466945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1090090426823098013970490373 204391955029330877619466945)
              ·
                refine ⟨153293966271998158214600209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204391955029330877619466945 153293966271998158214600209)
                ·
                  refine ⟨114970474703998618660950157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153293966271998158214600209 114970474703998618660950157)
                  ·
                    refine ⟨43113928013999481997856309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114970474703998618660950157 43113928013999481997856309)
                    ·
                      refine ⟨4041930751312451437299029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43113928013999481997856309 4041930751312451437299029)
                      ·
                        rfl

theorem cell23_7871632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_7871632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871632 prefixEnd_7871632 := by exact prefixLift 7871632
  have htrace : WordTrace (prefixWord ++ tailWord_7871632) baseStart_7871632 baseEnd_7871632 := by
    simpa [prefixWord, tailWord_7871632, baseEnd_7871632] using wordTrace_append hprefix tailTrace_7871632
  have hstable : (prefixWord ++ tailWord_7871632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871632).length < 2 ^ (prefixWord ++ tailWord_7871632).sum := by decide
  have hdescent : baseEnd_7871632 < baseStart_7871632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871690 : List Nat := [3, 1, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_7871690 : Nat := 118140960795 + 7871690 * 2 ^ 59
def prefixEnd_7871690 : Nat := 4983230072969 + 3 ^ 40 * 7871690 * 2
def baseEnd_7871690 : Nat := 1347320177730137403457921

theorem tailTrace_7871690 : CollatzResearch.WordTrace tailWord_7871690 prefixEnd_7871690 1347320177730137403457921 := by
  unfold tailWord_7871690
  simp only [CollatzResearch.WordTrace]
  refine ⟨71776030213054745616435131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191402747234812654977160349 71776030213054745616435131)
  ·
    refine ⟨107664045319582118424652697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71776030213054745616435131 107664045319582118424652697)
    ·
      refine ⟨80748033989686588818489523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107664045319582118424652697 80748033989686588818489523)
      ·
        refine ⟨121122050984529883227734285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80748033989686588818489523 121122050984529883227734285)
        ·
          refine ⟨45420769119198706210400357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121122050984529883227734285 45420769119198706210400357)
          ·
            refine ⟨8516394209849757414450067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45420769119198706210400357 8516394209849757414450067)
            ·
              refine ⟨12774591314774636121675101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516394209849757414450067 12774591314774636121675101)
              ·
                refine ⟨4790471743040488545628163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12774591314774636121675101 4790471743040488545628163)
                ·
                  refine ⟨7185707614560732818442245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790471743040488545628163 7185707614560732818442245)
                  ·
                    refine ⟨1347320177730137403457921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7185707614560732818442245 1347320177730137403457921)
                    ·
                      rfl

theorem cell23_7871690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_7871690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871690 prefixEnd_7871690 := by exact prefixLift 7871690
  have htrace : WordTrace (prefixWord ++ tailWord_7871690) baseStart_7871690 baseEnd_7871690 := by
    simpa [prefixWord, tailWord_7871690, baseEnd_7871690] using wordTrace_append hprefix tailTrace_7871690
  have hstable : (prefixWord ++ tailWord_7871690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871690).length < 2 ^ (prefixWord ++ tailWord_7871690).sum := by decide
  have hdescent : baseEnd_7871690 < baseStart_7871690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871700 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7871700 : Nat := 118140960795 + 7871700 * 2 ^ 59
def prefixEnd_7871700 : Nat := 4983230072969 + 3 ^ 40 * 7871700 * 2
def baseEnd_7871700 : Nat := 4041965667996957171248717

theorem tailTrace_7871700 : CollatzResearch.WordTrace tailWord_7871700 prefixEnd_7871700 4041965667996957171248717 := by
  unfold tailWord_7871700
  simp only [CollatzResearch.WordTrace]
  refine ⟨143552242791091377086802277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191402990388121836115736369 143552242791091377086802277)
  ·
    refine ⟨26916045523329633203775427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143552242791091377086802277 26916045523329633203775427)
    ·
      refine ⟨40374068284994449805663141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26916045523329633203775427 40374068284994449805663141)
      ·
        refine ⟨7570137803436459338561839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40374068284994449805663141 7570137803436459338561839)
        ·
          refine ⟨11355206705154689007842759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7570137803436459338561839 11355206705154689007842759)
          ·
            refine ⟨17032810057732033511764139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355206705154689007842759 17032810057732033511764139)
            ·
              refine ⟨25549215086598050267646209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17032810057732033511764139 25549215086598050267646209)
              ·
                refine ⟨19161911314948537700734657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25549215086598050267646209 19161911314948537700734657)
                ·
                  refine ⟨14371433486211403275550993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19161911314948537700734657 14371433486211403275550993)
                  ·
                    refine ⟨10778575114658552456663245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14371433486211403275550993 10778575114658552456663245)
                    ·
                      refine ⟨4041965667996957171248717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778575114658552456663245 4041965667996957171248717)
                      ·
                        rfl

theorem cell23_7871700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7871700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871700 prefixEnd_7871700 := by exact prefixLift 7871700
  have htrace : WordTrace (prefixWord ++ tailWord_7871700) baseStart_7871700 baseEnd_7871700 := by
    simpa [prefixWord, tailWord_7871700, baseEnd_7871700] using wordTrace_append hprefix tailTrace_7871700
  have hstable : (prefixWord ++ tailWord_7871700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871700).length < 2 ^ (prefixWord ++ tailWord_7871700).sum := by decide
  have hdescent : baseEnd_7871700 < baseStart_7871700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871713 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_7871713 : Nat := 118140960795 + 7871713 * 2 ^ 59
def prefixEnd_7871713 : Nat := 4983230072969 + 3 ^ 40 * 7871713 * 2
def baseEnd_7871713 : Nat := 4041972343245465620386157

theorem tailTrace_7871713 : CollatzResearch.WordTrace tailWord_7871713 prefixEnd_7871713 4041972343245465620386157 := by
  unfold tailWord_7871713
  simp only [CollatzResearch.WordTrace]
  refine ⟨287104959731135657393827793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191403306487423771595885195 287104959731135657393827793)
  ·
    refine ⟨215328719798351743045370845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287104959731135657393827793 215328719798351743045370845)
    ·
      refine ⟨80748269924381903642014067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215328719798351743045370845 80748269924381903642014067)
      ·
        refine ⟨121122404886572855463021101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80748269924381903642014067 121122404886572855463021101)
        ·
          refine ⟨45420901832464820798632913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121122404886572855463021101 45420901832464820798632913)
          ·
            refine ⟨34065676374348615598974685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45420901832464820798632913 34065676374348615598974685)
            ·
              refine ⟨12774628640380730849615507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34065676374348615598974685 12774628640380730849615507)
              ·
                refine ⟨19161942960571096274423261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12774628640380730849615507 19161942960571096274423261)
                ·
                  refine ⟨7185728610214161102908723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19161942960571096274423261 7185728610214161102908723)
                  ·
                    refine ⟨10778592915321241654363085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7185728610214161102908723 10778592915321241654363085)
                    ·
                      refine ⟨4041972343245465620386157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778592915321241654363085 4041972343245465620386157)
                      ·
                        rfl

theorem cell23_7871713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_7871713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871713 prefixEnd_7871713 := by exact prefixLift 7871713
  have htrace : WordTrace (prefixWord ++ tailWord_7871713) baseStart_7871713 baseEnd_7871713 := by
    simpa [prefixWord, tailWord_7871713, baseEnd_7871713] using wordTrace_append hprefix tailTrace_7871713
  have hstable : (prefixWord ++ tailWord_7871713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871713).length < 2 ^ (prefixWord ++ tailWord_7871713).sum := by decide
  have hdescent : baseEnd_7871713 < baseStart_7871713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871729 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 1, 6]
def baseStart_7871729 : Nat := 118140960795 + 7871729 * 2 ^ 59
def prefixEnd_7871729 : Nat := 4983230072969 + 3 ^ 40 * 7871729 * 2
def baseEnd_7871729 : Nat := 1347326852978645852595361

theorem tailTrace_7871729 : CollatzResearch.WordTrace tailWord_7871729 prefixEnd_7871729 1347326852978645852595361 := by
  unfold tailWord_7871729
  simp only [CollatzResearch.WordTrace]
  refine ⟨287105543299077692126410241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191403695532718461417606827 287105543299077692126410241)
  ·
    refine ⟨215329157474308269094807681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287105543299077692126410241 215329157474308269094807681)
    ·
      refine ⟨161496868105731201821105761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215329157474308269094807681 161496868105731201821105761)
      ·
        refine ⟨121122651079298401365829321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161496868105731201821105761 121122651079298401365829321)
        ·
          refine ⟨90841988309473801024371991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121122651079298401365829321 90841988309473801024371991)
          ·
            refine ⟨136262982464210701536557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90841988309473801024371991 136262982464210701536557987)
            ·
              refine ⟨204394473696316052304836981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136262982464210701536557987 204394473696316052304836981)
              ·
                refine ⟨19161981909029629903578467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204394473696316052304836981 19161981909029629903578467)
                ·
                  refine ⟨28742972863544444855367701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19161981909029629903578467 28742972863544444855367701)
                  ·
                    refine ⟨1347326852978645852595361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28742972863544444855367701 1347326852978645852595361)
                    ·
                      rfl

theorem cell23_7871729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_7871729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871729 prefixEnd_7871729 := by exact prefixLift 7871729
  have htrace : WordTrace (prefixWord ++ tailWord_7871729) baseStart_7871729 baseEnd_7871729 := by
    simpa [prefixWord, tailWord_7871729, baseEnd_7871729] using wordTrace_append hprefix tailTrace_7871729
  have hstable : (prefixWord ++ tailWord_7871729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871729).length < 2 ^ (prefixWord ++ tailWord_7871729).sum := by decide
  have hdescent : baseEnd_7871729 < baseStart_7871729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871740 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_7871740 : Nat := 118140960795 + 7871740 * 2 ^ 59
def prefixEnd_7871740 : Nat := 4983230072969 + 3 ^ 40 * 7871740 * 2
def baseEnd_7871740 : Nat := 4041986207223137014748533

theorem tailTrace_7871740 : CollatzResearch.WordTrace tailWord_7871740 prefixEnd_7871740 4041986207223137014748533 := by
  unfold tailWord_7871740
  simp only [CollatzResearch.WordTrace]
  refine ⟨143552972251018920502530337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191403963001358560670040449 143552972251018920502530337)
  ·
    refine ⟨107664729188264190376897753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143552972251018920502530337 107664729188264190376897753)
    ·
      refine ⟨80748546891198142782673315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107664729188264190376897753 80748546891198142782673315)
      ·
        refine ⟨121122820336797214174009973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80748546891198142782673315 121122820336797214174009973)
        ·
          refine ⟨11355264406574738828813435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121122820336797214174009973 11355264406574738828813435)
          ·
            refine ⟨17032896609862108243220153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355264406574738828813435 17032896609862108243220153)
            ·
              refine ⟨12774672457396581182415115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17032896609862108243220153 12774672457396581182415115)
              ·
                refine ⟨19162008686094871773622673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12774672457396581182415115 19162008686094871773622673)
                ·
                  refine ⟨14371506514571153830217005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19162008686094871773622673 14371506514571153830217005)
                  ·
                    refine ⟨5389314942964182686331377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14371506514571153830217005 5389314942964182686331377)
                    ·
                      refine ⟨4041986207223137014748533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389314942964182686331377 4041986207223137014748533)
                      ·
                        rfl

theorem cell23_7871740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_7871740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871740 prefixEnd_7871740 := by exact prefixLift 7871740
  have htrace : WordTrace (prefixWord ++ tailWord_7871740) baseStart_7871740 baseEnd_7871740 := by
    simpa [prefixWord, tailWord_7871740, baseEnd_7871740] using wordTrace_append hprefix tailTrace_7871740
  have hstable : (prefixWord ++ tailWord_7871740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871740).length < 2 ^ (prefixWord ++ tailWord_7871740).sum := by decide
  have hdescent : baseEnd_7871740 < baseStart_7871740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871753 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 1, 1, 4]
def baseStart_7871753 : Nat := 118140960795 + 7871753 * 2 ^ 59
def prefixEnd_7871753 : Nat := 4983230072969 + 3 ^ 40 * 7871753 * 2
def baseEnd_7871753 : Nat := 4041992882471645463885973

theorem tailTrace_7871753 : CollatzResearch.WordTrace tailWord_7871753 prefixEnd_7871753 4041992882471645463885973 := by
  unfold tailWord_7871753
  simp only [CollatzResearch.WordTrace]
  refine ⟨287106418650990744225283913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191404279100660496150189275 287106418650990744225283913)
  ·
    refine ⟨215329813988243058168962935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287106418650990744225283913 215329813988243058168962935)
    ·
      refine ⟨322994720982364587253444403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215329813988243058168962935 322994720982364587253444403)
      ·
        refine ⟨484492081473546880880166605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322994720982364587253444403 484492081473546880880166605)
        ·
          refine ⟨181684530552580080330062477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484492081473546880880166605 181684530552580080330062477)
          ·
            refine ⟨68131698957217530123773429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181684530552580080330062477 68131698957217530123773429)
            ·
              refine ⟨6387346777239143449103759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68131698957217530123773429 6387346777239143449103759)
              ·
                refine ⟨9581020165858715173655639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6387346777239143449103759 9581020165858715173655639)
                ·
                  refine ⟨14371530248788072760483459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9581020165858715173655639 14371530248788072760483459)
                  ·
                    refine ⟨21557295373182109140725189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14371530248788072760483459 21557295373182109140725189)
                    ·
                      refine ⟨4041992882471645463885973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21557295373182109140725189 4041992882471645463885973)
                      ·
                        rfl

theorem cell23_7871753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 1, 4].length) (baseStart_7871753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871753 prefixEnd_7871753 := by exact prefixLift 7871753
  have htrace : WordTrace (prefixWord ++ tailWord_7871753) baseStart_7871753 baseEnd_7871753 := by
    simpa [prefixWord, tailWord_7871753, baseEnd_7871753] using wordTrace_append hprefix tailTrace_7871753
  have hstable : (prefixWord ++ tailWord_7871753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871753).length < 2 ^ (prefixWord ++ tailWord_7871753).sum := by decide
  have hdescent : baseEnd_7871753 < baseStart_7871753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871756 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_7871756 : Nat := 118140960795 + 7871756 * 2 ^ 59
def prefixEnd_7871756 : Nat := 4983230072969 + 3 ^ 40 * 7871756 * 2
def baseEnd_7871756 : Nat := 4041994422913608952148459

theorem tailTrace_7871756 : CollatzResearch.WordTrace tailWord_7871756 prefixEnd_7871756 4041994422913608952148459 := by
  unfold tailWord_7871756
  simp only [CollatzResearch.WordTrace]
  refine ⟨143553264034989937868821561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191404352046653250491762081 143553264034989937868821561)
  ·
    refine ⟨107664948026242453401616171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143553264034989937868821561 107664948026242453401616171)
    ·
      refine ⟨161497422039363680102424257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107664948026242453401616171 161497422039363680102424257)
      ·
        refine ⟨121123066529522760076818193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161497422039363680102424257 121123066529522760076818193)
        ·
          refine ⟨90842299897142070057613645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121123066529522760076818193 90842299897142070057613645)
          ·
            refine ⟨34065862461428276271605117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90842299897142070057613645 34065862461428276271605117)
            ·
              refine ⟨12774698423035603601851919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34065862461428276271605117 12774698423035603601851919)
              ·
                refine ⟨19162047634553405402777879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12774698423035603601851919 19162047634553405402777879)
                ·
                  refine ⟨28743071451830108104166819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19162047634553405402777879 28743071451830108104166819)
                  ·
                    refine ⟨43114607177745162156250229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28743071451830108104166819 43114607177745162156250229)
                    ·
                      refine ⟨4041994422913608952148459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43114607177745162156250229 4041994422913608952148459)
                      ·
                        rfl

theorem cell23_7871756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_7871756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871756 prefixEnd_7871756 := by exact prefixLift 7871756
  have htrace : WordTrace (prefixWord ++ tailWord_7871756) baseStart_7871756 baseEnd_7871756 := by
    simpa [prefixWord, tailWord_7871756, baseEnd_7871756] using wordTrace_append hprefix tailTrace_7871756
  have hstable : (prefixWord ++ tailWord_7871756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871756).length < 2 ^ (prefixWord ++ tailWord_7871756).sum := by decide
  have hdescent : baseEnd_7871756 < baseStart_7871756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871773 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_7871773 : Nat := 118140960795 + 7871773 * 2 ^ 59
def prefixEnd_7871773 : Nat := 4983230072969 + 3 ^ 40 * 7871773 * 2
def baseEnd_7871773 : Nat := 4042003152084735385635881

theorem tailTrace_7871773 : CollatzResearch.WordTrace tailWord_7871773 prefixEnd_7871773 4042003152084735385635881 := by
  unfold tailWord_7871773
  simp only [CollatzResearch.WordTrace]
  refine ⟨287107148110918287641011973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191404765407278858427341315 287107148110918287641011973)
  ·
    refine ⟨53832590270797178932689745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287107148110918287641011973 53832590270797178932689745)
    ·
      refine ⟨40374442703097884199517309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53832590270797178932689745 40374442703097884199517309)
      ·
        refine ⟨15140416013661706574818991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40374442703097884199517309 15140416013661706574818991)
        ·
          refine ⟨22710624020492559862228487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15140416013661706574818991 22710624020492559862228487)
          ·
            refine ⟨34065936030738839793342731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22710624020492559862228487 34065936030738839793342731)
            ·
              refine ⟨51098904046108259690014097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34065936030738839793342731 51098904046108259690014097)
              ·
                refine ⟨38324178034581194767510573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51098904046108259690014097 38324178034581194767510573)
                ·
                  refine ⟨14371566762967948037816465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38324178034581194767510573 14371566762967948037816465)
                  ·
                    refine ⟨10778675072225961028362349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14371566762967948037816465 10778675072225961028362349)
                    ·
                      refine ⟨4042003152084735385635881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778675072225961028362349 4042003152084735385635881)
                      ·
                        rfl

theorem cell23_7871773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_7871773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871773 prefixEnd_7871773 := by exact prefixLift 7871773
  have htrace : WordTrace (prefixWord ++ tailWord_7871773) baseStart_7871773 baseEnd_7871773 := by
    simpa [prefixWord, tailWord_7871773, baseEnd_7871773] using wordTrace_append hprefix tailTrace_7871773
  have hstable : (prefixWord ++ tailWord_7871773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871773).length < 2 ^ (prefixWord ++ tailWord_7871773).sum := by decide
  have hdescent : baseEnd_7871773 < baseStart_7871773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871820 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_7871820 : Nat := 118140960795 + 7871820 * 2 ^ 59
def prefixEnd_7871820 : Nat := 4983230072969 + 3 ^ 40 * 7871820 * 2
def baseEnd_7871820 : Nat := 4042027285675496701748165

theorem tailTrace_7871820 : CollatzResearch.WordTrace tailWord_7871820 prefixEnd_7871820 4042027285675496701748165 := by
  unfold tailWord_7871820
  simp only [CollatzResearch.WordTrace]
  refine ⟨143554431170874007333986457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191405908227832009778648609 143554431170874007333986457)
  ·
    refine ⟨107665823378155505500489843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143554431170874007333986457 107665823378155505500489843)
    ·
      refine ⟨161498735067233258250734765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107665823378155505500489843 161498735067233258250734765)
      ·
        refine ⟨60562025650212471844025537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161498735067233258250734765 60562025650212471844025537)
        ·
          refine ⟨45421519237659353883019153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60562025650212471844025537 45421519237659353883019153)
          ·
            refine ⟨34066139428244515412264365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45421519237659353883019153 34066139428244515412264365)
            ·
              refine ⟨12774802285591693279599137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34066139428244515412264365 12774802285591693279599137)
              ·
                refine ⟨9581101714193769959699353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12774802285591693279599137 9581101714193769959699353)
                ·
                  refine ⟨7185826285645327469774515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9581101714193769959699353 7185826285645327469774515)
                  ·
                    refine ⟨10778739428467991204661773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7185826285645327469774515 10778739428467991204661773)
                    ·
                      refine ⟨4042027285675496701748165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10778739428467991204661773 4042027285675496701748165)
                      ·
                        rfl

theorem cell23_7871820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_7871820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871820 prefixEnd_7871820 := by exact prefixLift 7871820
  have htrace : WordTrace (prefixWord ++ tailWord_7871820) baseStart_7871820 baseEnd_7871820 := by
    simpa [prefixWord, tailWord_7871820, baseEnd_7871820] using wordTrace_append hprefix tailTrace_7871820
  have hstable : (prefixWord ++ tailWord_7871820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871820).length < 2 ^ (prefixWord ++ tailWord_7871820).sum := by decide
  have hdescent : baseEnd_7871820 < baseStart_7871820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871847 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_7871847 : Nat := 118140960795 + 7871847 * 2 ^ 59
def prefixEnd_7871847 : Nat := 4983230072969 + 3 ^ 40 * 7871847 * 2
def baseEnd_7871847 : Nat := 4042041149653168096110541

theorem tailTrace_7871847 : CollatzResearch.WordTrace tailWord_7871847 prefixEnd_7871847 4042041149653168096110541 := by
  unfold tailWord_7871847
  simp only [CollatzResearch.WordTrace]
  refine ⟨287109847112650198279205795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191406564741766798852803863 287109847112650198279205795)
  ·
    refine ⟨430664770668975297418808693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287109847112650198279205795 430664770668975297418808693)
    ·
      refine ⟨40374822250216434133013315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 430664770668975297418808693 40374822250216434133013315)
      ·
        refine ⟨60562233375324651199519973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40374822250216434133013315 60562233375324651199519973)
        ·
          refine ⟨11355418757873372099909995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60562233375324651199519973 11355418757873372099909995)
          ·
            refine ⟨17033128136810058149864993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355418757873372099909995 17033128136810058149864993)
            ·
              refine ⟨12774846102607543612398745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17033128136810058149864993 12774846102607543612398745)
              ·
                refine ⟨9581134576955657709299059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12774846102607543612398745 9581134576955657709299059)
                ·
                  refine ⟨14371701865433486563948589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9581134576955657709299059 14371701865433486563948589)
                  ·
                    refine ⟨5389388199537557461480721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14371701865433486563948589 5389388199537557461480721)
                    ·
                      refine ⟨4042041149653168096110541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5389388199537557461480721 4042041149653168096110541)
                      ·
                        rfl

theorem cell23_7871847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_7871847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871847 prefixEnd_7871847 := by exact prefixLift 7871847
  have htrace : WordTrace (prefixWord ++ tailWord_7871847) baseStart_7871847 baseEnd_7871847 := by
    simpa [prefixWord, tailWord_7871847, baseEnd_7871847] using wordTrace_append hprefix tailTrace_7871847
  have hstable : (prefixWord ++ tailWord_7871847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871847).length < 2 ^ (prefixWord ++ tailWord_7871847).sum := by decide
  have hdescent : baseEnd_7871847 < baseStart_7871847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871849 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 9]
def baseStart_7871849 : Nat := 118140960795 + 7871849 * 2 ^ 59
def prefixEnd_7871849 : Nat := 4983230072969 + 3 ^ 40 * 7871849 * 2
def baseEnd_7871849 : Nat := 449115797401608565365059

theorem tailTrace_7871849 : CollatzResearch.WordTrace tailWord_7871849 prefixEnd_7871849 449115797401608565365059 := by
  unfold tailWord_7871849
  simp only [CollatzResearch.WordTrace]
  refine ⟨287109920058642952620778601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191406613372428635080519067 287109920058642952620778601)
  ·
    refine ⟨215332440043982214465583951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287109920058642952620778601 215332440043982214465583951)
    ·
      refine ⟨322998660065973321698375927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215332440043982214465583951 322998660065973321698375927)
      ·
        refine ⟨484497990098959982547563891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322998660065973321698375927 484497990098959982547563891)
        ·
          refine ⟨726746985148439973821345837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484497990098959982547563891 726746985148439973821345837)
          ·
            refine ⟨272530119430664990183004689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726746985148439973821345837 272530119430664990183004689)
            ·
              refine ⟨204397589572998742637253517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272530119430664990183004689 204397589572998742637253517)
              ·
                refine ⟨76649096089874528488970069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204397589572998742637253517 76649096089874528488970069)
                ·
                  refine ⟨449115797401608565365059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76649096089874528488970069 449115797401608565365059)
                  ·
                    rfl

theorem cell23_7871849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_7871849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871849 prefixEnd_7871849 := by exact prefixLift 7871849
  have htrace : WordTrace (prefixWord ++ tailWord_7871849) baseStart_7871849 baseEnd_7871849 := by
    simpa [prefixWord, tailWord_7871849, baseEnd_7871849] using wordTrace_append hprefix tailTrace_7871849
  have hstable : (prefixWord ++ tailWord_7871849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871849).length < 2 ^ (prefixWord ++ tailWord_7871849).sum := by decide
  have hdescent : baseEnd_7871849 < baseStart_7871849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871859 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7]
def baseStart_7871859 : Nat := 118140960795 + 7871859 * 2 ^ 59
def prefixEnd_7871859 : Nat := 4983230072969 + 3 ^ 40 * 7871859 * 2
def baseEnd_7871859 : Nat := 4042047311421022049160485

theorem tailTrace_7871859 : CollatzResearch.WordTrace tailWord_7871859 prefixEnd_7871859 4042047311421022049160485 := by
  unfold tailWord_7871859
  simp only [CollatzResearch.WordTrace]
  refine ⟨287110284788606724328642631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191406856525737816219095087 287110284788606724328642631)
  ·
    refine ⟨430665427182910086492963947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287110284788606724328642631 430665427182910086492963947)
    ·
      refine ⟨645998140774365129739445921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430665427182910086492963947 645998140774365129739445921)
      ·
        refine ⟨484498605580773847304584441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645998140774365129739445921 484498605580773847304584441)
        ·
          refine ⟨363373954185580385478438331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484498605580773847304584441 363373954185580385478438331)
          ·
            refine ⟨545060931278370578217657497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363373954185580385478438331 545060931278370578217657497)
            ·
              refine ⟨408795698458777933663243123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545060931278370578217657497 408795698458777933663243123)
              ·
                refine ⟨613193547688166900494864685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408795698458777933663243123 613193547688166900494864685)
                ·
                  refine ⟨229947580383062587685574257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613193547688166900494864685 229947580383062587685574257)
                  ·
                    refine ⟨172460685287296940764180693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229947580383062587685574257 172460685287296940764180693)
                    ·
                      refine ⟨4042047311421022049160485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172460685287296940764180693 4042047311421022049160485)
                      ·
                        rfl

theorem cell23_7871859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_7871859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871859 prefixEnd_7871859 := by exact prefixLift 7871859
  have htrace : WordTrace (prefixWord ++ tailWord_7871859) baseStart_7871859 baseEnd_7871859 := by
    simpa [prefixWord, tailWord_7871859, baseEnd_7871859] using wordTrace_append hprefix tailTrace_7871859
  have hstable : (prefixWord ++ tailWord_7871859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871859).length < 2 ^ (prefixWord ++ tailWord_7871859).sum := by decide
  have hdescent : baseEnd_7871859 < baseStart_7871859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871916 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_7871916 : Nat := 118140960795 + 7871916 * 2 ^ 59
def prefixEnd_7871916 : Nat := 4983230072969 + 3 ^ 40 * 7871916 * 2
def baseEnd_7871916 : Nat := 4042076579818328326147723

theorem tailTrace_7871916 : CollatzResearch.WordTrace tailWord_7871916 prefixEnd_7871916 4042076579818328326147723 := by
  unfold tailWord_7871916
  simp only [CollatzResearch.WordTrace]
  refine ⟨143556181874700111531733801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191408242499600148708978401 143556181874700111531733801)
  ·
    refine ⟨107667136406025083648800351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143556181874700111531733801 107667136406025083648800351)
    ·
      refine ⟨161500704609037625473200527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107667136406025083648800351 161500704609037625473200527)
      ·
        refine ⟨242251056913556438209800791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161500704609037625473200527 242251056913556438209800791)
        ·
          refine ⟨363376585370334657314701187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242251056913556438209800791 363376585370334657314701187)
          ·
            refine ⟨545064878055501985972051781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363376585370334657314701187 545064878055501985972051781)
            ·
              refine ⟨102199664635406622369759709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545064878055501985972051781 102199664635406622369759709)
              ·
                refine ⟨38324874238277483388659891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102199664635406622369759709 38324874238277483388659891)
                ·
                  refine ⟨57487311357416225082989837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38324874238277483388659891 57487311357416225082989837)
                  ·
                    refine ⟨21557741759031084406121189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57487311357416225082989837 21557741759031084406121189)
                    ·
                      refine ⟨4042076579818328326147723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21557741759031084406121189 4042076579818328326147723)
                      ·
                        rfl

theorem cell23_7871916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_7871916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871916 prefixEnd_7871916 := by exact prefixLift 7871916
  have htrace : WordTrace (prefixWord ++ tailWord_7871916) baseStart_7871916 baseEnd_7871916 := by
    simpa [prefixWord, tailWord_7871916, baseEnd_7871916] using wordTrace_append hprefix tailTrace_7871916
  have hstable : (prefixWord ++ tailWord_7871916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871916).length < 2 ^ (prefixWord ++ tailWord_7871916).sum := by decide
  have hdescent : baseEnd_7871916 < baseStart_7871916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871933 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7871933 : Nat := 118140960795 + 7871933 * 2 ^ 59
def prefixEnd_7871933 : Nat := 4983230072969 + 3 ^ 40 * 7871933 * 2
def baseEnd_7871933 : Nat := 4042085308989454759635145

theorem tailTrace_7871933 : CollatzResearch.WordTrace tailWord_7871933 prefixEnd_7871933 4042085308989454759635145 := by
  unfold tailWord_7871933
  simp only [CollatzResearch.WordTrace]
  refine ⟨287112983790338634966836453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191408655860225756644557635 287112983790338634966836453)
  ·
    refine ⟨53833684460688494056281835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287112983790338634966836453 53833684460688494056281835)
    ·
      refine ⟨80750526691032741084422753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53833684460688494056281835 80750526691032741084422753)
      ·
        refine ⟨60562895018274555813317065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80750526691032741084422753 60562895018274555813317065)
        ·
          refine ⟨45422171263705916859987799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60562895018274555813317065 45422171263705916859987799)
          ·
            refine ⟨68133256895558875289981699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45422171263705916859987799 68133256895558875289981699)
            ·
              refine ⟨102199885343338312934972549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68133256895558875289981699 102199885343338312934972549)
              ·
                refine ⟨19162478501875933675307353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102199885343338312934972549 19162478501875933675307353)
                ·
                  refine ⟨14371858876406950256480515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19162478501875933675307353 14371858876406950256480515)
                  ·
                    refine ⟨21557788314610425384720773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14371858876406950256480515 21557788314610425384720773)
                    ·
                      refine ⟨4042085308989454759635145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21557788314610425384720773 4042085308989454759635145)
                      ·
                        rfl

theorem cell23_7871933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7871933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871933 prefixEnd_7871933 := by exact prefixLift 7871933
  have htrace : WordTrace (prefixWord ++ tailWord_7871933) baseStart_7871933 baseEnd_7871933 := by
    simpa [prefixWord, tailWord_7871933, baseEnd_7871933] using wordTrace_append hprefix tailTrace_7871933
  have hstable : (prefixWord ++ tailWord_7871933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871933).length < 2 ^ (prefixWord ++ tailWord_7871933).sum := by decide
  have hdescent : baseEnd_7871933 < baseStart_7871933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871943 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 3, 4]
def baseStart_7871943 : Nat := 118140960795 + 7871943 * 2 ^ 59
def prefixEnd_7871943 : Nat := 4983230072969 + 3 ^ 40 * 7871943 * 2
def baseEnd_7871943 : Nat := 1347363481265333240170033

theorem tailTrace_7871943 : CollatzResearch.WordTrace tailWord_7871943 prefixEnd_7871943 1347363481265333240170033 := by
  unfold tailWord_7871943
  simp only [CollatzResearch.WordTrace]
  refine ⟨287113348520302406674700483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191408899013534937783133655 287113348520302406674700483)
  ·
    refine ⟨430670022780453610012050725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287113348520302406674700483 430670022780453610012050725)
    ·
      refine ⟨80750629271335051877259511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430670022780453610012050725 80750629271335051877259511)
      ·
        refine ⟨121125943907002577815889267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80750629271335051877259511 121125943907002577815889267)
        ·
          refine ⟨181688915860503866723833901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121125943907002577815889267 181688915860503866723833901)
          ·
            refine ⟨68133343447688950021437713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181688915860503866723833901 68133343447688950021437713)
            ·
              refine ⟨51100007585766712516078285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68133343447688950021437713 51100007585766712516078285)
              ·
                refine ⟨19162502844662517193529357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51100007585766712516078285 19162502844662517193529357)
                ·
                  refine ⟨7185938566748443947573509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19162502844662517193529357 7185938566748443947573509)
                  ·
                    refine ⟨1347363481265333240170033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7185938566748443947573509 1347363481265333240170033)
                    ·
                      rfl

theorem cell23_7871943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_7871943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7871943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7871943 prefixEnd_7871943 := by exact prefixLift 7871943
  have htrace : WordTrace (prefixWord ++ tailWord_7871943) baseStart_7871943 baseEnd_7871943 := by
    simpa [prefixWord, tailWord_7871943, baseEnd_7871943] using wordTrace_append hprefix tailTrace_7871943
  have hstable : (prefixWord ++ tailWord_7871943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871943).length < 2 ^ (prefixWord ++ tailWord_7871943).sum := by decide
  have hdescent : baseEnd_7871943 < baseStart_7871943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
