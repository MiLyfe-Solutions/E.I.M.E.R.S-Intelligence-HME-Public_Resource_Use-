import V185TrunkScan23Chunk0085

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_511286 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_511286 : Nat := 118140960795 + 511286 * 2 ^ 59
def prefixEnd_511286 : Nat := 4983230072969 + 3 ^ 40 * 511286 * 2
def baseEnd_511286 : Nat := 87511823304930608291215

theorem tailTrace_511286 : CollatzResearch.WordTrace tailWord_511286 prefixEnd_511286 87511823304930608291215 := by
  unfold tailWord_511286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165508276606601096372107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12432088283803745027969141 1165508276606601096372107)
  ·
    refine ⟨1748262414909901644558161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1165508276606601096372107 1748262414909901644558161)
    ·
      refine ⟨1311196811182426233418621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1748262414909901644558161 1311196811182426233418621)
      ·
        refine ⟨491698804193409837531983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1311196811182426233418621 491698804193409837531983)
        ·
          refine ⟨737548206290114756297975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491698804193409837531983 737548206290114756297975)
          ·
            refine ⟨1106322309435172134446963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737548206290114756297975 1106322309435172134446963)
            ·
              refine ⟨1659483464152758201670445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106322309435172134446963 1659483464152758201670445)
              ·
                refine ⟨622306299057284325626417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1659483464152758201670445 622306299057284325626417)
                ·
                  refine ⟨466729724292963244219813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622306299057284325626417 466729724292963244219813)
                  ·
                    refine ⟨87511823304930608291215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466729724292963244219813 87511823304930608291215)
                    ·
                      rfl

theorem cell23_511286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_511286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511286 prefixEnd_511286 := by exact prefixLift 511286
  have htrace : WordTrace (prefixWord ++ tailWord_511286) baseStart_511286 baseEnd_511286 := by
    simpa [prefixWord, tailWord_511286, baseEnd_511286] using wordTrace_append hprefix tailTrace_511286
  have hstable : (prefixWord ++ tailWord_511286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511286).length < 2 ^ (prefixWord ++ tailWord_511286).sum := by decide
  have hdescent : baseEnd_511286 < baseStart_511286 := by decide
  rcases family_descends (prefixWord ++ tailWord_511286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511372 : List Nat := [2, 2, 1, 2, 1, 3, 4, 3, 5]
def baseStart_511372 : Nat := 118140960795 + 511372 * 2 ^ 59
def prefixEnd_511372 : Nat := 4983230072969 + 3 ^ 40 * 511372 * 2
def baseEnd_511372 : Nat := 29175514361230943155361

theorem tailTrace_511372 : CollatzResearch.WordTrace tailWord_511372 prefixEnd_511372 29175514361230943155361 := by
  unfold tailWord_511372
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325634551697027114792185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12434179402262702819722913 9325634551697027114792185)
  ·
    refine ⟨6994225913772770336094139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9325634551697027114792185 6994225913772770336094139)
    ·
      refine ⟨10491338870659155504141209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6994225913772770336094139 10491338870659155504141209)
      ·
        refine ⟨7868504152994366628105907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10491338870659155504141209 7868504152994366628105907)
        ·
          refine ⟨11802756229491549942158861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868504152994366628105907 11802756229491549942158861)
          ·
            refine ⟨4426033586059331228309573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11802756229491549942158861 4426033586059331228309573)
            ·
              refine ⟨829881297386124605308045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4426033586059331228309573 829881297386124605308045)
              ·
                refine ⟨311205486519796726990517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829881297386124605308045 311205486519796726990517)
                ·
                  refine ⟨29175514361230943155361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311205486519796726990517 29175514361230943155361)
                  ·
                    rfl

theorem cell23_511372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_511372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511372 prefixEnd_511372 := by exact prefixLift 511372
  have htrace : WordTrace (prefixWord ++ tailWord_511372) baseStart_511372 baseEnd_511372 := by
    simpa [prefixWord, tailWord_511372, baseEnd_511372] using wordTrace_append hprefix tailTrace_511372
  have hstable : (prefixWord ++ tailWord_511372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511372).length < 2 ^ (prefixWord ++ tailWord_511372).sum := by decide
  have hdescent : baseEnd_511372 < baseStart_511372 := by decide
  rcases family_descends (prefixWord ++ tailWord_511372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511400 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_511400 : Nat := 118140960795 + 511400 * 2 ^ 59
def prefixEnd_511400 : Nat := 4983230072969 + 3 ^ 40 * 511400 * 2
def baseEnd_511400 : Nat := 262594006709404378848121

theorem tailTrace_511400 : CollatzResearch.WordTrace tailWord_511400 prefixEnd_511400 262594006709404378848121 := by
  unfold tailWord_511400
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326145173646307505801827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12434860231528410007735769 9326145173646307505801827)
  ·
    refine ⟨13989217760469461258702741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9326145173646307505801827 13989217760469461258702741)
    ·
      refine ⟨655744582522005996501691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13989217760469461258702741 655744582522005996501691)
      ·
        refine ⟨983616873783008994752537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655744582522005996501691 983616873783008994752537)
        ·
          refine ⟨737712655337256746064403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983616873783008994752537 737712655337256746064403)
          ·
            refine ⟨1106568983005885119096605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737712655337256746064403 1106568983005885119096605)
            ·
              refine ⟨414963368627206919661227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1106568983005885119096605 414963368627206919661227)
              ·
                refine ⟨622445052940810379491841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414963368627206919661227 622445052940810379491841)
                ·
                  refine ⟨466833789705607784618881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622445052940810379491841 466833789705607784618881)
                  ·
                    refine ⟨350125342279205838464161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 466833789705607784618881 350125342279205838464161)
                    ·
                      refine ⟨262594006709404378848121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350125342279205838464161 262594006709404378848121)
                      ·
                        rfl

theorem cell23_511400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_511400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511400 prefixEnd_511400 := by exact prefixLift 511400
  have htrace : WordTrace (prefixWord ++ tailWord_511400) baseStart_511400 baseEnd_511400 := by
    simpa [prefixWord, tailWord_511400, baseEnd_511400] using wordTrace_append hprefix tailTrace_511400
  have hstable : (prefixWord ++ tailWord_511400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511400).length < 2 ^ (prefixWord ++ tailWord_511400).sum := by decide
  have hdescent : baseEnd_511400 < baseStart_511400 := by decide
  rcases family_descends (prefixWord ++ tailWord_511400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511422 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_511422 : Nat := 118140960795 + 511422 * 2 ^ 59
def prefixEnd_511422 : Nat := 4983230072969 + 3 ^ 40 * 511422 * 2
def baseEnd_511422 : Nat := 262605303283803292773019

theorem tailTrace_511422 : CollatzResearch.WordTrace tailWord_511422 prefixEnd_511422 262605303283803292773019 := by
  unfold tailWord_511422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2331636594151614096113065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12435395168808608512603013 2331636594151614096113065)
  ·
    refine ⟨1748727445613710572084799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2331636594151614096113065 1748727445613710572084799)
    ·
      refine ⟨2623091168420565858127199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748727445613710572084799 2623091168420565858127199)
      ·
        refine ⟨3934636752630848787190799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623091168420565858127199 3934636752630848787190799)
        ·
          refine ⟨5901955128946273180786199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934636752630848787190799 5901955128946273180786199)
          ·
            refine ⟨8852932693419409771179299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901955128946273180786199 8852932693419409771179299)
            ·
              refine ⟨13279399040129114656768949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8852932693419409771179299 13279399040129114656768949)
              ·
                refine ⟨1244943660012104499072089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13279399040129114656768949 1244943660012104499072089)
                ·
                  refine ⟨933707745009078374304067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1244943660012104499072089 933707745009078374304067)
                  ·
                    refine ⟨1400561617513617561456101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 933707745009078374304067 1400561617513617561456101)
                    ·
                      refine ⟨262605303283803292773019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1400561617513617561456101 262605303283803292773019)
                      ·
                        rfl

theorem cell23_511422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_511422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511422 prefixEnd_511422 := by exact prefixLift 511422
  have htrace : WordTrace (prefixWord ++ tailWord_511422) baseStart_511422 baseEnd_511422 := by
    simpa [prefixWord, tailWord_511422, baseEnd_511422] using wordTrace_append hprefix tailTrace_511422
  have hstable : (prefixWord ++ tailWord_511422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511422).length < 2 ^ (prefixWord ++ tailWord_511422).sum := by decide
  have hdescent : baseEnd_511422 < baseStart_511422 := by decide
  rcases family_descends (prefixWord ++ tailWord_511422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511445 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 8]
def baseStart_511445 : Nat := 118140960795 + 511445 * 2 ^ 59
def prefixEnd_511445 : Nat := 4983230072969 + 3 ^ 40 * 511445 * 2
def baseEnd_511445 : Nat := 29179679259872966976157

theorem tailTrace_511445 : CollatzResearch.WordTrace tailWord_511445 prefixEnd_511445 29179679259872966976157 := by
  unfold tailWord_511445
  simp only [CollatzResearch.WordTrace]
  refine ⟨18653931632129587696991789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12435954421419725131327859 18653931632129587696991789)
  ·
    refine ⟨6995224362048595386371921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18653931632129587696991789 6995224362048595386371921)
    ·
      refine ⟨5246418271536446539778941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6995224362048595386371921 5246418271536446539778941)
      ·
        refine ⟨1967406851826167452417103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5246418271536446539778941 1967406851826167452417103)
        ·
          refine ⟨2951110277739251178625655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967406851826167452417103 2951110277739251178625655)
          ·
            refine ⟨4426665416608876767938483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951110277739251178625655 4426665416608876767938483)
            ·
              refine ⟨6639998124913315151907725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426665416608876767938483 6639998124913315151907725)
              ·
                refine ⟨2489999296842493181965397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6639998124913315151907725 2489999296842493181965397)
                ·
                  refine ⟨29179679259872966976157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2489999296842493181965397 29179679259872966976157)
                  ·
                    rfl

theorem cell23_511445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_511445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511445 prefixEnd_511445 := by exact prefixLift 511445
  have htrace : WordTrace (prefixWord ++ tailWord_511445) baseStart_511445 baseEnd_511445 := by
    simpa [prefixWord, tailWord_511445, baseEnd_511445] using wordTrace_append hprefix tailTrace_511445
  have hstable : (prefixWord ++ tailWord_511445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511445).length < 2 ^ (prefixWord ++ tailWord_511445).sum := by decide
  have hdescent : baseEnd_511445 < baseStart_511445 := by decide
  rcases family_descends (prefixWord ++ tailWord_511445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511449 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 3, 4]
def baseStart_511449 : Nat := 118140960795 + 511449 * 2 ^ 59
def prefixEnd_511449 : Nat := 4983230072969 + 3 ^ 40 * 511449 * 2
def baseEnd_511449 : Nat := 87539722420491562378465

theorem tailTrace_511449 : CollatzResearch.WordTrace tailWord_511449 prefixEnd_511449 87539722420491562378465 := by
  unfold tailWord_511449
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654077524115096380137401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12436051682743397586758267 18654077524115096380137401)
  ·
    refine ⟨13990558143086322285103051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18654077524115096380137401 13990558143086322285103051)
    ·
      refine ⟨20985837214629483427654577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13990558143086322285103051 20985837214629483427654577)
      ·
        refine ⟨15739377910972112570740933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20985837214629483427654577 15739377910972112570740933)
        ·
          refine ⟨2951133358307271107013925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15739377910972112570740933 2951133358307271107013925)
          ·
            refine ⟨553337504682613332565111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2951133358307271107013925 553337504682613332565111)
            ·
              refine ⟨830006257023919998847667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553337504682613332565111 830006257023919998847667)
              ·
                refine ⟨1245009385535879998271501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830006257023919998847667 1245009385535879998271501)
                ·
                  refine ⟨466878519575954999351813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245009385535879998271501 466878519575954999351813)
                  ·
                    refine ⟨87539722420491562378465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466878519575954999351813 87539722420491562378465)
                    ·
                      rfl

theorem cell23_511449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_511449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511449 prefixEnd_511449 := by exact prefixLift 511449
  have htrace : WordTrace (prefixWord ++ tailWord_511449) baseStart_511449 baseEnd_511449 := by
    simpa [prefixWord, tailWord_511449, baseEnd_511449] using wordTrace_append hprefix tailTrace_511449
  have hstable : (prefixWord ++ tailWord_511449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511449).length < 2 ^ (prefixWord ++ tailWord_511449).sum := by decide
  have hdescent : baseEnd_511449 < baseStart_511449 := by decide
  rcases family_descends (prefixWord ++ tailWord_511449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511500 : List Nat := [2, 2, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_511500 : Nat := 118140960795 + 511500 * 2 ^ 59
def prefixEnd_511500 : Nat := 4983230072969 + 3 ^ 40 * 511500 * 2
def baseEnd_511500 : Nat := 87548451591617995865887

theorem tailTrace_511500 : CollatzResearch.WordTrace tailWord_511500 prefixEnd_511500 87548451591617995865887 := by
  unfold tailWord_511500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327968823465166045121977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12437291764620221393495969 9327968823465166045121977)
  ·
    refine ⟨6995976617598874533841483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9327968823465166045121977 6995976617598874533841483)
    ·
      refine ⟨10493964926398311800762225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6995976617598874533841483 10493964926398311800762225)
      ·
        refine ⟨7870473694798733850571669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10493964926398311800762225 7870473694798733850571669)
        ·
          refine ⟨368928454443690649245547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7870473694798733850571669 368928454443690649245547)
          ·
            refine ⟨553392681665535973868321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368928454443690649245547 553392681665535973868321)
            ·
              refine ⟨415044511249151980401241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553392681665535973868321 415044511249151980401241)
              ·
                refine ⟨311283383436863985300931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415044511249151980401241 311283383436863985300931)
                ·
                  refine ⟨466925075155295977951397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311283383436863985300931 466925075155295977951397)
                  ·
                    refine ⟨87548451591617995865887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466925075155295977951397 87548451591617995865887)
                    ·
                      rfl

theorem cell23_511500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_511500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511500 prefixEnd_511500 := by exact prefixLift 511500
  have htrace : WordTrace (prefixWord ++ tailWord_511500) baseStart_511500 baseEnd_511500 := by
    simpa [prefixWord, tailWord_511500, baseEnd_511500] using wordTrace_append hprefix tailTrace_511500
  have hstable : (prefixWord ++ tailWord_511500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511500).length < 2 ^ (prefixWord ++ tailWord_511500).sum := by decide
  have hdescent : baseEnd_511500 < baseStart_511500 := by decide
  rcases family_descends (prefixWord ++ tailWord_511500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511505 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 3, 6]
def baseStart_511505 : Nat := 118140960795 + 511505 * 2 ^ 59
def prefixEnd_511505 : Nat := 4983230072969 + 3 ^ 40 * 511505 * 2
def baseEnd_511505 : Nat := 87549307392708822678379

theorem tailTrace_511505 : CollatzResearch.WordTrace tailWord_511505 prefixEnd_511505 87549307392708822678379 := by
  unfold tailWord_511505
  simp only [CollatzResearch.WordTrace]
  refine ⟨18656120011912217944175969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12437413341274811962783979 18656120011912217944175969)
  ·
    refine ⟨13992090008934163458131977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18656120011912217944175969 13992090008934163458131977)
    ·
      refine ⟨10494067506700622593598983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13992090008934163458131977 10494067506700622593598983)
      ·
        refine ⟨15741101260050933890398475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10494067506700622593598983 15741101260050933890398475)
        ·
          refine ⟨23611651890076400835597713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15741101260050933890398475 23611651890076400835597713)
          ·
            refine ⟨17708738917557300626698285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23611651890076400835597713 17708738917557300626698285)
            ·
              refine ⟨6640777094083987735011857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17708738917557300626698285 6640777094083987735011857)
              ·
                refine ⟨4980582820562990801258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640777094083987735011857 4980582820562990801258893)
                ·
                  refine ⟨1867718557711121550472085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4980582820562990801258893 1867718557711121550472085)
                  ·
                    refine ⟨87549307392708822678379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1867718557711121550472085 87549307392708822678379)
                    ·
                      rfl

theorem cell23_511505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_511505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511505 prefixEnd_511505 := by exact prefixLift 511505
  have htrace : WordTrace (prefixWord ++ tailWord_511505) baseStart_511505 baseEnd_511505 := by
    simpa [prefixWord, tailWord_511505, baseEnd_511505] using wordTrace_append hprefix tailTrace_511505
  have hstable : (prefixWord ++ tailWord_511505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511505).length < 2 ^ (prefixWord ++ tailWord_511505).sum := by decide
  have hdescent : baseEnd_511505 < baseStart_511505 := by decide
  rcases family_descends (prefixWord ++ tailWord_511505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511522 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_511522 : Nat := 118140960795 + 511522 * 2 ^ 59
def prefixEnd_511522 : Nat := 4983230072969 + 3 ^ 40 * 511522 * 2
def baseEnd_511522 : Nat := 87552217116417633840853

theorem tailTrace_511522 : CollatzResearch.WordTrace tailWord_511522 prefixEnd_511522 87552217116417633840853 := by
  unfold tailWord_511522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4664185013212657461886205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12437826701900419898363213 4664185013212657461886205)
  ·
    refine ⟨1749069379954746548207327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4664185013212657461886205 1749069379954746548207327)
    ·
      refine ⟨2623604069932119822310991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749069379954746548207327 2623604069932119822310991)
      ·
        refine ⟨3935406104898179733466487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623604069932119822310991 3935406104898179733466487)
        ·
          refine ⟨5903109157347269600199731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935406104898179733466487 5903109157347269600199731)
          ·
            refine ⟨8854663736020904400299597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903109157347269600199731 8854663736020904400299597)
            ·
              refine ⟨3320498901007839150112349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8854663736020904400299597 3320498901007839150112349)
              ·
                refine ⟨1245187087877939681292131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3320498901007839150112349 1245187087877939681292131)
                ·
                  refine ⟨1867780631816909521938197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245187087877939681292131 1867780631816909521938197)
                  ·
                    refine ⟨87552217116417633840853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1867780631816909521938197 87552217116417633840853)
                    ·
                      rfl

theorem cell23_511522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_511522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511522 prefixEnd_511522 := by exact prefixLift 511522
  have htrace : WordTrace (prefixWord ++ tailWord_511522) baseStart_511522 baseEnd_511522 := by
    simpa [prefixWord, tailWord_511522, baseEnd_511522] using wordTrace_append hprefix tailTrace_511522
  have hstable : (prefixWord ++ tailWord_511522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511522).length < 2 ^ (prefixWord ++ tailWord_511522).sum := by decide
  have hdescent : baseEnd_511522 < baseStart_511522 := by decide
  rcases family_descends (prefixWord ++ tailWord_511522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511555 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6]
def baseStart_511555 : Nat := 118140960795 + 511555 * 2 ^ 59
def prefixEnd_511555 : Nat := 4983230072969 + 3 ^ 40 * 511555 * 2
def baseEnd_511555 : Nat := 262673596210851272409907

theorem tailTrace_511555 : CollatzResearch.WordTrace tailWord_511555 prefixEnd_511555 262673596210851272409907 := by
  unfold tailWord_511555
  simp only [CollatzResearch.WordTrace]
  refine ⟨18657943661731076483496119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12438629107820717655664079 18657943661731076483496119)
  ·
    refine ⟨27986915492596614725244179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18657943661731076483496119 27986915492596614725244179)
    ·
      refine ⟨41980373238894922087866269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27986915492596614725244179 41980373238894922087866269)
      ·
        refine ⟨15742639964585595782949851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41980373238894922087866269 15742639964585595782949851)
        ·
          refine ⟨23613959946878393674424777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15742639964585595782949851 23613959946878393674424777)
          ·
            refine ⟨17710469960158795255818583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23613959946878393674424777 17710469960158795255818583)
            ·
              refine ⟨26565704940238192883727875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17710469960158795255818583 26565704940238192883727875)
              ·
                refine ⟨39848557410357289325591813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26565704940238192883727875 39848557410357289325591813)
                ·
                  refine ⟨7471604514441991748548465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39848557410357289325591813 7471604514441991748548465)
                  ·
                    refine ⟨5603703385831493811411349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471604514441991748548465 5603703385831493811411349)
                    ·
                      refine ⟨262673596210851272409907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5603703385831493811411349 262673596210851272409907)
                      ·
                        rfl

theorem cell23_511555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_511555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511555 prefixEnd_511555 := by exact prefixLift 511555
  have htrace : WordTrace (prefixWord ++ tailWord_511555) baseStart_511555 baseEnd_511555 := by
    simpa [prefixWord, tailWord_511555, baseEnd_511555] using wordTrace_append hprefix tailTrace_511555
  have hstable : (prefixWord ++ tailWord_511555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511555).length < 2 ^ (prefixWord ++ tailWord_511555).sum := by decide
  have hdescent : baseEnd_511555 < baseStart_511555 := by decide
  rcases family_descends (prefixWord ++ tailWord_511555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511597 : List Nat := [1, 5, 1, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_511597 : Nat := 118140960795 + 511597 * 2 ^ 59
def prefixEnd_511597 : Nat := 4983230072969 + 3 ^ 40 * 511597 * 2
def baseEnd_511597 : Nat := 262695162398340108084715

theorem tailTrace_511597 : CollatzResearch.WordTrace tailWord_511597 prefixEnd_511597 262695162398340108084715 := by
  unfold tailWord_511597
  simp only [CollatzResearch.WordTrace]
  refine ⟨18659475527578917656525045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12439650351719278437683363 18659475527578917656525045)
  ·
    refine ⟨1749325830710523530299223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18659475527578917656525045 1749325830710523530299223)
    ·
      refine ⟨2623988746065785295448835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749325830710523530299223 2623988746065785295448835)
      ·
        refine ⟨3935983119098677943173253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623988746065785295448835 3935983119098677943173253)
        ·
          refine ⟨737996834831002114344985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3935983119098677943173253 737996834831002114344985)
          ·
            refine ⟨553497626123251585758739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737996834831002114344985 553497626123251585758739)
            ·
              refine ⟨830246439184877378638109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553497626123251585758739 830246439184877378638109)
              ·
                refine ⟨311342414694329016989291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830246439184877378638109 311342414694329016989291)
                ·
                  refine ⟨467013622041493525483937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311342414694329016989291 467013622041493525483937)
                  ·
                    refine ⟨350260216531120144112953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 467013622041493525483937 350260216531120144112953)
                    ·
                      refine ⟨262695162398340108084715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350260216531120144112953 262695162398340108084715)
                      ·
                        rfl

theorem cell23_511597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_511597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511597 prefixEnd_511597 := by exact prefixLift 511597
  have htrace : WordTrace (prefixWord ++ tailWord_511597) baseStart_511597 baseEnd_511597 := by
    simpa [prefixWord, tailWord_511597, baseEnd_511597] using wordTrace_append hprefix tailTrace_511597
  have hstable : (prefixWord ++ tailWord_511597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511597).length < 2 ^ (prefixWord ++ tailWord_511597).sum := by decide
  have hdescent : baseEnd_511597 < baseStart_511597 := by decide
  rcases family_descends (prefixWord ++ tailWord_511597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511630 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_511630 : Nat := 118140960795 + 511630 * 2 ^ 59
def prefixEnd_511630 : Nat := 4983230072969 + 3 ^ 40 * 511630 * 2
def baseEnd_511630 : Nat := 262712107259938478972063

theorem tailTrace_511630 : CollatzResearch.WordTrace tailWord_511630 prefixEnd_511630 262712107259938478972063 := by
  unfold tailWord_511630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332584892057420536559543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12440452757639576194984229 2332584892057420536559543)
  ·
    refine ⟨3498877338086130804839315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2332584892057420536559543 3498877338086130804839315)
    ·
      refine ⟨5248316007129196207258973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498877338086130804839315 5248316007129196207258973)
      ·
        refine ⟨1968118502673448577722115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5248316007129196207258973 1968118502673448577722115)
        ·
          refine ⟨2952177754010172866583173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968118502673448577722115 2952177754010172866583173)
          ·
            refine ⟨553533328876907412484345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2952177754010172866583173 553533328876907412484345)
            ·
              refine ⟨415149996657680559363259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553533328876907412484345 415149996657680559363259)
              ·
                refine ⟨622724994986520839044889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415149996657680559363259 622724994986520839044889)
                ·
                  refine ⟨467043746239890629283667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622724994986520839044889 467043746239890629283667)
                  ·
                    refine ⟨700565619359835943925501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467043746239890629283667 700565619359835943925501)
                    ·
                      refine ⟨262712107259938478972063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 700565619359835943925501 262712107259938478972063)
                      ·
                        rfl

theorem cell23_511630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_511630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511630 prefixEnd_511630 := by exact prefixLift 511630
  have htrace : WordTrace (prefixWord ++ tailWord_511630) baseStart_511630 baseEnd_511630 := by
    simpa [prefixWord, tailWord_511630, baseEnd_511630] using wordTrace_append hprefix tailTrace_511630
  have hstable : (prefixWord ++ tailWord_511630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511630).length < 2 ^ (prefixWord ++ tailWord_511630).sum := by decide
  have hdescent : baseEnd_511630 < baseStart_511630 := by decide
  rcases family_descends (prefixWord ++ tailWord_511630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511632 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_511632 : Nat := 118140960795 + 511632 * 2 ^ 59
def prefixEnd_511632 : Nat := 4983230072969 + 3 ^ 40 * 511632 * 2
def baseEnd_511632 : Nat := 262713134221247471147053

theorem tailTrace_511632 : CollatzResearch.WordTrace tailWord_511632 prefixEnd_511632 262713134221247471147053 := by
  unfold tailWord_511632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330376041226059317024575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12440501388301412422699433 9330376041226059317024575)
  ·
    refine ⟨13995564061839088975536863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9330376041226059317024575 13995564061839088975536863)
    ·
      refine ⟨20993346092758633463305295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995564061839088975536863 20993346092758633463305295)
      ·
        refine ⟨31490019139137950194957943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20993346092758633463305295 31490019139137950194957943)
        ·
          refine ⟨47235028708706925292436915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31490019139137950194957943 47235028708706925292436915)
          ·
            refine ⟨70852543063060387938655373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47235028708706925292436915 70852543063060387938655373)
            ·
              refine ⟨26569703648647645476995765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70852543063060387938655373 26569703648647645476995765)
              ·
                refine ⟨2490909717060716763468353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26569703648647645476995765 2490909717060716763468353)
                ·
                  refine ⟨1868182287795537572601265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2490909717060716763468353 1868182287795537572601265)
                  ·
                    refine ⟨1401136715846653179450949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1868182287795537572601265 1401136715846653179450949)
                    ·
                      refine ⟨262713134221247471147053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1401136715846653179450949 262713134221247471147053)
                      ·
                        rfl

theorem cell23_511632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_511632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511632 prefixEnd_511632 := by exact prefixLift 511632
  have htrace : WordTrace (prefixWord ++ tailWord_511632) baseStart_511632 baseEnd_511632 := by
    simpa [prefixWord, tailWord_511632, baseEnd_511632] using wordTrace_append hprefix tailTrace_511632
  have hstable : (prefixWord ++ tailWord_511632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511632).length < 2 ^ (prefixWord ++ tailWord_511632).sum := by decide
  have hdescent : baseEnd_511632 < baseStart_511632 := by decide
  rcases family_descends (prefixWord ++ tailWord_511632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511676 : List Nat := [2, 2, 2, 3, 1, 3, 1, 4, 5]
def baseStart_511676 : Nat := 118140960795 + 511676 * 2 ^ 59
def prefixEnd_511676 : Nat := 4983230072969 + 3 ^ 40 * 511676 * 2
def baseEnd_511676 : Nat := 29192858596671699888539

theorem tailTrace_511676 : CollatzResearch.WordTrace tailWord_511676 prefixEnd_511676 29192858596671699888539 := by
  unfold tailWord_511676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9331178447146357074325441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12441571262861809432433921 9331178447146357074325441)
  ·
    refine ⟨6998383835359767805744081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9331178447146357074325441 6998383835359767805744081)
    ·
      refine ⟨5248787876519825854308061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6998383835359767805744081 5248787876519825854308061)
      ·
        refine ⟨1968295453694934695365523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5248787876519825854308061 1968295453694934695365523)
        ·
          refine ⟨2952443180542402043048285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968295453694934695365523 2952443180542402043048285)
          ·
            refine ⟨1107166192703400766143107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2952443180542402043048285 1107166192703400766143107)
            ·
              refine ⟨1660749289055101149214661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107166192703400766143107 1660749289055101149214661)
              ·
                refine ⟨311390491697831465477749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1660749289055101149214661 311390491697831465477749)
                ·
                  refine ⟨29192858596671699888539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311390491697831465477749 29192858596671699888539)
                  ·
                    rfl

theorem cell23_511676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_511676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511676 prefixEnd_511676 := by exact prefixLift 511676
  have htrace : WordTrace (prefixWord ++ tailWord_511676) baseStart_511676 baseEnd_511676 := by
    simpa [prefixWord, tailWord_511676, baseEnd_511676] using wordTrace_append hprefix tailTrace_511676
  have hstable : (prefixWord ++ tailWord_511676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511676).length < 2 ^ (prefixWord ++ tailWord_511676).sum := by decide
  have hdescent : baseEnd_511676 < baseStart_511676 := by decide
  rcases family_descends (prefixWord ++ tailWord_511676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511679 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 7, 2]
def baseStart_511679 : Nat := 118140960795 + 511679 * 2 ^ 59
def prefixEnd_511679 : Nat := 4983230072969 + 3 ^ 40 * 511679 * 2
def baseEnd_511679 : Nat := 262737267812008787259337

theorem tailTrace_511679 : CollatzResearch.WordTrace tailWord_511679 prefixEnd_511679 262737267812008787259337 := by
  unfold tailWord_511679
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662466313281845661010091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12441644208854563774006727 18662466313281845661010091)
  ·
    refine ⟨27993699469922768491515137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18662466313281845661010091 27993699469922768491515137)
    ·
      refine ⟨20995274602442076368636353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27993699469922768491515137 20995274602442076368636353)
      ·
        refine ⟨15746455951831557276477265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20995274602442076368636353 15746455951831557276477265)
        ·
          refine ⟨11809841963873667957357949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15746455951831557276477265 11809841963873667957357949)
          ·
            refine ⟨4428690736452625484009231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11809841963873667957357949 4428690736452625484009231)
            ·
              refine ⟨6643036104678938226013847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428690736452625484009231 6643036104678938226013847)
              ·
                refine ⟨9964554157018407339020771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643036104678938226013847 9964554157018407339020771)
                ·
                  refine ⟨14946831235527611008531157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9964554157018407339020771 14946831235527611008531157)
                  ·
                    refine ⟨350316357082678383012449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14946831235527611008531157 350316357082678383012449)
                    ·
                      refine ⟨262737267812008787259337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350316357082678383012449 262737267812008787259337)
                      ·
                        rfl

theorem cell23_511679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_511679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511679 prefixEnd_511679 := by exact prefixLift 511679
  have htrace : WordTrace (prefixWord ++ tailWord_511679) baseStart_511679 baseEnd_511679 := by
    simpa [prefixWord, tailWord_511679, baseEnd_511679] using wordTrace_append hprefix tailTrace_511679
  have hstable : (prefixWord ++ tailWord_511679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511679).length < 2 ^ (prefixWord ++ tailWord_511679).sum := by decide
  have hdescent : baseEnd_511679 < baseStart_511679 := by decide
  rcases family_descends (prefixWord ++ tailWord_511679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511706 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_511706 : Nat := 118140960795 + 511706 * 2 ^ 59
def prefixEnd_511706 : Nat := 4983230072969 + 3 ^ 40 * 511706 * 2
def baseEnd_511706 : Nat := 87583710596560060540571

theorem tailTrace_511706 : CollatzResearch.WordTrace tailWord_511706 prefixEnd_511706 87583710596560060540571 := by
  unfold tailWord_511706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665862771046007318060743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12442300722789352848161981 4665862771046007318060743)
  ·
    refine ⟨6998794156569010977091115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4665862771046007318060743 6998794156569010977091115)
    ·
      refine ⟨10498191234853516465636673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6998794156569010977091115 10498191234853516465636673)
      ·
        refine ⟨7873643426140137349227505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10498191234853516465636673 7873643426140137349227505)
        ·
          refine ⟨5905232569605103011920629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7873643426140137349227505 5905232569605103011920629)
          ·
            refine ⟨553615553400478407367559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5905232569605103011920629 553615553400478407367559)
            ·
              refine ⟨830423330100717611051339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553615553400478407367559 830423330100717611051339)
              ·
                refine ⟨1245634995151076416577009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830423330100717611051339 1245634995151076416577009)
                ·
                  refine ⟨934226246363307312432757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245634995151076416577009 934226246363307312432757)
                  ·
                    refine ⟨87583710596560060540571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 934226246363307312432757 87583710596560060540571)
                    ·
                      rfl

theorem cell23_511706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_511706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511706 prefixEnd_511706 := by exact prefixLift 511706
  have htrace : WordTrace (prefixWord ++ tailWord_511706) baseStart_511706 baseEnd_511706 := by
    simpa [prefixWord, tailWord_511706, baseEnd_511706] using wordTrace_append hprefix tailTrace_511706
  have hstable : (prefixWord ++ tailWord_511706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511706).length < 2 ^ (prefixWord ++ tailWord_511706).sum := by decide
  have hdescent : baseEnd_511706 < baseStart_511706 := by decide
  rcases family_descends (prefixWord ++ tailWord_511706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511726 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_511726 : Nat := 118140960795 + 511726 * 2 ^ 59
def prefixEnd_511726 : Nat := 4983230072969 + 3 ^ 40 * 511726 * 2
def baseEnd_511726 : Nat := 262761401402770103371621

theorem tailTrace_511726 : CollatzResearch.WordTrace tailWord_511726 prefixEnd_511726 262761401402770103371621 := by
  unfold tailWord_511726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333022568013946585996379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12442787029407715125314021 2333022568013946585996379)
  ·
    refine ⟨3499533852020919878994569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333022568013946585996379 3499533852020919878994569)
    ·
      refine ⟨2624650389015689909245927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3499533852020919878994569 2624650389015689909245927)
      ·
        refine ⟨3936975583523534863868891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624650389015689909245927 3936975583523534863868891)
        ·
          refine ⟨5905463375285302295803337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936975583523534863868891 5905463375285302295803337)
          ·
            refine ⟨4429097531463976721852503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905463375285302295803337 4429097531463976721852503)
            ·
              refine ⟨6643646297195965082778755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429097531463976721852503 6643646297195965082778755)
              ·
                refine ⟨9965469445793947624168133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643646297195965082778755 9965469445793947624168133)
                ·
                  refine ⟨1868525521086365179531525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9965469445793947624168133 1868525521086365179531525)
                  ·
                    refine ⟨350348535203693471162161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868525521086365179531525 350348535203693471162161)
                    ·
                      refine ⟨262761401402770103371621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350348535203693471162161 262761401402770103371621)
                      ·
                        rfl

theorem cell23_511726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_511726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511726 prefixEnd_511726 := by exact prefixLift 511726
  have htrace : WordTrace (prefixWord ++ tailWord_511726) baseStart_511726 baseEnd_511726 := by
    simpa [prefixWord, tailWord_511726, baseEnd_511726] using wordTrace_append hprefix tailTrace_511726
  have hstable : (prefixWord ++ tailWord_511726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511726).length < 2 ^ (prefixWord ++ tailWord_511726).sum := by decide
  have hdescent : baseEnd_511726 < baseStart_511726 := by decide
  rcases family_descends (prefixWord ++ tailWord_511726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511746 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_511746 : Nat := 118140960795 + 511746 * 2 ^ 59
def prefixEnd_511746 : Nat := 4983230072969 + 3 ^ 40 * 511746 * 2
def baseEnd_511746 : Nat := 262771671015860025121529

theorem tailTrace_511746 : CollatzResearch.WordTrace tailWord_511746 prefixEnd_511746 262771671015860025121529 := by
  unfold tailWord_511746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666227501009779025924773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12443273336026077402466061 4666227501009779025924773)
  ·
    refine ⟨874917656439333567360895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4666227501009779025924773 874917656439333567360895)
    ·
      refine ⟨1312376484659000351041343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 874917656439333567360895 1312376484659000351041343)
      ·
        refine ⟨1968564726988500526562015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312376484659000351041343 1968564726988500526562015)
        ·
          refine ⟨2952847090482750789843023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968564726988500526562015 2952847090482750789843023)
          ·
            refine ⟨4429270635724126184764535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952847090482750789843023 4429270635724126184764535)
            ·
              refine ⟨6643905953586189277146803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429270635724126184764535 6643905953586189277146803)
              ·
                refine ⟨9965858930379283915720205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643905953586189277146803 9965858930379283915720205)
                ·
                  refine ⟨3737197098892231468395077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9965858930379283915720205 3737197098892231468395077)
                  ·
                    refine ⟨700724456042293400324077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3737197098892231468395077 700724456042293400324077)
                    ·
                      refine ⟨262771671015860025121529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 700724456042293400324077 262771671015860025121529)
                      ·
                        rfl

theorem cell23_511746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_511746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511746 prefixEnd_511746 := by exact prefixLift 511746
  have htrace : WordTrace (prefixWord ++ tailWord_511746) baseStart_511746 baseEnd_511746 := by
    simpa [prefixWord, tailWord_511746, baseEnd_511746] using wordTrace_append hprefix tailTrace_511746
  have hstable : (prefixWord ++ tailWord_511746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511746).length < 2 ^ (prefixWord ++ tailWord_511746).sum := by decide
  have hdescent : baseEnd_511746 < baseStart_511746 := by decide
  rcases family_descends (prefixWord ++ tailWord_511746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511770 : List Nat := [3, 1, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_511770 : Nat := 118140960795 + 511770 * 2 ^ 59
def prefixEnd_511770 : Nat := 4983230072969 + 3 ^ 40 * 511770 * 2
def baseEnd_511770 : Nat := 87594664850522643740473

theorem tailTrace_511770 : CollatzResearch.WordTrace tailWord_511770 prefixEnd_511770 87594664850522643740473 := by
  unfold tailWord_511770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666446338988042050643191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12443856903968112135048509 4666446338988042050643191)
  ·
    refine ⟨6999669508482063075964787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4666446338988042050643191 6999669508482063075964787)
    ·
      refine ⟨10499504262723094613947181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6999669508482063075964787 10499504262723094613947181)
      ·
        refine ⟨3937314098521160480230193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10499504262723094613947181 3937314098521160480230193)
        ·
          refine ⟨2952985573890870360172645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3937314098521160480230193 2952985573890870360172645)
          ·
            refine ⟨553684795104538192532371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2952985573890870360172645 553684795104538192532371)
            ·
              refine ⟨830527192656807288798557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553684795104538192532371 830527192656807288798557)
              ·
                refine ⟨311447697246302733299459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830527192656807288798557 311447697246302733299459)
                ·
                  refine ⟨467171545869454099949189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311447697246302733299459 467171545869454099949189)
                  ·
                    refine ⟨87594664850522643740473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 467171545869454099949189 87594664850522643740473)
                    ·
                      rfl

theorem cell23_511770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_511770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511770 prefixEnd_511770 := by exact prefixLift 511770
  have htrace : WordTrace (prefixWord ++ tailWord_511770) baseStart_511770 baseEnd_511770 := by
    simpa [prefixWord, tailWord_511770, baseEnd_511770] using wordTrace_append hprefix tailTrace_511770
  have hstable : (prefixWord ++ tailWord_511770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511770).length < 2 ^ (prefixWord ++ tailWord_511770).sum := by decide
  have hdescent : baseEnd_511770 < baseStart_511770 := by decide
  rcases family_descends (prefixWord ++ tailWord_511770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511793 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_511793 : Nat := 118140960795 + 511793 * 2 ^ 59
def prefixEnd_511793 : Nat := 4983230072969 + 3 ^ 40 * 511793 * 2
def baseEnd_511793 : Nat := 262795804606621341233813

theorem tailTrace_511793 : CollatzResearch.WordTrace tailWord_511793 prefixEnd_511793 262795804606621341233813 := by
  unfold tailWord_511793
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666624234868843130660033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12444416156579228753773355 18666624234868843130660033)
  ·
    refine ⟨13999968176151632347995025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18666624234868843130660033 13999968176151632347995025)
    ·
      refine ⟨10499976132113724260996269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13999968176151632347995025 10499976132113724260996269)
      ·
        refine ⟨3937491049542646597873601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10499976132113724260996269 3937491049542646597873601)
        ·
          refine ⟨2953118287156984948405201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3937491049542646597873601 2953118287156984948405201)
          ·
            refine ⟨2214838715367738711303901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2953118287156984948405201 2214838715367738711303901)
            ·
              refine ⟨830564518262902016738963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2214838715367738711303901 830564518262902016738963)
              ·
                refine ⟨1245846777394353025108445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830564518262902016738963 1245846777394353025108445)
                ·
                  refine ⟨467192541522882384415667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245846777394353025108445 467192541522882384415667)
                  ·
                    refine ⟨700788812284323576623501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467192541522882384415667 700788812284323576623501)
                    ·
                      refine ⟨262795804606621341233813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 700788812284323576623501 262795804606621341233813)
                      ·
                        rfl

theorem cell23_511793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_511793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511793 prefixEnd_511793 := by exact prefixLift 511793
  have htrace : WordTrace (prefixWord ++ tailWord_511793) baseStart_511793 baseEnd_511793 := by
    simpa [prefixWord, tailWord_511793, baseEnd_511793] using wordTrace_append hprefix tailTrace_511793
  have hstable : (prefixWord ++ tailWord_511793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511793).length < 2 ^ (prefixWord ++ tailWord_511793).sum := by decide
  have hdescent : baseEnd_511793 < baseStart_511793 := by decide
  rcases family_descends (prefixWord ++ tailWord_511793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511816 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_511816 : Nat := 118140960795 + 511816 * 2 ^ 59
def prefixEnd_511816 : Nat := 4983230072969 + 3 ^ 40 * 511816 * 2
def baseEnd_511816 : Nat := 262807614661674751246207

theorem tailTrace_511816 : CollatzResearch.WordTrace tailWord_511816 prefixEnd_511816 262807614661674751246207 := by
  unfold tailWord_511816
  simp only [CollatzResearch.WordTrace]
  refine ⟨9333731556892759029373651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12444975409190345372498201 9333731556892759029373651)
  ·
    refine ⟨14000597335339138544060477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9333731556892759029373651 14000597335339138544060477)
    ·
      refine ⟨5250224000752176954022679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14000597335339138544060477 5250224000752176954022679)
      ·
        refine ⟨7875336001128265431034019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250224000752176954022679 7875336001128265431034019)
        ·
          refine ⟨11813004001692398146551029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7875336001128265431034019 11813004001692398146551029)
          ·
            refine ⟨1107469125158662326239159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11813004001692398146551029 1107469125158662326239159)
            ·
              refine ⟨1661203687737993489358739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107469125158662326239159 1661203687737993489358739)
              ·
                refine ⟨2491805531606990234038109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661203687737993489358739 2491805531606990234038109)
                ·
                  refine ⟨934427074352621337764291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2491805531606990234038109 934427074352621337764291)
                  ·
                    refine ⟨1401640611528932006646437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 934427074352621337764291 1401640611528932006646437)
                    ·
                      refine ⟨262807614661674751246207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1401640611528932006646437 262807614661674751246207)
                      ·
                        rfl

theorem cell23_511816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_511816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511816 prefixEnd_511816 := by exact prefixLift 511816
  have htrace : WordTrace (prefixWord ++ tailWord_511816) baseStart_511816 baseEnd_511816 := by
    simpa [prefixWord, tailWord_511816, baseEnd_511816] using wordTrace_append hprefix tailTrace_511816
  have hstable : (prefixWord ++ tailWord_511816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511816).length < 2 ^ (prefixWord ++ tailWord_511816).sum := by decide
  have hdescent : baseEnd_511816 < baseStart_511816 := by decide
  rcases family_descends (prefixWord ++ tailWord_511816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511820 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 2, 3, 2]
def baseStart_511820 : Nat := 118140960795 + 511820 * 2 ^ 59
def prefixEnd_511820 : Nat := 4983230072969 + 3 ^ 40 * 511820 * 2
def baseEnd_511820 : Nat := 262809668584292735596189

theorem tailTrace_511820 : CollatzResearch.WordTrace tailWord_511820 prefixEnd_511820 262809668584292735596189 := by
  unfold tailWord_511820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9333804502885513370946457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12445072670514017827928609 9333804502885513370946457)
  ·
    refine ⟨7000353377164135028209843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9333804502885513370946457 7000353377164135028209843)
    ·
      refine ⟨10500530065746202542314765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7000353377164135028209843 10500530065746202542314765)
      ·
        refine ⟨3937698774654825953368037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10500530065746202542314765 3937698774654825953368037)
        ·
          refine ⟨738318520247779866256507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3937698774654825953368037 738318520247779866256507)
          ·
            refine ⟨1107477780371669799384761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738318520247779866256507 1107477780371669799384761)
            ·
              refine ⟨830608335278752349538571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107477780371669799384761 830608335278752349538571)
              ·
                refine ⟨1245912502918128524307857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830608335278752349538571 1245912502918128524307857)
                ·
                  refine ⟨934434377188596393230893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245912502918128524307857 934434377188596393230893)
                  ·
                    refine ⟨350412891445723647461585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 934434377188596393230893 350412891445723647461585)
                    ·
                      refine ⟨262809668584292735596189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350412891445723647461585 262809668584292735596189)
                      ·
                        rfl

theorem cell23_511820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_511820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511820 prefixEnd_511820 := by exact prefixLift 511820
  have htrace : WordTrace (prefixWord ++ tailWord_511820) baseStart_511820 baseEnd_511820 := by
    simpa [prefixWord, tailWord_511820, baseEnd_511820] using wordTrace_append hprefix tailTrace_511820
  have hstable : (prefixWord ++ tailWord_511820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511820).length < 2 ^ (prefixWord ++ tailWord_511820).sum := by decide
  have hdescent : baseEnd_511820 < baseStart_511820 := by decide
  rcases family_descends (prefixWord ++ tailWord_511820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511826 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_511826 : Nat := 118140960795 + 511826 * 2 ^ 59
def prefixEnd_511826 : Nat := 4983230072969 + 3 ^ 40 * 511826 * 2
def baseEnd_511826 : Nat := 87604249822739904040387

theorem tailTrace_511826 : CollatzResearch.WordTrace tailWord_511826 prefixEnd_511826 87604249822739904040387 := by
  unfold tailWord_511826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666956960937322441652833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12445218562499526511074221 4666956960937322441652833)
  ·
    refine ⟨3500217720702991831239625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4666956960937322441652833 3500217720702991831239625)
    ·
      refine ⟨2625163290527243873429719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3500217720702991831239625 2625163290527243873429719)
      ·
        refine ⟨3937744935790865810144579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625163290527243873429719 3937744935790865810144579)
        ·
          refine ⟨5906617403686298715216869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937744935790865810144579 5906617403686298715216869)
          ·
            refine ⟨1107490763191181009103163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5906617403686298715216869 1107490763191181009103163)
            ·
              refine ⟨1661236144786771513654745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107490763191181009103163 1661236144786771513654745)
              ·
                refine ⟨1245927108590078635241059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661236144786771513654745 1245927108590078635241059)
                ·
                  refine ⟨1868890662885117952861589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245927108590078635241059 1868890662885117952861589)
                  ·
                    refine ⟨87604249822739904040387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1868890662885117952861589 87604249822739904040387)
                    ·
                      rfl

theorem cell23_511826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_511826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511826 prefixEnd_511826 := by exact prefixLift 511826
  have htrace : WordTrace (prefixWord ++ tailWord_511826) baseStart_511826 baseEnd_511826 := by
    simpa [prefixWord, tailWord_511826, baseEnd_511826] using wordTrace_append hprefix tailTrace_511826
  have hstable : (prefixWord ++ tailWord_511826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511826).length < 2 ^ (prefixWord ++ tailWord_511826).sum := by decide
  have hdescent : baseEnd_511826 < baseStart_511826 := by decide
  rcases family_descends (prefixWord ++ tailWord_511826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511833 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 1, 1, 4]
def baseStart_511833 : Nat := 118140960795 + 511833 * 2 ^ 59
def prefixEnd_511833 : Nat := 4983230072969 + 3 ^ 40 * 511833 * 2
def baseEnd_511833 : Nat := 262816343832801184733629

theorem tailTrace_511833 : CollatzResearch.WordTrace tailWord_511833 prefixEnd_511833 262816343832801184733629 := by
  unfold tailWord_511833
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668083154723929962116153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12445388769815953308077435 18668083154723929962116153)
  ·
    refine ⟨14001062366042947471587115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18668083154723929962116153 14001062366042947471587115)
    ·
      refine ⟨21001593549064421207380673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14001062366042947471587115 21001593549064421207380673)
      ·
        refine ⟨15751195161798315905535505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21001593549064421207380673 15751195161798315905535505)
        ·
          refine ⟨11813396371348736929151629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15751195161798315905535505 11813396371348736929151629)
          ·
            refine ⟨4430023639255776348431861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11813396371348736929151629 4430023639255776348431861)
            ·
              refine ⟨415314716180229032665487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4430023639255776348431861 415314716180229032665487)
              ·
                refine ⟨622972074270343548998231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415314716180229032665487 622972074270343548998231)
                ·
                  refine ⟨934458111405515323497347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 622972074270343548998231 934458111405515323497347)
                  ·
                    refine ⟨1401687167108272985246021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 934458111405515323497347 1401687167108272985246021)
                    ·
                      refine ⟨262816343832801184733629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1401687167108272985246021 262816343832801184733629)
                      ·
                        rfl

theorem cell23_511833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_511833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511833 prefixEnd_511833 := by exact prefixLift 511833
  have htrace : WordTrace (prefixWord ++ tailWord_511833) baseStart_511833 baseEnd_511833 := by
    simpa [prefixWord, tailWord_511833, baseEnd_511833] using wordTrace_append hprefix tailTrace_511833
  have hstable : (prefixWord ++ tailWord_511833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511833).length < 2 ^ (prefixWord ++ tailWord_511833).sum := by decide
  have hdescent : baseEnd_511833 < baseStart_511833 := by decide
  rcases family_descends (prefixWord ++ tailWord_511833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511844 : List Nat := [2, 3, 1, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_511844 : Nat := 118140960795 + 511844 * 2 ^ 59
def prefixEnd_511844 : Nat := 4983230072969 + 3 ^ 40 * 511844 * 2
def baseEnd_511844 : Nat := 262821992120000641696079

theorem tailTrace_511844 : CollatzResearch.WordTrace tailWord_511844 prefixEnd_511844 262821992120000641696079 := by
  unfold tailWord_511844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334242178842039420383293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12445656238456052560511057 9334242178842039420383293)
  ·
    refine ⟨3500340817065764782643735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9334242178842039420383293 3500340817065764782643735)
    ·
      refine ⟨5250511225598647173965603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500340817065764782643735 5250511225598647173965603)
      ·
        refine ⟨7875766838397970760948405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250511225598647173965603 7875766838397970760948405)
        ·
          refine ⟨738353141099809758838913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7875766838397970760948405 738353141099809758838913)
          ·
            refine ⟨553764855824857319129185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738353141099809758838913 553764855824857319129185)
            ·
              refine ⟨415323641868642989346889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553764855824857319129185 415323641868642989346889)
              ·
                refine ⟨311492731401482242010167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415323641868642989346889 311492731401482242010167)
                ·
                  refine ⟨467239097102223363015251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311492731401482242010167 467239097102223363015251)
                  ·
                    refine ⟨700858645653335044522877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467239097102223363015251 700858645653335044522877)
                    ·
                      refine ⟨262821992120000641696079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 700858645653335044522877 262821992120000641696079)
                      ·
                        rfl

theorem cell23_511844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_511844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511844 prefixEnd_511844 := by exact prefixLift 511844
  have htrace : WordTrace (prefixWord ++ tailWord_511844) baseStart_511844 baseEnd_511844 := by
    simpa [prefixWord, tailWord_511844, baseEnd_511844] using wordTrace_append hprefix tailTrace_511844
  have hstable : (prefixWord ++ tailWord_511844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511844).length < 2 ^ (prefixWord ++ tailWord_511844).sum := by decide
  have hdescent : baseEnd_511844 < baseStart_511844 := by decide
  rcases family_descends (prefixWord ++ tailWord_511844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511866 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_511866 : Nat := 118140960795 + 511866 * 2 ^ 59
def prefixEnd_511866 : Nat := 4983230072969 + 3 ^ 40 * 511866 * 2
def baseEnd_511866 : Nat := 262833288694399555620977

theorem tailTrace_511866 : CollatzResearch.WordTrace tailWord_511866 prefixEnd_511866 262833288694399555620977 := by
  unfold tailWord_511866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667321690901094149516863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12446191175736251065378301 4667321690901094149516863)
  ·
    refine ⟨7000982536351641224275295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4667321690901094149516863 7000982536351641224275295)
    ·
      refine ⟨10501473804527461836412943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7000982536351641224275295 10501473804527461836412943)
      ·
        refine ⟨15752210706791192754619415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501473804527461836412943 15752210706791192754619415)
        ·
          refine ⟨23628316060186789131929123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15752210706791192754619415 23628316060186789131929123)
          ·
            refine ⟨35442474090280183697893685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23628316060186789131929123 35442474090280183697893685)
            ·
              refine ⟨3322731945963767221677533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35442474090280183697893685 3322731945963767221677533)
              ·
                refine ⟨1246024479736412708129075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3322731945963767221677533 1246024479736412708129075)
                ·
                  refine ⟨1869036719604619062193613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246024479736412708129075 1869036719604619062193613)
                  ·
                    refine ⟨700888769851732148322605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1869036719604619062193613 700888769851732148322605)
                    ·
                      refine ⟨262833288694399555620977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 700888769851732148322605 262833288694399555620977)
                      ·
                        rfl

theorem cell23_511866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_511866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511866 prefixEnd_511866 := by exact prefixLift 511866
  have htrace : WordTrace (prefixWord ++ tailWord_511866) baseStart_511866 baseEnd_511866 := by
    simpa [prefixWord, tailWord_511866, baseEnd_511866] using wordTrace_append hprefix tailTrace_511866
  have hstable : (prefixWord ++ tailWord_511866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511866).length < 2 ^ (prefixWord ++ tailWord_511866).sum := by decide
  have hdescent : baseEnd_511866 < baseStart_511866 := by decide
  rcases family_descends (prefixWord ++ tailWord_511866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511869 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_511869 : Nat := 118140960795 + 511869 * 2 ^ 59
def prefixEnd_511869 : Nat := 4983230072969 + 3 ^ 40 * 511869 * 2
def baseEnd_511869 : Nat := 87611609712121014627821

theorem tailTrace_511869 : CollatzResearch.WordTrace tailWord_511869 prefixEnd_511869 87611609712121014627821 := by
  unfold tailWord_511869
  simp only [CollatzResearch.WordTrace]
  refine ⟨18669396182593508110426661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12446264121729005406951107 18669396182593508110426661)
  ·
    refine ⟨3500511784236282770704999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18669396182593508110426661 3500511784236282770704999)
    ·
      refine ⟨5250767676354424156057499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500511784236282770704999 5250767676354424156057499)
      ·
        refine ⟨7876151514531636234086249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250767676354424156057499 7876151514531636234086249)
        ·
          refine ⟨5907113635898727175564687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7876151514531636234086249 5907113635898727175564687)
          ·
            refine ⟨8860670453848090763347031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907113635898727175564687 8860670453848090763347031)
            ·
              refine ⟨13291005680772136145020547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860670453848090763347031 13291005680772136145020547)
              ·
                refine ⟨19936508521158204217530821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13291005680772136145020547 19936508521158204217530821)
                ·
                  refine ⟨3738095347717163290787029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19936508521158204217530821 3738095347717163290787029)
                  ·
                    refine ⟨87611609712121014627821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3738095347717163290787029 87611609712121014627821)
                    ·
                      rfl

theorem cell23_511869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_511869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511869 prefixEnd_511869 := by exact prefixLift 511869
  have htrace : WordTrace (prefixWord ++ tailWord_511869) baseStart_511869 baseEnd_511869 := by
    simpa [prefixWord, tailWord_511869, baseEnd_511869] using wordTrace_append hprefix tailTrace_511869
  have hstable : (prefixWord ++ tailWord_511869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511869).length < 2 ^ (prefixWord ++ tailWord_511869).sum := by decide
  have hdescent : baseEnd_511869 < baseStart_511869 := by decide
  rcases family_descends (prefixWord ++ tailWord_511869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511870 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_511870 : Nat := 118140960795 + 511870 * 2 ^ 59
def prefixEnd_511870 : Nat := 4983230072969 + 3 ^ 40 * 511870 * 2
def baseEnd_511870 : Nat := 262835342617017539970959

theorem tailTrace_511870 : CollatzResearch.WordTrace tailWord_511870 prefixEnd_511870 262835342617017539970959 := by
  unfold tailWord_511870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333679081948735660151633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12446288437059923520808709 2333679081948735660151633)
  ·
    refine ⟨1750259311461551745113725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2333679081948735660151633 1750259311461551745113725)
    ·
      refine ⟨656347241798081904417647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1750259311461551745113725 656347241798081904417647)
      ·
        refine ⟨984520862697122856626471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656347241798081904417647 984520862697122856626471)
        ·
          refine ⟨1476781294045684284939707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984520862697122856626471 1476781294045684284939707)
          ·
            refine ⟨2215171941068526427409561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476781294045684284939707 2215171941068526427409561)
            ·
              refine ⟨1661378955801394820557171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215171941068526427409561 1661378955801394820557171)
              ·
                refine ⟨2492068433702092230835757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661378955801394820557171 2492068433702092230835757)
                ·
                  refine ⟨934525662638284586563409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2492068433702092230835757 934525662638284586563409)
                  ·
                    refine ⟨700894246978713439922557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934525662638284586563409 700894246978713439922557)
                    ·
                      refine ⟨262835342617017539970959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 700894246978713439922557 262835342617017539970959)
                      ·
                        rfl

theorem cell23_511870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_511870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511870 prefixEnd_511870 := by exact prefixLift 511870
  have htrace : WordTrace (prefixWord ++ tailWord_511870) baseStart_511870 baseEnd_511870 := by
    simpa [prefixWord, tailWord_511870, baseEnd_511870] using wordTrace_append hprefix tailTrace_511870
  have hstable : (prefixWord ++ tailWord_511870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511870).length < 2 ^ (prefixWord ++ tailWord_511870).sum := by decide
  have hdescent : baseEnd_511870 < baseStart_511870 := by decide
  rcases family_descends (prefixWord ++ tailWord_511870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511900 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_511900 : Nat := 118140960795 + 511900 * 2 ^ 59
def prefixEnd_511900 : Nat := 4983230072969 + 3 ^ 40 * 511900 * 2
def baseEnd_511900 : Nat := 262850747036652422595821

theorem tailTrace_511900 : CollatzResearch.WordTrace tailWord_511900 prefixEnd_511900 262850747036652422595821 := by
  unfold tailWord_511900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335263422740600202402577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12447017896987466936536769 9335263422740600202402577)
  ·
    refine ⟨7001447567055450151801933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9335263422740600202402577 7001447567055450151801933)
    ·
      refine ⟨2625542837645793806925725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7001447567055450151801933 2625542837645793806925725)
      ·
        refine ⟨984578564117172677597147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2625542837645793806925725 984578564117172677597147)
        ·
          refine ⟨1476867846175759016395721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984578564117172677597147 1476867846175759016395721)
          ·
            refine ⟨1107650884631819262296791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476867846175759016395721 1107650884631819262296791)
            ·
              refine ⟨1661476326947728893445187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107650884631819262296791 1661476326947728893445187)
              ·
                refine ⟨2492214490421593340167781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661476326947728893445187 2492214490421593340167781)
                ·
                  refine ⟨467290216954048751281459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2492214490421593340167781 467290216954048751281459)
                  ·
                    refine ⟨700935325431073126922189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467290216954048751281459 700935325431073126922189)
                    ·
                      refine ⟨262850747036652422595821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 700935325431073126922189 262850747036652422595821)
                      ·
                        rfl

theorem cell23_511900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_511900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511900 prefixEnd_511900 := by exact prefixLift 511900
  have htrace : WordTrace (prefixWord ++ tailWord_511900) baseStart_511900 baseEnd_511900 := by
    simpa [prefixWord, tailWord_511900, baseEnd_511900] using wordTrace_append hprefix tailTrace_511900
  have hstable : (prefixWord ++ tailWord_511900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511900).length < 2 ^ (prefixWord ++ tailWord_511900).sum := by decide
  have hdescent : baseEnd_511900 < baseStart_511900 := by decide
  rcases family_descends (prefixWord ++ tailWord_511900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511939 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7]
def baseStart_511939 : Nat := 118140960795 + 511939 * 2 ^ 59
def prefixEnd_511939 : Nat := 4983230072969 + 3 ^ 40 * 511939 * 2
def baseEnd_511939 : Nat := 262870772782177770008141

theorem tailTrace_511939 : CollatzResearch.WordTrace tailWord_511939 prefixEnd_511939 262870772782177770008141 := by
  unfold tailWord_511939
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671949292339910065474871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12447966194893273376983247 18671949292339910065474871)
  ·
    refine ⟨28007923938509865098212307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18671949292339910065474871 28007923938509865098212307)
    ·
      refine ⟨42011885907764797647318461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28007923938509865098212307 42011885907764797647318461)
      ·
        refine ⟨15754457215411799117744423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42011885907764797647318461 15754457215411799117744423)
        ·
          refine ⟨23631685823117698676616635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15754457215411799117744423 23631685823117698676616635)
          ·
            refine ⟨35447528734676548014924953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23631685823117698676616635 35447528734676548014924953)
            ·
              refine ⟨26585646551007411011193715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35447528734676548014924953 26585646551007411011193715)
              ·
                refine ⟨39878469826511116516790573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26585646551007411011193715 39878469826511116516790573)
                ·
                  refine ⟨14954426184941668693796465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39878469826511116516790573 14954426184941668693796465)
                  ·
                    refine ⟨11215819638706251520347349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14954426184941668693796465 11215819638706251520347349)
                    ·
                      refine ⟨262870772782177770008141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11215819638706251520347349 262870772782177770008141)
                      ·
                        rfl

theorem cell23_511939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_511939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511939 prefixEnd_511939 := by exact prefixLift 511939
  have htrace : WordTrace (prefixWord ++ tailWord_511939) baseStart_511939 baseEnd_511939 := by
    simpa [prefixWord, tailWord_511939, baseEnd_511939] using wordTrace_append hprefix tailTrace_511939
  have hstable : (prefixWord ++ tailWord_511939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511939).length < 2 ^ (prefixWord ++ tailWord_511939).sum := by decide
  have hdescent : baseEnd_511939 < baseStart_511939 := by decide
  rcases family_descends (prefixWord ++ tailWord_511939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511956 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_511956 : Nat := 118140960795 + 511956 * 2 ^ 59
def prefixEnd_511956 : Nat := 4983230072969 + 3 ^ 40 * 511956 * 2
def baseEnd_511956 : Nat := 262879501953304203495563

theorem tailTrace_511956 : CollatzResearch.WordTrace tailWord_511956 prefixEnd_511956 262879501953304203495563 := by
  unfold tailWord_511956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336284666639160984421861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12448379555518881312562481 9336284666639160984421861)
  ·
    refine ⟨1750553374994842684579099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9336284666639160984421861 1750553374994842684579099)
    ·
      refine ⟨2625830062492264026868649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750553374994842684579099 2625830062492264026868649)
      ·
        refine ⟨1969372546869198020151487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2625830062492264026868649 1969372546869198020151487)
        ·
          refine ⟨2954058820303797030227231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969372546869198020151487 2954058820303797030227231)
          ·
            refine ⟨4431088230455695545340847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954058820303797030227231 4431088230455695545340847)
            ·
              refine ⟨6646632345683543318011271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431088230455695545340847 6646632345683543318011271)
              ·
                refine ⟨9969948518525314977016907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6646632345683543318011271 9969948518525314977016907)
                ·
                  refine ⟨14954922777787972465525361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9969948518525314977016907 14954922777787972465525361)
                  ·
                    refine ⟨11216192083340979349144021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14954922777787972465525361 11216192083340979349144021)
                    ·
                      refine ⟨262879501953304203495563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11216192083340979349144021 262879501953304203495563)
                      ·
                        rfl

theorem cell23_511956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_511956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511956 prefixEnd_511956 := by exact prefixLift 511956
  have htrace : WordTrace (prefixWord ++ tailWord_511956) baseStart_511956 baseEnd_511956 := by
    simpa [prefixWord, tailWord_511956, baseEnd_511956] using wordTrace_append hprefix tailTrace_511956
  have hstable : (prefixWord ++ tailWord_511956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511956).length < 2 ^ (prefixWord ++ tailWord_511956).sum := by decide
  have hdescent : baseEnd_511956 < baseStart_511956 := by decide
  rcases family_descends (prefixWord ++ tailWord_511956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511976 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 6, 5]
def baseStart_511976 : Nat := 118140960795 + 511976 * 2 ^ 59
def prefixEnd_511976 : Nat := 4983230072969 + 3 ^ 40 * 511976 * 2
def baseEnd_511976 : Nat := 87629923855464708415157

theorem tailTrace_511976 : CollatzResearch.WordTrace tailWord_511976 prefixEnd_511976 87629923855464708415157 := by
  unfold tailWord_511976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336649396602932692285891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12448865862137243589714521 9336649396602932692285891)
  ·
    refine ⟨14004974094904399038428837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9336649396602932692285891 14004974094904399038428837)
    ·
      refine ⟨2625932642794574819705407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14004974094904399038428837 2625932642794574819705407)
      ·
        refine ⟨3938898964191862229558111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625932642794574819705407 3938898964191862229558111)
        ·
          refine ⟨5908348446287793344337167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938898964191862229558111 5908348446287793344337167)
          ·
            refine ⟨8862522669431690016505751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908348446287793344337167 8862522669431690016505751)
            ·
              refine ⟨13293784004147535024758627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862522669431690016505751 13293784004147535024758627)
              ·
                refine ⟨19940676006221302537137941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13293784004147535024758627 19940676006221302537137941)
                ·
                  refine ⟨934719187791623556428341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19940676006221302537137941 934719187791623556428341)
                  ·
                    refine ⟨87629923855464708415157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 934719187791623556428341 87629923855464708415157)
                    ·
                      rfl

theorem cell23_511976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_511976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511976 prefixEnd_511976 := by exact prefixLift 511976
  have htrace : WordTrace (prefixWord ++ tailWord_511976) baseStart_511976 baseEnd_511976 := by
    simpa [prefixWord, tailWord_511976, baseEnd_511976] using wordTrace_append hprefix tailTrace_511976
  have hstable : (prefixWord ++ tailWord_511976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511976).length < 2 ^ (prefixWord ++ tailWord_511976).sum := by decide
  have hdescent : baseEnd_511976 < baseStart_511976 := by decide
  rcases family_descends (prefixWord ++ tailWord_511976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511993 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 2, 5]
def baseStart_511993 : Nat := 118140960795 + 511993 * 2 ^ 59
def prefixEnd_511993 : Nat := 4983230072969 + 3 ^ 40 * 511993 * 2
def baseEnd_511993 : Nat := 87632833579173519577631

theorem tailTrace_511993 : CollatzResearch.WordTrace tailWord_511993 prefixEnd_511993 87632833579173519577631 := by
  unfold tailWord_511993
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673918834144277287940633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12449279222762851525293755 18673918834144277287940633)
  ·
    refine ⟨14005439125608207965955475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18673918834144277287940633 14005439125608207965955475)
    ·
      refine ⟨21008158688412311948933213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14005439125608207965955475 21008158688412311948933213)
      ·
        refine ⟨7878059508154616980849955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21008158688412311948933213 7878059508154616980849955)
        ·
          refine ⟨11817089262231925471274933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7878059508154616980849955 11817089262231925471274933)
          ·
            refine ⟨1107852118334243012932025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11817089262231925471274933 1107852118334243012932025)
            ·
              refine ⟨830889088750682259699019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107852118334243012932025 830889088750682259699019)
              ·
                refine ⟨1246333633126023389548529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830889088750682259699019 1246333633126023389548529)
                ·
                  refine ⟨934750224844517542161397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1246333633126023389548529 934750224844517542161397)
                  ·
                    refine ⟨87632833579173519577631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 934750224844517542161397 87632833579173519577631)
                    ·
                      rfl

theorem cell23_511993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_511993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511993 prefixEnd_511993 := by exact prefixLift 511993
  have htrace : WordTrace (prefixWord ++ tailWord_511993) baseStart_511993 baseEnd_511993 := by
    simpa [prefixWord, tailWord_511993, baseEnd_511993] using wordTrace_append hprefix tailTrace_511993
  have hstable : (prefixWord ++ tailWord_511993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511993).length < 2 ^ (prefixWord ++ tailWord_511993).sum := by decide
  have hdescent : baseEnd_511993 < baseStart_511993 := by decide
  rcases family_descends (prefixWord ++ tailWord_511993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512050 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_512050 : Nat := 118140960795 + 512050 * 2 ^ 59
def prefixEnd_512050 : Nat := 4983230072969 + 3 ^ 40 * 512050 * 2
def baseEnd_512050 : Nat := 262927769134826835720131

theorem tailTrace_512050 : CollatzResearch.WordTrace tailWord_512050 prefixEnd_512050 262927769134826835720131 := by
  unfold tailWord_512050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668999448734444005691401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12450665196625184015177069 4668999448734444005691401)
  ·
    refine ⟨3501749586550833004268551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4668999448734444005691401 3501749586550833004268551)
    ·
      refine ⟨5252624379826249506402827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501749586550833004268551 5252624379826249506402827)
      ·
        refine ⟨7878936569739374259604241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5252624379826249506402827 7878936569739374259604241)
        ·
          refine ⟨5909202427304530694703181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7878936569739374259604241 5909202427304530694703181)
          ·
            refine ⟨2215950910239199010513693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5909202427304530694703181 2215950910239199010513693)
            ·
              refine ⟨830981591339699628942635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2215950910239199010513693 830981591339699628942635)
              ·
                refine ⟨1246472387009549443413953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830981591339699628942635 1246472387009549443413953)
                ·
                  refine ⟨934854290257162082560465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1246472387009549443413953 934854290257162082560465)
                  ·
                    refine ⟨701140717692871561920349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934854290257162082560465 701140717692871561920349)
                    ·
                      refine ⟨262927769134826835720131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701140717692871561920349 262927769134826835720131)
                      ·
                        rfl

theorem cell23_512050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_512050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512050 prefixEnd_512050 := by exact prefixLift 512050
  have htrace : WordTrace (prefixWord ++ tailWord_512050) baseStart_512050 baseEnd_512050 := by
    simpa [prefixWord, tailWord_512050, baseEnd_512050] using wordTrace_append hprefix tailTrace_512050
  have hstable : (prefixWord ++ tailWord_512050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512050).length < 2 ^ (prefixWord ++ tailWord_512050).sum := by decide
  have hdescent : baseEnd_512050 < baseStart_512050 := by decide
  rcases family_descends (prefixWord ++ tailWord_512050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512070 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_512070 : Nat := 118140960795 + 512070 * 2 ^ 59
def prefixEnd_512070 : Nat := 4983230072969 + 3 ^ 40 * 512070 * 2
def baseEnd_512070 : Nat := 29215337638657417496671

theorem tailTrace_512070 : CollatzResearch.WordTrace tailWord_512070 prefixEnd_512070 29215337638657417496671 := by
  unfold tailWord_512070
  simp only [CollatzResearch.WordTrace]
  refine ⟨583647726714541232452927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12451151503243546292329109 583647726714541232452927)
  ·
    refine ⟨875471590071811848679391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583647726714541232452927 875471590071811848679391)
    ·
      refine ⟨1313207385107717773019087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875471590071811848679391 1313207385107717773019087)
      ·
        refine ⟨1969811077661576659528631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313207385107717773019087 1969811077661576659528631)
        ·
          refine ⟨2954716616492364989292947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969811077661576659528631 2954716616492364989292947)
          ·
            refine ⟨4432074924738547483939421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954716616492364989292947 4432074924738547483939421)
            ·
              refine ⟨1662028096776955306477283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4432074924738547483939421 1662028096776955306477283)
              ·
                refine ⟨2493042145165432959715925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662028096776955306477283 2493042145165432959715925)
                ·
                  refine ⟨29215337638657417496671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2493042145165432959715925 29215337638657417496671)
                  ·
                    rfl

theorem cell23_512070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_512070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512070 prefixEnd_512070 := by exact prefixLift 512070
  have htrace : WordTrace (prefixWord ++ tailWord_512070) baseStart_512070 baseEnd_512070 := by
    simpa [prefixWord, tailWord_512070, baseEnd_512070] using wordTrace_append hprefix tailTrace_512070
  have hstable : (prefixWord ++ tailWord_512070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512070).length < 2 ^ (prefixWord ++ tailWord_512070).sum := by decide
  have hdescent : baseEnd_512070 < baseStart_512070 := by decide
  rcases family_descends (prefixWord ++ tailWord_512070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512113 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 6, 4]
def baseStart_512113 : Nat := 118140960795 + 512113 * 2 ^ 59
def prefixEnd_512113 : Nat := 4983230072969 + 3 ^ 40 * 512113 * 2
def baseEnd_512113 : Nat := 87653372805353363077447

theorem tailTrace_512113 : CollatzResearch.WordTrace tailWord_512113 prefixEnd_512113 87653372805353363077447 := by
  unfold tailWord_512113
  simp only [CollatzResearch.WordTrace]
  refine ⟨18678295593709537782308993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12452197062473025188205995 18678295593709537782308993)
  ·
    refine ⟨14008721695282153336731745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18678295593709537782308993 14008721695282153336731745)
    ·
      refine ⟨10506541271461615002548809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14008721695282153336731745 10506541271461615002548809)
      ·
        refine ⟨7879905953596211251911607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10506541271461615002548809 7879905953596211251911607)
        ·
          refine ⟨11819858930394316877867411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7879905953596211251911607 11819858930394316877867411)
          ·
            refine ⟨17729788395591475316801117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11819858930394316877867411 17729788395591475316801117)
            ·
              refine ⟨6648670648346803243800419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17729788395591475316801117 6648670648346803243800419)
              ·
                refine ⟨9973005972520204865700629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648670648346803243800419 9973005972520204865700629)
                ·
                  refine ⟨467484654961884603079717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9973005972520204865700629 467484654961884603079717)
                  ·
                    refine ⟨87653372805353363077447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 467484654961884603079717 87653372805353363077447)
                    ·
                      rfl

theorem cell23_512113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_512113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512113 prefixEnd_512113 := by exact prefixLift 512113
  have htrace : WordTrace (prefixWord ++ tailWord_512113) baseStart_512113 baseEnd_512113 := by
    simpa [prefixWord, tailWord_512113, baseEnd_512113] using wordTrace_append hprefix tailTrace_512113
  have hstable : (prefixWord ++ tailWord_512113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512113).length < 2 ^ (prefixWord ++ tailWord_512113).sum := by decide
  have hdescent : baseEnd_512113 < baseStart_512113 := by decide
  rcases family_descends (prefixWord ++ tailWord_512113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512114 : List Nat := [3, 2, 1, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_512114 : Nat := 118140960795 + 512114 * 2 ^ 59
def prefixEnd_512114 : Nat := 4983230072969 + 3 ^ 40 * 512114 * 2
def baseEnd_512114 : Nat := 262960631896714585319837

theorem tailTrace_512114 : CollatzResearch.WordTrace tailWord_512114 prefixEnd_512114 262960631896714585319837 := by
  unfold tailWord_512114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669583016676478738273849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12452221377803943302063597 4669583016676478738273849)
  ·
    refine ⟨3502187262507359053705387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4669583016676478738273849 3502187262507359053705387)
    ·
      refine ⟨5253280893761038580558081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502187262507359053705387 5253280893761038580558081)
      ·
        refine ⟨3939960670320778935418561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5253280893761038580558081 3939960670320778935418561)
        ·
          refine ⟨2954970502740584201563921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3939960670320778935418561 2954970502740584201563921)
          ·
            refine ⟨2216227877055438151172941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954970502740584201563921 2216227877055438151172941)
            ·
              refine ⟨831085453895789306689853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2216227877055438151172941 831085453895789306689853)
              ·
                refine ⟨311657045210920990008695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831085453895789306689853 311657045210920990008695)
                ·
                  refine ⟨467485567816381485013043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311657045210920990008695 467485567816381485013043)
                  ·
                    refine ⟨701228351724572227519565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467485567816381485013043 701228351724572227519565)
                    ·
                      refine ⟨262960631896714585319837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701228351724572227519565 262960631896714585319837)
                      ·
                        rfl

theorem cell23_512114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_512114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512114 prefixEnd_512114 := by exact prefixLift 512114
  have htrace : WordTrace (prefixWord ++ tailWord_512114) baseStart_512114 baseEnd_512114 := by
    simpa [prefixWord, tailWord_512114, baseEnd_512114] using wordTrace_append hprefix tailTrace_512114
  have hstable : (prefixWord ++ tailWord_512114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512114).length < 2 ^ (prefixWord ++ tailWord_512114).sum := by decide
  have hdescent : baseEnd_512114 < baseStart_512114 := by decide
  rcases family_descends (prefixWord ++ tailWord_512114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512123 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 3]
def baseStart_512123 : Nat := 118140960795 + 512123 * 2 ^ 59
def prefixEnd_512123 : Nat := 4983230072969 + 3 ^ 40 * 512123 * 2
def baseEnd_512123 : Nat := 262965253222605050107295

theorem tailTrace_512123 : CollatzResearch.WordTrace tailWord_512123 prefixEnd_512123 262965253222605050107295 := by
  unfold tailWord_512123
  simp only [CollatzResearch.WordTrace]
  refine ⟨18678660323673309490173023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12452440215782206326782015 18678660323673309490173023)
  ·
    refine ⟨28017990485509964235259535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18678660323673309490173023 28017990485509964235259535)
    ·
      refine ⟨42026985728264946352889303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28017990485509964235259535 42026985728264946352889303)
      ·
        refine ⟨63040478592397419529333955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42026985728264946352889303 63040478592397419529333955)
        ·
          refine ⟨94560717888596129294000933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63040478592397419529333955 94560717888596129294000933)
          ·
            refine ⟨17730134604111774242625175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94560717888596129294000933 17730134604111774242625175)
            ·
              refine ⟨26595201906167661363937763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17730134604111774242625175 26595201906167661363937763)
              ·
                refine ⟨39892802859251492045906645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26595201906167661363937763 39892802859251492045906645)
                ·
                  refine ⟨934987567013706844825937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 39892802859251492045906645 934987567013706844825937)
                  ·
                    refine ⟨701240675260280133619453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934987567013706844825937 701240675260280133619453)
                    ·
                      refine ⟨262965253222605050107295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701240675260280133619453 262965253222605050107295)
                      ·
                        rfl

theorem cell23_512123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 3].length) (baseStart_512123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512123 prefixEnd_512123 := by exact prefixLift 512123
  have htrace : WordTrace (prefixWord ++ tailWord_512123) baseStart_512123 baseEnd_512123 := by
    simpa [prefixWord, tailWord_512123, baseEnd_512123] using wordTrace_append hprefix tailTrace_512123
  have hstable : (prefixWord ++ tailWord_512123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512123).length < 2 ^ (prefixWord ++ tailWord_512123).sum := by decide
  have hdescent : baseEnd_512123 < baseStart_512123 := by decide
  rcases family_descends (prefixWord ++ tailWord_512123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512133 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_512133 : Nat := 118140960795 + 512133 * 2 ^ 59
def prefixEnd_512133 : Nat := 4983230072969 + 3 ^ 40 * 512133 * 2
def baseEnd_512133 : Nat := 262970388029150010982249

theorem tailTrace_512133 : CollatzResearch.WordTrace tailWord_512133 prefixEnd_512133 262970388029150010982249 := by
  unfold tailWord_512133
  simp only [CollatzResearch.WordTrace]
  refine ⟨18679025053637081198037053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12452683369091387465358035 18679025053637081198037053)
  ·
    refine ⟨7004634395113905449263895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18679025053637081198037053 7004634395113905449263895)
    ·
      refine ⟨10506951592670858173895843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7004634395113905449263895 10506951592670858173895843)
      ·
        refine ⟨15760427389006287260843765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10506951592670858173895843 15760427389006287260843765)
        ·
          refine ⟨1477540067719339430704103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15760427389006287260843765 1477540067719339430704103)
          ·
            refine ⟨2216310101579009146056155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477540067719339430704103 2216310101579009146056155)
            ·
              refine ⟨3324465152368513719084233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216310101579009146056155 3324465152368513719084233)
              ·
                refine ⟨2493348864276385289313175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324465152368513719084233 2493348864276385289313175)
                ·
                  refine ⟨3740023296414577933969763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493348864276385289313175 3740023296414577933969763)
                  ·
                    refine ⟨5610034944621866900954645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3740023296414577933969763 5610034944621866900954645)
                    ·
                      refine ⟨262970388029150010982249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5610034944621866900954645 262970388029150010982249)
                      ·
                        rfl

theorem cell23_512133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_512133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512133 prefixEnd_512133 := by exact prefixLift 512133
  have htrace : WordTrace (prefixWord ++ tailWord_512133) baseStart_512133 baseEnd_512133 := by
    simpa [prefixWord, tailWord_512133, baseEnd_512133] using wordTrace_append hprefix tailTrace_512133
  have hstable : (prefixWord ++ tailWord_512133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512133).length < 2 ^ (prefixWord ++ tailWord_512133).sum := by decide
  have hdescent : baseEnd_512133 < baseStart_512133 := by decide
  rcases family_descends (prefixWord ++ tailWord_512133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512153 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 3]
def baseStart_512153 : Nat := 118140960795 + 512153 * 2 ^ 59
def prefixEnd_512153 : Nat := 4983230072969 + 3 ^ 40 * 512153 * 2
def baseEnd_512153 : Nat := 262980657642239932732157

theorem tailTrace_512153 : CollatzResearch.WordTrace tailWord_512153 prefixEnd_512153 262980657642239932732157 := by
  unfold tailWord_512153
  simp only [CollatzResearch.WordTrace]
  refine ⟨18679754513564624613765113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12453169675709749742510075 18679754513564624613765113)
  ·
    refine ⟨14009815885173468460323835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18679754513564624613765113 14009815885173468460323835)
    ·
      refine ⟨21014723827760202690485753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14009815885173468460323835 21014723827760202690485753)
      ·
        refine ⟨15761042870820152017864315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21014723827760202690485753 15761042870820152017864315)
        ·
          refine ⟨23641564306230228026796473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15761042870820152017864315 23641564306230228026796473)
          ·
            refine ⟨17731173229672671020097355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23641564306230228026796473 17731173229672671020097355)
            ·
              refine ⟨26596759844509006530146033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17731173229672671020097355 26596759844509006530146033)
              ·
                refine ⟨19947569883381754897609525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26596759844509006530146033 19947569883381754897609525)
                ·
                  refine ⟨1870084676567039521650893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19947569883381754897609525 1870084676567039521650893)
                  ·
                    refine ⟨701281753712639820619085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870084676567039521650893 701281753712639820619085)
                    ·
                      refine ⟨262980657642239932732157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701281753712639820619085 262980657642239932732157)
                      ·
                        rfl

theorem cell23_512153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_512153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512153 prefixEnd_512153 := by exact prefixLift 512153
  have htrace : WordTrace (prefixWord ++ tailWord_512153) baseStart_512153 baseEnd_512153 := by
    simpa [prefixWord, tailWord_512153, baseEnd_512153] using wordTrace_append hprefix tailTrace_512153
  have hstable : (prefixWord ++ tailWord_512153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512153).length < 2 ^ (prefixWord ++ tailWord_512153).sum := by decide
  have hdescent : baseEnd_512153 < baseStart_512153 := by decide
  rcases family_descends (prefixWord ++ tailWord_512153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512154 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_512154 : Nat := 118140960795 + 512154 * 2 ^ 59
def prefixEnd_512154 : Nat := 4983230072969 + 3 ^ 40 * 512154 * 2
def baseEnd_512154 : Nat := 262981171122894428819653

theorem tailTrace_512154 : CollatzResearch.WordTrace tailWord_512154 prefixEnd_512154 262981171122894428819653 := by
  unfold tailWord_512154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669947746640250446137879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12453193991040667856367677 4669947746640250446137879)
  ·
    refine ⟨7004921619960375669206819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4669947746640250446137879 7004921619960375669206819)
    ·
      refine ⟨10507382429940563503810229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7004921619960375669206819 10507382429940563503810229)
      ·
        refine ⟨985067102806927828482209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10507382429940563503810229 985067102806927828482209)
        ·
          refine ⟨738800327105195871361657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985067102806927828482209 738800327105195871361657)
          ·
            refine ⟨554100245328896903521243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738800327105195871361657 554100245328896903521243)
            ·
              refine ⟨831150367993345355281865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554100245328896903521243 831150367993345355281865)
              ·
                refine ⟨623362775995009016461399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831150367993345355281865 623362775995009016461399)
                ·
                  refine ⟨935044163992513524692099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623362775995009016461399 935044163992513524692099)
                  ·
                    refine ⟨1402566245988770287038149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 935044163992513524692099 1402566245988770287038149)
                    ·
                      refine ⟨262981171122894428819653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1402566245988770287038149 262981171122894428819653)
                      ·
                        rfl

theorem cell23_512154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_512154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512154 prefixEnd_512154 := by exact prefixLift 512154
  have htrace : WordTrace (prefixWord ++ tailWord_512154) baseStart_512154 baseEnd_512154 := by
    simpa [prefixWord, tailWord_512154, baseEnd_512154] using wordTrace_append hprefix tailTrace_512154
  have hstable : (prefixWord ++ tailWord_512154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512154).length < 2 ^ (prefixWord ++ tailWord_512154).sum := by decide
  have hdescent : baseEnd_512154 < baseStart_512154 := by decide
  rcases family_descends (prefixWord ++ tailWord_512154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512157 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_512157 : Nat := 118140960795 + 512157 * 2 ^ 59
def prefixEnd_512157 : Nat := 4983230072969 + 3 ^ 40 * 512157 * 2
def baseEnd_512157 : Nat := 262982711564857917082139

theorem tailTrace_512157 : CollatzResearch.WordTrace tailWord_512157 prefixEnd_512157 262982711564857917082139 := by
  unfold tailWord_512157
  simp only [CollatzResearch.WordTrace]
  refine ⟨18679900405550133296910725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12453266937033422197940483 18679900405550133296910725)
  ·
    refine ⟨3502481326040649993170761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18679900405550133296910725 3502481326040649993170761)
    ·
      refine ⟨2626860994530487494878071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3502481326040649993170761 2626860994530487494878071)
      ·
        refine ⟨3940291491795731242317107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626860994530487494878071 3940291491795731242317107)
        ·
          refine ⟨5910437237693596863475661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940291491795731242317107 5910437237693596863475661)
          ·
            refine ⟨2216413964135098823803373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5910437237693596863475661 2216413964135098823803373)
            ·
              refine ⟨831155236550662058926265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2216413964135098823803373 831155236550662058926265)
              ·
                refine ⟨623366427412996544194699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831155236550662058926265 623366427412996544194699)
                ·
                  refine ⟨935049641119494816292049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623366427412996544194699 935049641119494816292049)
                  ·
                    refine ⟨701287230839621112219037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 935049641119494816292049 701287230839621112219037)
                    ·
                      refine ⟨262982711564857917082139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701287230839621112219037 262982711564857917082139)
                      ·
                        rfl

theorem cell23_512157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_512157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512157 prefixEnd_512157 := by exact prefixLift 512157
  have htrace : WordTrace (prefixWord ++ tailWord_512157) baseStart_512157 baseEnd_512157 := by
    simpa [prefixWord, tailWord_512157, baseEnd_512157] using wordTrace_append hprefix tailTrace_512157
  have hstable : (prefixWord ++ tailWord_512157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512157).length < 2 ^ (prefixWord ++ tailWord_512157).sum := by decide
  have hdescent : baseEnd_512157 < baseStart_512157 := by decide
  rcases family_descends (prefixWord ++ tailWord_512157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512167 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_512167 : Nat := 118140960795 + 512167 * 2 ^ 59
def prefixEnd_512167 : Nat := 4983230072969 + 3 ^ 40 * 512167 * 2
def baseEnd_512167 : Nat := 262987846371402877957093

theorem tailTrace_512167 : CollatzResearch.WordTrace tailWord_512167 prefixEnd_512167 262987846371402877957093 := by
  unfold tailWord_512167
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680265135513905004774755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12453510090342603336516503 18680265135513905004774755)
  ·
    refine ⟨28020397703270857507162133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680265135513905004774755 28020397703270857507162133)
    ·
      refine ⟨1313456142340821445648225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28020397703270857507162133 1313456142340821445648225)
      ·
        refine ⟨985092106755616084236169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313456142340821445648225 985092106755616084236169)
        ·
          refine ⟨738819080066712063177127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985092106755616084236169 738819080066712063177127)
          ·
            refine ⟨1108228620100068094765691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738819080066712063177127 1108228620100068094765691)
            ·
              refine ⟨1662342930150102142148537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108228620100068094765691 1662342930150102142148537)
              ·
                refine ⟨1246757197612576606611403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662342930150102142148537 1246757197612576606611403)
                ·
                  refine ⟨1870135796418864909917105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246757197612576606611403 1870135796418864909917105)
                  ·
                    refine ⟨1402601847314148682437829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1870135796418864909917105 1402601847314148682437829)
                    ·
                      refine ⟨262987846371402877957093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1402601847314148682437829 262987846371402877957093)
                      ·
                        rfl

theorem cell23_512167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_512167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512167 prefixEnd_512167 := by exact prefixLift 512167
  have htrace : WordTrace (prefixWord ++ tailWord_512167) baseStart_512167 baseEnd_512167 := by
    simpa [prefixWord, tailWord_512167, baseEnd_512167] using wordTrace_append hprefix tailTrace_512167
  have hstable : (prefixWord ++ tailWord_512167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512167).length < 2 ^ (prefixWord ++ tailWord_512167).sum := by decide
  have hdescent : baseEnd_512167 < baseStart_512167 := by decide
  rcases family_descends (prefixWord ++ tailWord_512167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512187 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 3]
def baseStart_512187 : Nat := 118140960795 + 512187 * 2 ^ 59
def prefixEnd_512187 : Nat := 4983230072969 + 3 ^ 40 * 512187 * 2
def baseEnd_512187 : Nat := 262998115984492799707001

theorem tailTrace_512187 : CollatzResearch.WordTrace tailWord_512187 prefixEnd_512187 262998115984492799707001 := by
  unfold tailWord_512187
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680994595441448420502815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12453996396960965613668543 18680994595441448420502815)
  ·
    refine ⟨28021491893162172630754223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680994595441448420502815 28021491893162172630754223)
    ·
      refine ⟨42032237839743258946131335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28021491893162172630754223 42032237839743258946131335)
      ·
        refine ⟨63048356759614888419197003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42032237839743258946131335 63048356759614888419197003)
        ·
          refine ⟨94572535139422332628795505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63048356759614888419197003 94572535139422332628795505)
          ·
            refine ⟨70929401354566749471596629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94572535139422332628795505 70929401354566749471596629)
            ·
              refine ⟨831203922123829095370273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 70929401354566749471596629 831203922123829095370273)
              ·
                refine ⟨623402941592871821527705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831203922123829095370273 623402941592871821527705)
                ·
                  refine ⟨467552206194653866145779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623402941592871821527705 467552206194653866145779)
                  ·
                    refine ⟨701328309291980799218669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467552206194653866145779 701328309291980799218669)
                    ·
                      refine ⟨262998115984492799707001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701328309291980799218669 262998115984492799707001)
                      ·
                        rfl

theorem cell23_512187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 3].length) (baseStart_512187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512187 prefixEnd_512187 := by exact prefixLift 512187
  have htrace : WordTrace (prefixWord ++ tailWord_512187) baseStart_512187 baseEnd_512187 := by
    simpa [prefixWord, tailWord_512187, baseEnd_512187] using wordTrace_append hprefix tailTrace_512187
  have hstable : (prefixWord ++ tailWord_512187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512187).length < 2 ^ (prefixWord ++ tailWord_512187).sum := by decide
  have hdescent : baseEnd_512187 < baseStart_512187 := by decide
  rcases family_descends (prefixWord ++ tailWord_512187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512194 : List Nat := [3, 5, 1, 1, 1, 3, 1, 8]
def baseStart_512194 : Nat := 118140960795 + 512194 * 2 ^ 59
def prefixEnd_512194 : Nat := 4983230072969 + 3 ^ 40 * 512194 * 2
def baseEnd_512194 : Nat := 9740804087002750826647

theorem tailTrace_512194 : CollatzResearch.WordTrace tailWord_512194 prefixEnd_512194 9740804087002750826647 := by
  unfold tailWord_512194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4670312476604022154001909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12454166604277392410671757 4670312476604022154001909)
  ·
    refine ⟨437841794681627076937679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4670312476604022154001909 437841794681627076937679)
    ·
      refine ⟨656762692022440615406519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437841794681627076937679 656762692022440615406519)
      ·
        refine ⟨985144038033660923109779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656762692022440615406519 985144038033660923109779)
        ·
          refine ⟨1477716057050491384664669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985144038033660923109779 1477716057050491384664669)
          ·
            refine ⟨554143521393934269249251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1477716057050491384664669 554143521393934269249251)
            ·
              refine ⟨831215282090901403873877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554143521393934269249251 831215282090901403873877)
              ·
                refine ⟨9740804087002750826647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 831215282090901403873877 9740804087002750826647)
                ·
                  rfl

theorem cell23_512194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 8].length) (baseStart_512194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512194 prefixEnd_512194 := by exact prefixLift 512194
  have htrace : WordTrace (prefixWord ++ tailWord_512194) baseStart_512194 baseEnd_512194 := by
    simpa [prefixWord, tailWord_512194, baseEnd_512194] using wordTrace_append hprefix tailTrace_512194
  have hstable : (prefixWord ++ tailWord_512194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512194).length < 2 ^ (prefixWord ++ tailWord_512194).sum := by decide
  have hdescent : baseEnd_512194 < baseStart_512194 := by decide
  rcases family_descends (prefixWord ++ tailWord_512194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512203 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 2, 6]
def baseStart_512203 : Nat := 118140960795 + 512203 * 2 ^ 59
def prefixEnd_512203 : Nat := 4983230072969 + 3 ^ 40 * 512203 * 2
def baseEnd_512203 : Nat := 87668777224988245702309

theorem tailTrace_512203 : CollatzResearch.WordTrace tailWord_512203 prefixEnd_512203 87668777224988245702309 := by
  unfold tailWord_512203
  simp only [CollatzResearch.WordTrace]
  refine ⟨18681578163383483153085263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12454385442255655435390175 18681578163383483153085263)
  ·
    refine ⟨28022367245075224729627895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18681578163383483153085263 28022367245075224729627895)
    ·
      refine ⟨42033550867612837094441843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28022367245075224729627895 42033550867612837094441843)
      ·
        refine ⟨63050326301419255641662765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42033550867612837094441843 63050326301419255641662765)
        ·
          refine ⟨23643872363032220865623537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63050326301419255641662765 23643872363032220865623537)
          ·
            refine ⟨17732904272274165649217653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23643872363032220865623537 17732904272274165649217653)
            ·
              refine ⟨1662459775525703029614155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17732904272274165649217653 1662459775525703029614155)
              ·
                refine ⟨2493689663288554544421233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662459775525703029614155 2493689663288554544421233)
                ·
                  refine ⟨1870267247466415908315925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2493689663288554544421233 1870267247466415908315925)
                  ·
                    refine ⟨87668777224988245702309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1870267247466415908315925 87668777224988245702309)
                    ·
                      rfl

theorem cell23_512203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 6].length) (baseStart_512203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512203 prefixEnd_512203 := by exact prefixLift 512203
  have htrace : WordTrace (prefixWord ++ tailWord_512203) baseStart_512203 baseEnd_512203 := by
    simpa [prefixWord, tailWord_512203, baseEnd_512203] using wordTrace_append hprefix tailTrace_512203
  have hstable : (prefixWord ++ tailWord_512203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512203).length < 2 ^ (prefixWord ++ tailWord_512203).sum := by decide
  have hdescent : baseEnd_512203 < baseStart_512203 := by decide
  rcases family_descends (prefixWord ++ tailWord_512203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512204 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_512204 : Nat := 118140960795 + 512204 * 2 ^ 59
def prefixEnd_512204 : Nat := 4983230072969 + 3 ^ 40 * 512204 * 2
def baseEnd_512204 : Nat := 263006845155619233194423

theorem tailTrace_512204 : CollatzResearch.WordTrace tailWord_512204 prefixEnd_512204 263006845155619233194423 := by
  unfold tailWord_512204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340807318189930161935833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12454409757586573549247777 9340807318189930161935833)
  ·
    refine ⟨7005605488642447621451875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9340807318189930161935833 7005605488642447621451875)
    ·
      refine ⟨10508408232963671432177813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7005605488642447621451875 10508408232963671432177813)
      ·
        refine ⟨492581635920172098383335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10508408232963671432177813 492581635920172098383335)
        ·
          refine ⟨738872453880258147575003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492581635920172098383335 738872453880258147575003)
          ·
            refine ⟨1108308680820387221362505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738872453880258147575003 1108308680820387221362505)
            ·
              refine ⟨831231510615290416021879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108308680820387221362505 831231510615290416021879)
              ·
                refine ⟨1246847265922935624032819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831231510615290416021879 1246847265922935624032819)
                ·
                  refine ⟨1870270898884403436049229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246847265922935624032819 1870270898884403436049229)
                  ·
                    refine ⟨701351587081651288518461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870270898884403436049229 701351587081651288518461)
                    ·
                      refine ⟨263006845155619233194423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701351587081651288518461 263006845155619233194423)
                      ·
                        rfl

theorem cell23_512204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_512204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512204 prefixEnd_512204 := by exact prefixLift 512204
  have htrace : WordTrace (prefixWord ++ tailWord_512204) baseStart_512204 baseEnd_512204 := by
    simpa [prefixWord, tailWord_512204, baseEnd_512204] using wordTrace_append hprefix tailTrace_512204
  have hstable : (prefixWord ++ tailWord_512204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512204).length < 2 ^ (prefixWord ++ tailWord_512204).sum := by decide
  have hdescent : baseEnd_512204 < baseStart_512204 := by decide
  rcases family_descends (prefixWord ++ tailWord_512204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512223 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_512223 : Nat := 118140960795 + 512223 * 2 ^ 59
def prefixEnd_512223 : Nat := 4983230072969 + 3 ^ 40 * 512223 * 2
def baseEnd_512223 : Nat := 263016601288054658856835

theorem tailTrace_512223 : CollatzResearch.WordTrace tailWord_512223 prefixEnd_512223 263016601288054658856835 := by
  unfold tailWord_512223
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682307623311026568813323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12454871748874017712542215 18682307623311026568813323)
  ·
    refine ⟨28023461434966539853219985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18682307623311026568813323 28023461434966539853219985)
    ·
      refine ⟨21017596076224904889914989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28023461434966539853219985 21017596076224904889914989)
      ·
        refine ⟨7881598528584339333718121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21017596076224904889914989 7881598528584339333718121)
        ·
          refine ⟨5911198896438254500288591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7881598528584339333718121 5911198896438254500288591)
          ·
            refine ⟨8866798344657381750432887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911198896438254500288591 8866798344657381750432887)
            ·
              refine ⟨13300197516986072625649331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866798344657381750432887 13300197516986072625649331)
              ·
                refine ⟨19950296275479108938473997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300197516986072625649331 19950296275479108938473997)
                ·
                  refine ⟨7481361103304665851927749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19950296275479108938473997 7481361103304665851927749)
                  ·
                    refine ⟨1402755206869624847236453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7481361103304665851927749 1402755206869624847236453)
                    ·
                      refine ⟨263016601288054658856835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1402755206869624847236453 263016601288054658856835)
                      ·
                        rfl

theorem cell23_512223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_512223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512223 prefixEnd_512223 := by exact prefixLift 512223
  have htrace : WordTrace (prefixWord ++ tailWord_512223) baseStart_512223 baseEnd_512223 := by
    simpa [prefixWord, tailWord_512223, baseEnd_512223] using wordTrace_append hprefix tailTrace_512223
  have hstable : (prefixWord ++ tailWord_512223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512223).length < 2 ^ (prefixWord ++ tailWord_512223).sum := by decide
  have hdescent : baseEnd_512223 < baseStart_512223 := by decide
  rcases family_descends (prefixWord ++ tailWord_512223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512231 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_512231 : Nat := 118140960795 + 512231 * 2 ^ 59
def prefixEnd_512231 : Nat := 4983230072969 + 3 ^ 40 * 512231 * 2
def baseEnd_512231 : Nat := 263020709133290627556799

theorem tailTrace_512231 : CollatzResearch.WordTrace tailWord_512231 prefixEnd_512231 263020709133290627556799 := by
  unfold tailWord_512231
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682599407282043935104547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12455066271521362623403031 18682599407282043935104547)
  ·
    refine ⟨28023899110923065902656821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18682599407282043935104547 28023899110923065902656821)
    ·
      refine ⟨2627240541649037428374077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28023899110923065902656821 2627240541649037428374077)
      ·
        refine ⟨985215203118389035640279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2627240541649037428374077 985215203118389035640279)
        ·
          refine ⟨1477822804677583553460419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985215203118389035640279 1477822804677583553460419)
          ·
            refine ⟨2216734207016375330190629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477822804677583553460419 2216734207016375330190629)
            ·
              refine ⟨415637663815570374410743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2216734207016375330190629 415637663815570374410743)
              ·
                refine ⟨623456495723355561616115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415637663815570374410743 623456495723355561616115)
                ·
                  refine ⟨935184743585033342424173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623456495723355561616115 935184743585033342424173)
                  ·
                    refine ⟨350694278844387503409065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 935184743585033342424173 350694278844387503409065)
                    ·
                      refine ⟨263020709133290627556799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350694278844387503409065 263020709133290627556799)
                      ·
                        rfl

theorem cell23_512231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_512231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512231 prefixEnd_512231 := by exact prefixLift 512231
  have htrace : WordTrace (prefixWord ++ tailWord_512231) baseStart_512231 baseEnd_512231 := by
    simpa [prefixWord, tailWord_512231, baseEnd_512231] using wordTrace_append hprefix tailTrace_512231
  have hstable : (prefixWord ++ tailWord_512231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512231).length < 2 ^ (prefixWord ++ tailWord_512231).sum := by decide
  have hdescent : baseEnd_512231 < baseStart_512231 := by decide
  rcases family_descends (prefixWord ++ tailWord_512231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512250 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 7]
def baseStart_512250 : Nat := 118140960795 + 512250 * 2 ^ 59
def prefixEnd_512250 : Nat := 4983230072969 + 3 ^ 40 * 512250 * 2
def baseEnd_512250 : Nat := 29225607251747339246579

theorem tailTrace_512250 : CollatzResearch.WordTrace tailWord_512250 prefixEnd_512250 29225607251747339246579 := by
  unfold tailWord_512250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4670823098553302545011551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12455528262808806786697469 4670823098553302545011551)
  ·
    refine ⟨7006234647829953817517327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4670823098553302545011551 7006234647829953817517327)
    ·
      refine ⟨10509351971744930726275991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006234647829953817517327 10509351971744930726275991)
      ·
        refine ⟨15764027957617396089413987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10509351971744930726275991 15764027957617396089413987)
        ·
          refine ⟨23646041936426094134120981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15764027957617396089413987 23646041936426094134120981)
          ·
            refine ⟨1108408215769973162536921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23646041936426094134120981 1108408215769973162536921)
            ·
              refine ⟨831306161827479871902691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108408215769973162536921 831306161827479871902691)
              ·
                refine ⟨1246959242741219807854037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831306161827479871902691 1246959242741219807854037)
                ·
                  refine ⟨29225607251747339246579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1246959242741219807854037 29225607251747339246579)
                  ·
                    rfl

theorem cell23_512250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_512250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512250 prefixEnd_512250 := by exact prefixLift 512250
  have htrace : WordTrace (prefixWord ++ tailWord_512250) baseStart_512250 baseEnd_512250 := by
    simpa [prefixWord, tailWord_512250, baseEnd_512250] using wordTrace_append hprefix tailTrace_512250
  have hstable : (prefixWord ++ tailWord_512250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512250).length < 2 ^ (prefixWord ++ tailWord_512250).sum := by decide
  have hdescent : baseEnd_512250 < baseStart_512250 := by decide
  rcases family_descends (prefixWord ++ tailWord_512250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512280 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 2, 5]
def baseStart_512280 : Nat := 118140960795 + 512280 * 2 ^ 59
def prefixEnd_512280 : Nat := 4983230072969 + 3 ^ 40 * 512280 * 2
def baseEnd_512280 : Nat := 87681956561786978614691

theorem tailTrace_512280 : CollatzResearch.WordTrace tailWord_512280 prefixEnd_512280 87681956561786978614691 := by
  unfold tailWord_512280
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342193292052262651819147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12456257722736350202425529 9342193292052262651819147)
  ·
    refine ⟨14013289938078393977728721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9342193292052262651819147 14013289938078393977728721)
    ·
      refine ⟨10509967453558795483296541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14013289938078393977728721 10509967453558795483296541)
      ·
        refine ⟨3941237795084548306236203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10509967453558795483296541 3941237795084548306236203)
        ·
          refine ⟨5911856692626822459354305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941237795084548306236203 5911856692626822459354305)
          ·
            refine ⟨4433892519470116844515729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5911856692626822459354305 4433892519470116844515729)
            ·
              refine ⟨3325419389602587633386797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433892519470116844515729 3325419389602587633386797)
              ·
                refine ⟨1247032271100970362520049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325419389602587633386797 1247032271100970362520049)
                ·
                  refine ⟨935274203325727771890037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247032271100970362520049 935274203325727771890037)
                  ·
                    refine ⟨87681956561786978614691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 935274203325727771890037 87681956561786978614691)
                    ·
                      rfl

theorem cell23_512280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_512280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512280 prefixEnd_512280 := by exact prefixLift 512280
  have htrace : WordTrace (prefixWord ++ tailWord_512280) baseStart_512280 baseEnd_512280 := by
    simpa [prefixWord, tailWord_512280, baseEnd_512280] using wordTrace_append hprefix tailTrace_512280
  have hstable : (prefixWord ++ tailWord_512280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512280).length < 2 ^ (prefixWord ++ tailWord_512280).sum := by decide
  have hdescent : baseEnd_512280 < baseStart_512280 := by decide
  rcases family_descends (prefixWord ++ tailWord_512280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512300 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_512300 : Nat := 118140960795 + 512300 * 2 ^ 59
def prefixEnd_512300 : Nat := 4983230072969 + 3 ^ 40 * 512300 * 2
def baseEnd_512300 : Nat := 263056139298450857593981

theorem tailTrace_512300 : CollatzResearch.WordTrace tailWord_512300 prefixEnd_512300 263056139298450857593981 := by
  unfold tailWord_512300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342558022016034359683177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12456744029354712479577569 9342558022016034359683177)
  ·
    refine ⟨7006918516512025769762383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9342558022016034359683177 7006918516512025769762383)
    ·
      refine ⟨10510377774768038654643575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006918516512025769762383 10510377774768038654643575)
      ·
        refine ⟨15765566662152057981965363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10510377774768038654643575 15765566662152057981965363)
        ·
          refine ⟨23648349993228086972948045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15765566662152057981965363 23648349993228086972948045)
          ·
            refine ⟨8868131247460532614855517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23648349993228086972948045 8868131247460532614855517)
            ·
              refine ⟨3325549217797699730570819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8868131247460532614855517 3325549217797699730570819)
              ·
                refine ⟨4988323826696549595856229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325549217797699730570819 4988323826696549595856229)
                ·
                  refine ⟨935310717505603049223043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4988323826696549595856229 935310717505603049223043)
                  ·
                    refine ⟨1402966076258404573834565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 935310717505603049223043 1402966076258404573834565)
                    ·
                      refine ⟨263056139298450857593981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1402966076258404573834565 263056139298450857593981)
                      ·
                        rfl

theorem cell23_512300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_512300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512300 prefixEnd_512300 := by exact prefixLift 512300
  have htrace : WordTrace (prefixWord ++ tailWord_512300) baseStart_512300 baseEnd_512300 := by
    simpa [prefixWord, tailWord_512300, baseEnd_512300] using wordTrace_append hprefix tailTrace_512300
  have hstable : (prefixWord ++ tailWord_512300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512300).length < 2 ^ (prefixWord ++ tailWord_512300).sum := by decide
  have hdescent : baseEnd_512300 < baseStart_512300 := by decide
  rcases family_descends (prefixWord ++ tailWord_512300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512301 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 7]
def baseStart_512301 : Nat := 118140960795 + 512301 * 2 ^ 59
def prefixEnd_512301 : Nat := 4983230072969 + 3 ^ 40 * 512301 * 2
def baseEnd_512301 : Nat := 29228516975456150409053

theorem tailTrace_512301 : CollatzResearch.WordTrace tailWord_512301 prefixEnd_512301 29228516975456150409053 := by
  unfold tailWord_512301
  simp only [CollatzResearch.WordTrace]
  refine ⟨18685152517028445890152757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12456768344685630593435171 18685152517028445890152757)
  ·
    refine ⟨1751733048471416802201821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18685152517028445890152757 1751733048471416802201821)
    ·
      refine ⟨656899893176781300825683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1751733048471416802201821 656899893176781300825683)
      ·
        refine ⟨985349839765171951238525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656899893176781300825683 985349839765171951238525)
        ·
          refine ⟨369506189911939481714447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985349839765171951238525 369506189911939481714447)
          ·
            refine ⟨554259284867909222571671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369506189911939481714447 554259284867909222571671)
            ·
              refine ⟨831388927301863833857507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554259284867909222571671 831388927301863833857507)
              ·
                refine ⟨1247083390952795750786261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831388927301863833857507 1247083390952795750786261)
                ·
                  refine ⟨29228516975456150409053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1247083390952795750786261 29228516975456150409053)
                  ·
                    rfl

theorem cell23_512301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_512301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512301 prefixEnd_512301 := by exact prefixLift 512301
  have htrace : WordTrace (prefixWord ++ tailWord_512301) baseStart_512301 baseEnd_512301 := by
    simpa [prefixWord, tailWord_512301, baseEnd_512301] using wordTrace_append hprefix tailTrace_512301
  have hstable : (prefixWord ++ tailWord_512301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512301).length < 2 ^ (prefixWord ++ tailWord_512301).sum := by decide
  have hdescent : baseEnd_512301 < baseStart_512301 := by decide
  rcases family_descends (prefixWord ++ tailWord_512301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512320 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3]
def baseStart_512320 : Nat := 118140960795 + 512320 * 2 ^ 59
def prefixEnd_512320 : Nat := 4983230072969 + 3 ^ 40 * 512320 * 2
def baseEnd_512320 : Nat := 263066408911540779343889

theorem tailTrace_512320 : CollatzResearch.WordTrace tailWord_512320 prefixEnd_512320 263066408911540779343889 := by
  unfold tailWord_512320
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342922751979806067547207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12457230335973074756729609 9342922751979806067547207)
  ·
    refine ⟨14014384127969709101320811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9342922751979806067547207 14014384127969709101320811)
    ·
      refine ⟨21021576191954563651981217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14014384127969709101320811 21021576191954563651981217)
      ·
        refine ⟨15766182143965922738985913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21021576191954563651981217 15766182143965922738985913)
        ·
          refine ⟨11824636607974442054239435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15766182143965922738985913 11824636607974442054239435)
          ·
            refine ⟨17736954911961663081359153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11824636607974442054239435 17736954911961663081359153)
            ·
              refine ⟨13302716183971247311019365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17736954911961663081359153 13302716183971247311019365)
              ·
                refine ⟨2494259284494608870816131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13302716183971247311019365 2494259284494608870816131)
                ·
                  refine ⟨3741388926741913306224197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494259284494608870816131 3741388926741913306224197)
                  ·
                    refine ⟨701510423764108744917037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741388926741913306224197 701510423764108744917037)
                    ·
                      refine ⟨263066408911540779343889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701510423764108744917037 263066408911540779343889)
                      ·
                        rfl

theorem cell23_512320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_512320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512320 prefixEnd_512320 := by exact prefixLift 512320
  have htrace : WordTrace (prefixWord ++ tailWord_512320) baseStart_512320 baseEnd_512320 := by
    simpa [prefixWord, tailWord_512320, baseEnd_512320] using wordTrace_append hprefix tailTrace_512320
  have hstable : (prefixWord ++ tailWord_512320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512320).length < 2 ^ (prefixWord ++ tailWord_512320).sum := by decide
  have hdescent : baseEnd_512320 < baseStart_512320 := by decide
  rcases family_descends (prefixWord ++ tailWord_512320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512337 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_512337 : Nat := 118140960795 + 512337 * 2 ^ 59
def prefixEnd_512337 : Nat := 4983230072969 + 3 ^ 40 * 512337 * 2
def baseEnd_512337 : Nat := 263075138082667212831311

theorem tailTrace_512337 : CollatzResearch.WordTrace tailWord_512337 prefixEnd_512337 263075138082667212831311 := by
  unfold tailWord_512337
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686465544898024038463265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12457643696598682692308843 18686465544898024038463265)
  ·
    refine ⟨14014849158673518028847449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18686465544898024038463265 14014849158673518028847449)
    ·
      refine ⟨10511136869005138521635587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14014849158673518028847449 10511136869005138521635587)
      ·
        refine ⟨15766705303507707782453381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10511136869005138521635587 15766705303507707782453381)
        ·
          refine ⟨2956257244407695209210009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15766705303507707782453381 2956257244407695209210009)
          ·
            refine ⟨2217192933305771406907507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956257244407695209210009 2217192933305771406907507)
            ·
              refine ⟨3325789399958657110361261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217192933305771406907507 3325789399958657110361261)
              ·
                refine ⟨1247171024984496416385473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325789399958657110361261 1247171024984496416385473)
                ·
                  refine ⟨935378268738372312289105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247171024984496416385473 935378268738372312289105)
                  ·
                    refine ⟨701533701553779234216829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 935378268738372312289105 701533701553779234216829)
                    ·
                      refine ⟨263075138082667212831311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701533701553779234216829 263075138082667212831311)
                      ·
                        rfl

theorem cell23_512337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_512337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512337 prefixEnd_512337 := by exact prefixLift 512337
  have htrace : WordTrace (prefixWord ++ tailWord_512337) baseStart_512337 baseEnd_512337 := by
    simpa [prefixWord, tailWord_512337, baseEnd_512337] using wordTrace_append hprefix tailTrace_512337
  have hstable : (prefixWord ++ tailWord_512337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512337).length < 2 ^ (prefixWord ++ tailWord_512337).sum := by decide
  have hdescent : baseEnd_512337 < baseStart_512337 := by decide
  rcases family_descends (prefixWord ++ tailWord_512337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512354 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_512354 : Nat := 118140960795 + 512354 * 2 ^ 59
def prefixEnd_512354 : Nat := 4983230072969 + 3 ^ 40 * 512354 * 2
def baseEnd_512354 : Nat := 263083867253793646318733

theorem tailTrace_512354 : CollatzResearch.WordTrace tailWord_512354 prefixEnd_512354 263083867253793646318733 := by
  unfold tailWord_512354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671771396459108985458029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12458057057224290627888077 4671771396459108985458029)
  ·
    refine ⟨1751914273672165869546761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4671771396459108985458029 1751914273672165869546761)
    ·
      refine ⟨1313935705254124402160071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1751914273672165869546761 1313935705254124402160071)
      ·
        refine ⟨1970903557881186603240107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313935705254124402160071 1970903557881186603240107)
        ·
          refine ⟨2956355336821779904860161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970903557881186603240107 2956355336821779904860161)
          ·
            refine ⟨2217266502616334928645121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956355336821779904860161 2217266502616334928645121)
            ·
              refine ⟨1662949876962251196483841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217266502616334928645121 1662949876962251196483841)
              ·
                refine ⟨1247212407721688397362881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662949876962251196483841 1247212407721688397362881)
                ·
                  refine ⟨935409305791266298022161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247212407721688397362881 935409305791266298022161)
                  ·
                    refine ⟨701556979343449723516621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 935409305791266298022161 701556979343449723516621)
                    ·
                      refine ⟨263083867253793646318733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701556979343449723516621 263083867253793646318733)
                      ·
                        rfl

theorem cell23_512354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_512354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512354 prefixEnd_512354 := by exact prefixLift 512354
  have htrace : WordTrace (prefixWord ++ tailWord_512354) baseStart_512354 baseEnd_512354 := by
    simpa [prefixWord, tailWord_512354, baseEnd_512354] using wordTrace_append hprefix tailTrace_512354
  have hstable : (prefixWord ++ tailWord_512354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512354).length < 2 ^ (prefixWord ++ tailWord_512354).sum := by decide
  have hdescent : baseEnd_512354 < baseStart_512354 := by decide
  rcases family_descends (prefixWord ++ tailWord_512354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512357 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 6]
def baseStart_512357 : Nat := 118140960795 + 512357 * 2 ^ 59
def prefixEnd_512357 : Nat := 4983230072969 + 3 ^ 40 * 512357 * 2
def baseEnd_512357 : Nat := 29231711966195237175691

theorem tailTrace_512357 : CollatzResearch.WordTrace tailWord_512357 prefixEnd_512357 29231711966195237175691 := by
  unfold tailWord_512357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18687195004825567454191325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12458130003217044969460883 18687195004825567454191325)
  ·
    refine ⟨7007698126809587795321747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18687195004825567454191325 7007698126809587795321747)
    ·
      refine ⟨10511547190214381692982621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7007698126809587795321747 10511547190214381692982621)
      ·
        refine ⟨3941830196330393134868483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10511547190214381692982621 3941830196330393134868483)
        ·
          refine ⟨5912745294495589702302725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941830196330393134868483 5912745294495589702302725)
          ·
            refine ⟨1108639742717923069181761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5912745294495589702302725 1108639742717923069181761)
            ·
              refine ⟨831479807038442301886321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108639742717923069181761 831479807038442301886321)
              ·
                refine ⟨623609855278831726414741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831479807038442301886321 623609855278831726414741)
                ·
                  refine ⟨29231711966195237175691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 623609855278831726414741 29231711966195237175691)
                  ·
                    rfl

theorem cell23_512357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_512357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512357 prefixEnd_512357 := by exact prefixLift 512357
  have htrace : WordTrace (prefixWord ++ tailWord_512357) baseStart_512357 baseEnd_512357 := by
    simpa [prefixWord, tailWord_512357, baseEnd_512357] using wordTrace_append hprefix tailTrace_512357
  have hstable : (prefixWord ++ tailWord_512357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512357).length < 2 ^ (prefixWord ++ tailWord_512357).sum := by decide
  have hdescent : baseEnd_512357 < baseStart_512357 := by decide
  rcases family_descends (prefixWord ++ tailWord_512357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512377 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 1, 5, 2]
def baseStart_512377 : Nat := 118140960795 + 512377 * 2 ^ 59
def prefixEnd_512377 : Nat := 4983230072969 + 3 ^ 40 * 512377 * 2
def baseEnd_512377 : Nat := 263095677308847056331127

theorem tailTrace_512377 : CollatzResearch.WordTrace tailWord_512377 prefixEnd_512377 263095677308847056331127 := by
  unfold tailWord_512377
  simp only [CollatzResearch.WordTrace]
  refine ⟨18687924464753110869919385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12458616309835407246612923 18687924464753110869919385)
  ·
    refine ⟨14015943348564833152439539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18687924464753110869919385 14015943348564833152439539)
    ·
      refine ⟨21023915022847249728659309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14015943348564833152439539 21023915022847249728659309)
      ·
        refine ⟨7883968133567718648247241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21023915022847249728659309 7883968133567718648247241)
        ·
          refine ⟨5912976100175788986185431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7883968133567718648247241 5912976100175788986185431)
          ·
            refine ⟨8869464150263683479278147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912976100175788986185431 8869464150263683479278147)
            ·
              refine ⟨13304196225395525218917221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869464150263683479278147 13304196225395525218917221)
              ·
                refine ⟨2494536792261660978546979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13304196225395525218917221 2494536792261660978546979)
                ·
                  refine ⟨3741805188392491467820469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494536792261660978546979 3741805188392491467820469)
                  ·
                    refine ⟨350794236411796075108169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3741805188392491467820469 350794236411796075108169)
                    ·
                      refine ⟨263095677308847056331127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350794236411796075108169 263095677308847056331127)
                      ·
                        rfl

theorem cell23_512377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_512377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512377 prefixEnd_512377 := by exact prefixLift 512377
  have htrace : WordTrace (prefixWord ++ tailWord_512377) baseStart_512377 baseEnd_512377 := by
    simpa [prefixWord, tailWord_512377, baseEnd_512377] using wordTrace_append hprefix tailTrace_512377
  have hstable : (prefixWord ++ tailWord_512377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512377).length < 2 ^ (prefixWord ++ tailWord_512377).sum := by decide
  have hdescent : baseEnd_512377 < baseStart_512377 := by decide
  rcases family_descends (prefixWord ++ tailWord_512377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512441 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 3, 2, 2]
def baseStart_512441 : Nat := 118140960795 + 512441 * 2 ^ 59
def prefixEnd_512441 : Nat := 4983230072969 + 3 ^ 40 * 512441 * 2
def baseEnd_512441 : Nat := 263128540070734805930833

theorem tailTrace_512441 : CollatzResearch.WordTrace tailWord_512441 prefixEnd_512441 263128540070734805930833 := by
  unfold tailWord_512441
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690258736521249800249177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12460172491014166533499451 18690258736521249800249177)
  ·
    refine ⟨14017694052390937350186883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18690258736521249800249177 14017694052390937350186883)
    ·
      refine ⟨21026541078586406025280325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14017694052390937350186883 21026541078586406025280325)
      ·
        refine ⟨3942476452234951129740061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21026541078586406025280325 3942476452234951129740061)
        ·
          refine ⟨1478428669588106673652523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3942476452234951129740061 1478428669588106673652523)
          ·
            refine ⟨2217643004382160010478785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478428669588106673652523 2217643004382160010478785)
            ·
              refine ⟨1663232253286620007859089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217643004382160010478785 1663232253286620007859089)
              ·
                refine ⟨1247424189964965005894317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663232253286620007859089 1247424189964965005894317)
                ·
                  refine ⟨467784071236861877210369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247424189964965005894317 467784071236861877210369)
                  ·
                    refine ⟨350838053427646407907777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 467784071236861877210369 350838053427646407907777)
                    ·
                      refine ⟨263128540070734805930833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350838053427646407907777 263128540070734805930833)
                      ·
                        rfl

theorem cell23_512441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_512441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512441 prefixEnd_512441 := by exact prefixLift 512441
  have htrace : WordTrace (prefixWord ++ tailWord_512441) baseStart_512441 baseEnd_512441 := by
    simpa [prefixWord, tailWord_512441, baseEnd_512441] using wordTrace_append hprefix tailTrace_512441
  have hstable : (prefixWord ++ tailWord_512441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512441).length < 2 ^ (prefixWord ++ tailWord_512441).sum := by decide
  have hdescent : baseEnd_512441 < baseStart_512441 := by decide
  rcases family_descends (prefixWord ++ tailWord_512441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512452 : List Nat := [2, 3, 3, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_512452 : Nat := 118140960795 + 512452 * 2 ^ 59
def prefixEnd_512452 : Nat := 4983230072969 + 3 ^ 40 * 512452 * 2
def baseEnd_512452 : Nat := 263134188357934262893283

theorem tailTrace_512452 : CollatzResearch.WordTrace tailWord_512452 prefixEnd_512452 263134188357934262893283 := by
  unfold tailWord_512452
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345329969740699339449805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12460439959654265785933073 9345329969740699339449805)
  ·
    refine ⟨3504498738652762252293677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9345329969740699339449805 3504498738652762252293677)
    ·
      refine ⟨1314187026994785844610129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3504498738652762252293677 1314187026994785844610129)
      ·
        refine ⟨985640270246089383457597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1314187026994785844610129 985640270246089383457597)
        ·
          refine ⟨369615101342283518796599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985640270246089383457597 369615101342283518796599)
          ·
            refine ⟨554422652013425278194899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369615101342283518796599 554422652013425278194899)
            ·
              refine ⟨831633978020137917292349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554422652013425278194899 831633978020137917292349)
              ·
                refine ⟨311862741757551718984631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831633978020137917292349 311862741757551718984631)
                ·
                  refine ⟨467794112636327578476947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311862741757551718984631 467794112636327578476947)
                  ·
                    refine ⟨701691168954491367715421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467794112636327578476947 701691168954491367715421)
                    ·
                      refine ⟨263134188357934262893283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701691168954491367715421 263134188357934262893283)
                      ·
                        rfl

theorem cell23_512452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_512452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512452 prefixEnd_512452 := by exact prefixLift 512452
  have htrace : WordTrace (prefixWord ++ tailWord_512452) baseStart_512452 baseEnd_512452 := by
    simpa [prefixWord, tailWord_512452, baseEnd_512452] using wordTrace_append hprefix tailTrace_512452
  have hstable : (prefixWord ++ tailWord_512452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512452).length < 2 ^ (prefixWord ++ tailWord_512452).sum := by decide
  have hdescent : baseEnd_512452 < baseStart_512452 := by decide
  rcases family_descends (prefixWord ++ tailWord_512452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512457 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 3]
def baseStart_512457 : Nat := 118140960795 + 512457 * 2 ^ 59
def prefixEnd_512457 : Nat := 4983230072969 + 3 ^ 40 * 512457 * 2
def baseEnd_512457 : Nat := 263136755761206743330759

theorem tailTrace_512457 : CollatzResearch.WordTrace tailWord_512457 prefixEnd_512457 263136755761206743330759 := by
  unfold tailWord_512457
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690842304463284532831625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12460561536308856355221083 18690842304463284532831625)
  ·
    refine ⟨14018131728347463399623719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18690842304463284532831625 14018131728347463399623719)
    ·
      refine ⟨21027197592521195099435579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14018131728347463399623719 21027197592521195099435579)
      ·
        refine ⟨31540796388781792649153369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21027197592521195099435579 31540796388781792649153369)
        ·
          refine ⟨23655597291586344486865027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31540796388781792649153369 23655597291586344486865027)
          ·
            refine ⟨35483395937379516730297541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23655597291586344486865027 35483395937379516730297541)
            ·
              refine ⟨6653136738258659386930789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35483395937379516730297541 6653136738258659386930789)
              ·
                refine ⟨1247463138423498635049523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6653136738258659386930789 1247463138423498635049523)
                ·
                  refine ⟨1871194707635247952574285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247463138423498635049523 1871194707635247952574285)
                  ·
                    refine ⟨701698015363217982215357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871194707635247952574285 701698015363217982215357)
                    ·
                      refine ⟨263136755761206743330759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701698015363217982215357 263136755761206743330759)
                      ·
                        rfl

theorem cell23_512457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_512457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512457 prefixEnd_512457 := by exact prefixLift 512457
  have htrace : WordTrace (prefixWord ++ tailWord_512457) baseStart_512457 baseEnd_512457 := by
    simpa [prefixWord, tailWord_512457, baseEnd_512457] using wordTrace_append hprefix tailTrace_512457
  have hstable : (prefixWord ++ tailWord_512457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512457).length < 2 ^ (prefixWord ++ tailWord_512457).sum := by decide
  have hdescent : baseEnd_512457 < baseStart_512457 := by decide
  rcases family_descends (prefixWord ++ tailWord_512457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512467 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 9, 2]
def baseStart_512467 : Nat := 118140960795 + 512467 * 2 ^ 59
def prefixEnd_512467 : Nat := 4983230072969 + 3 ^ 40 * 512467 * 2
def baseEnd_512467 : Nat := 263141890567751704205713

theorem tailTrace_512467 : CollatzResearch.WordTrace tailWord_512467 prefixEnd_512467 263141890567751704205713 := by
  unfold tailWord_512467
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691207034427056240695655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12460804689618037493797103 18691207034427056240695655)
  ·
    refine ⟨28036810551640584361043483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18691207034427056240695655 28036810551640584361043483)
    ·
      refine ⟨42055215827460876541565225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28036810551640584361043483 42055215827460876541565225)
      ·
        refine ⟨31541411870595657406173919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42055215827460876541565225 31541411870595657406173919)
        ·
          refine ⟨47312117805893486109260879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31541411870595657406173919 47312117805893486109260879)
          ·
            refine ⟨70968176708840229163891319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47312117805893486109260879 70968176708840229163891319)
            ·
              refine ⟨106452265063260343745836979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70968176708840229163891319 106452265063260343745836979)
              ·
                refine ⟨159678397594890515618755469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106452265063260343745836979 159678397594890515618755469)
                ·
                  refine ⟨59879399098083943357033301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159678397594890515618755469 59879399098083943357033301)
                  ·
                    refine ⟨350855854090335605607617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59879399098083943357033301 350855854090335605607617)
                    ·
                      refine ⟨263141890567751704205713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350855854090335605607617 263141890567751704205713)
                      ·
                        rfl

theorem cell23_512467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9, 2].length) (baseStart_512467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512467 prefixEnd_512467 := by exact prefixLift 512467
  have htrace : WordTrace (prefixWord ++ tailWord_512467) baseStart_512467 baseEnd_512467 := by
    simpa [prefixWord, tailWord_512467, baseEnd_512467] using wordTrace_append hprefix tailTrace_512467
  have hstable : (prefixWord ++ tailWord_512467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512467).length < 2 ^ (prefixWord ++ tailWord_512467).sum := by decide
  have hdescent : baseEnd_512467 < baseStart_512467 := by decide
  rcases family_descends (prefixWord ++ tailWord_512467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512474 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_512474 : Nat := 118140960795 + 512474 * 2 ^ 59
def prefixEnd_512474 : Nat := 4983230072969 + 3 ^ 40 * 512474 * 2
def baseEnd_512474 : Nat := 263145484932333176818181

theorem tailTrace_512474 : CollatzResearch.WordTrace tailWord_512474 prefixEnd_512474 263145484932333176818181 := by
  unfold tailWord_512474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672865586350424109050119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12460974896934464290800317 4672865586350424109050119)
  ·
    refine ⟨7009298379525636163575179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4672865586350424109050119 7009298379525636163575179)
    ·
      refine ⟨10513947569288454245362769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7009298379525636163575179 10513947569288454245362769)
      ·
        refine ⟨7885460676966340684022077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10513947569288454245362769 7885460676966340684022077)
        ·
          refine ⟨2957047753862377756508279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7885460676966340684022077 2957047753862377756508279)
          ·
            refine ⟨4435571630793566634762419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957047753862377756508279 4435571630793566634762419)
            ·
              refine ⟨6653357446190349952143629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435571630793566634762419 6653357446190349952143629)
              ·
                refine ⟨2495009042321381232053861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6653357446190349952143629 2495009042321381232053861)
                ·
                  refine ⟨467814195435258981010099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495009042321381232053861 467814195435258981010099)
                  ·
                    refine ⟨701721293152888471515149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467814195435258981010099 701721293152888471515149)
                    ·
                      refine ⟨263145484932333176818181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701721293152888471515149 263145484932333176818181)
                      ·
                        rfl

theorem cell23_512474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_512474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512474 prefixEnd_512474 := by exact prefixLift 512474
  have htrace : WordTrace (prefixWord ++ tailWord_512474) baseStart_512474 baseEnd_512474 := by
    simpa [prefixWord, tailWord_512474, baseEnd_512474] using wordTrace_append hprefix tailTrace_512474
  have hstable : (prefixWord ++ tailWord_512474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512474).length < 2 ^ (prefixWord ++ tailWord_512474).sum := by decide
  have hdescent : baseEnd_512474 < baseStart_512474 := by decide
  rcases family_descends (prefixWord ++ tailWord_512474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512477 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_512477 : Nat := 118140960795 + 512477 * 2 ^ 59
def prefixEnd_512477 : Nat := 4983230072969 + 3 ^ 40 * 512477 * 2
def baseEnd_512477 : Nat := 87715675124765555026889

theorem tailTrace_512477 : CollatzResearch.WordTrace tailWord_512477 prefixEnd_512477 87715675124765555026889 := by
  unfold tailWord_512477
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691571764390827948559685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12461047842927218632373123 18691571764390827948559685)
  ·
    refine ⟨3504669705823280240354941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18691571764390827948559685 3504669705823280240354941)
    ·
      refine ⟨1314251139683730090133103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3504669705823280240354941 1314251139683730090133103)
      ·
        refine ⟨1971376709525595135199655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1314251139683730090133103 1971376709525595135199655)
        ·
          refine ⟨2957065064288392702799483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971376709525595135199655 2957065064288392702799483)
          ·
            refine ⟨4435597596432589054199225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957065064288392702799483 4435597596432589054199225)
            ·
              refine ⟨3326698197324441790649419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4435597596432589054199225 3326698197324441790649419)
              ·
                refine ⟨4990047295986662685974129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326698197324441790649419 4990047295986662685974129)
                ·
                  refine ⟨3742535471989997014480597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4990047295986662685974129 3742535471989997014480597)
                  ·
                    refine ⟨87715675124765555026889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3742535471989997014480597 87715675124765555026889)
                    ·
                      rfl

theorem cell23_512477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_512477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512477 prefixEnd_512477 := by exact prefixLift 512477
  have htrace : WordTrace (prefixWord ++ tailWord_512477) baseStart_512477 baseEnd_512477 := by
    simpa [prefixWord, tailWord_512477, baseEnd_512477] using wordTrace_append hprefix tailTrace_512477
  have hstable : (prefixWord ++ tailWord_512477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512477).length < 2 ^ (prefixWord ++ tailWord_512477).sum := by decide
  have hdescent : baseEnd_512477 < baseStart_512477 := by decide
  rcases family_descends (prefixWord ++ tailWord_512477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512485 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_512485 : Nat := 118140960795 + 512485 * 2 ^ 59
def prefixEnd_512485 : Nat := 4983230072969 + 3 ^ 40 * 512485 * 2
def baseEnd_512485 : Nat := 87717044406510877926877

theorem tailTrace_512485 : CollatzResearch.WordTrace tailWord_512485 prefixEnd_512485 87717044406510877926877 := by
  unfold tailWord_512485
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691863548361845314850909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12461242365574563543233939 18691863548361845314850909)
  ·
    refine ⟨7009448830635691993069091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18691863548361845314850909 7009448830635691993069091)
    ·
      refine ⟨10514173245953537989603637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7009448830635691993069091 10514173245953537989603637)
      ·
        refine ⟨985703741808144186525341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10514173245953537989603637 985703741808144186525341)
        ·
          refine ⟨369638903178054069947003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985703741808144186525341 369638903178054069947003)
          ·
            refine ⟨554458354767081104920505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369638903178054069947003 554458354767081104920505)
            ·
              refine ⟨415843766075310828690379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554458354767081104920505 415843766075310828690379)
              ·
                refine ⟨623765649112966243035569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415843766075310828690379 623765649112966243035569)
                ·
                  refine ⟨467824236834724682276677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623765649112966243035569 467824236834724682276677)
                  ·
                    refine ⟨87717044406510877926877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 467824236834724682276677 87717044406510877926877)
                    ·
                      rfl

theorem cell23_512485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_512485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512485 prefixEnd_512485 := by exact prefixLift 512485
  have htrace : WordTrace (prefixWord ++ tailWord_512485) baseStart_512485 baseEnd_512485 := by
    simpa [prefixWord, tailWord_512485, baseEnd_512485] using wordTrace_append hprefix tailTrace_512485
  have hstable : (prefixWord ++ tailWord_512485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512485).length < 2 ^ (prefixWord ++ tailWord_512485).sum := by decide
  have hdescent : baseEnd_512485 < baseStart_512485 := by decide
  rcases family_descends (prefixWord ++ tailWord_512485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512517 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_512517 : Nat := 118140960795 + 512517 * 2 ^ 59
def prefixEnd_512517 : Nat := 4983230072969 + 3 ^ 40 * 512517 * 2
def baseEnd_512517 : Nat := 263167564600476508580483

theorem tailTrace_512517 : CollatzResearch.WordTrace tailWord_512517 prefixEnd_512517 263167564600476508580483 := by
  unfold tailWord_512517
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693030684245914780015805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12462020456163943186677203 18693030684245914780015805)
  ·
    refine ⟨7009886506592218042505927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18693030684245914780015805 7009886506592218042505927)
    ·
      refine ⟨10514829759888327063758891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7009886506592218042505927 10514829759888327063758891)
      ·
        refine ⟨15772244639832490595638337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10514829759888327063758891 15772244639832490595638337)
        ·
          refine ⟨11829183479874367946728753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15772244639832490595638337 11829183479874367946728753)
          ·
            refine ⟨8871887609905775960046565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11829183479874367946728753 8871887609905775960046565)
            ·
              refine ⟨1663478926857332992508731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8871887609905775960046565 1663478926857332992508731)
              ·
                refine ⟨2495218390285999488763097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663478926857332992508731 2495218390285999488763097)
                ·
                  refine ⟨1871413792714499616572323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2495218390285999488763097 1871413792714499616572323)
                  ·
                    refine ⟨2807120689071749424858485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1871413792714499616572323 2807120689071749424858485)
                    ·
                      refine ⟨263167564600476508580483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2807120689071749424858485 263167564600476508580483)
                      ·
                        rfl

theorem cell23_512517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_512517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512517 prefixEnd_512517 := by exact prefixLift 512517
  have htrace : WordTrace (prefixWord ++ tailWord_512517) baseStart_512517 baseEnd_512517 := by
    simpa [prefixWord, tailWord_512517, baseEnd_512517] using wordTrace_append hprefix tailTrace_512517
  have hstable : (prefixWord ++ tailWord_512517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512517).length < 2 ^ (prefixWord ++ tailWord_512517).sum := by decide
  have hdescent : baseEnd_512517 < baseStart_512517 := by decide
  rcases family_descends (prefixWord ++ tailWord_512517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512525 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_512525 : Nat := 118140960795 + 512525 * 2 ^ 59
def prefixEnd_512525 : Nat := 4983230072969 + 3 ^ 40 * 512525 * 2
def baseEnd_512525 : Nat := 263171672445712477280447

theorem tailTrace_512525 : CollatzResearch.WordTrace tailWord_512525 prefixEnd_512525 263171672445712477280447 := by
  unfold tailWord_512525
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693322468216932146307029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12462214978811288097538019 18693322468216932146307029)
  ·
    refine ⟨438124745348834347179071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18693322468216932146307029 438124745348834347179071)
    ·
      refine ⟨657187118023251520768607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438124745348834347179071 657187118023251520768607)
      ·
        refine ⟨985780677034877281152911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657187118023251520768607 985780677034877281152911)
        ·
          refine ⟨1478671015552315921729367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985780677034877281152911 1478671015552315921729367)
          ·
            refine ⟨2218006523328473882594051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478671015552315921729367 2218006523328473882594051)
            ·
              refine ⟨3327009784992710823891077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218006523328473882594051 3327009784992710823891077)
              ·
                refine ⟨623814334686133279479577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3327009784992710823891077 623814334686133279479577)
                ·
                  refine ⟨467860751014599959609683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623814334686133279479577 467860751014599959609683)
                  ·
                    refine ⟨701791126521899939414525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467860751014599959609683 701791126521899939414525)
                    ·
                      refine ⟨263171672445712477280447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701791126521899939414525 263171672445712477280447)
                      ·
                        rfl

theorem cell23_512525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_512525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512525 prefixEnd_512525 := by exact prefixLift 512525
  have htrace : WordTrace (prefixWord ++ tailWord_512525) baseStart_512525 baseEnd_512525 := by
    simpa [prefixWord, tailWord_512525, baseEnd_512525] using wordTrace_append hprefix tailTrace_512525
  have hstable : (prefixWord ++ tailWord_512525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512525).length < 2 ^ (prefixWord ++ tailWord_512525).sum := by decide
  have hdescent : baseEnd_512525 < baseStart_512525 := by decide
  rcases family_descends (prefixWord ++ tailWord_512525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512554 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 7]
def baseStart_512554 : Nat := 118140960795 + 512554 * 2 ^ 59
def prefixEnd_512554 : Nat := 4983230072969 + 3 ^ 40 * 512554 * 2
def baseEnd_512554 : Nat := 29242951487188095979757

theorem tailTrace_512554 : CollatzResearch.WordTrace tailWord_512554 prefixEnd_512554 29242951487188095979757 := by
  unfold tailWord_512554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673595046277967524778179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12462920123407913399408477 4673595046277967524778179)
  ·
    refine ⟨7010392569416951287167269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4673595046277967524778179 7010392569416951287167269)
    ·
      refine ⟨1314448606765678366343863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7010392569416951287167269 1314448606765678366343863)
      ·
        refine ⟨1971672910148517549515795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1314448606765678366343863 1971672910148517549515795)
        ·
          refine ⟨2957509365222776324273693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971672910148517549515795 2957509365222776324273693)
          ·
            refine ⟨1109066011958541121602635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2957509365222776324273693 1109066011958541121602635)
            ·
              refine ⟨1663599017937811682403953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109066011958541121602635 1663599017937811682403953)
              ·
                refine ⟨1247699263453358761802965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663599017937811682403953 1247699263453358761802965)
                ·
                  refine ⟨29242951487188095979757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1247699263453358761802965 29242951487188095979757)
                  ·
                    rfl

theorem cell23_512554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_512554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512554 prefixEnd_512554 := by exact prefixLift 512554
  have htrace : WordTrace (prefixWord ++ tailWord_512554) baseStart_512554 baseEnd_512554 := by
    simpa [prefixWord, tailWord_512554, baseEnd_512554] using wordTrace_append hprefix tailTrace_512554
  have hstable : (prefixWord ++ tailWord_512554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512554).length < 2 ^ (prefixWord ++ tailWord_512554).sum := by decide
  have hdescent : baseEnd_512554 < baseStart_512554 := by decide
  rcases family_descends (prefixWord ++ tailWord_512554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512567 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 1, 7]
def baseStart_512567 : Nat := 118140960795 + 512567 * 2 ^ 59
def prefixEnd_512567 : Nat := 4983230072969 + 3 ^ 40 * 512567 * 2
def baseEnd_512567 : Nat := 87731079544400437651751

theorem tailTrace_512567 : CollatzResearch.WordTrace tailWord_512567 prefixEnd_512567 87731079544400437651751 := by
  unfold tailWord_512567
  simp only [CollatzResearch.WordTrace]
  refine ⟨18694854334064773319335955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12463236222709848879557303 18694854334064773319335955)
  ·
    refine ⟨28042281501097159979003933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18694854334064773319335955 28042281501097159979003933)
    ·
      refine ⟨10515855562911434992126475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28042281501097159979003933 10515855562911434992126475)
      ·
        refine ⟨15773783344367152488189713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10515855562911434992126475 15773783344367152488189713)
        ·
          refine ⟨11830337508275364366142285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15773783344367152488189713 11830337508275364366142285)
          ·
            refine ⟨4436376565603261637303357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11830337508275364366142285 4436376565603261637303357)
            ·
              refine ⟨1663641212101223113988759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436376565603261637303357 1663641212101223113988759)
              ·
                refine ⟨2495461818151834670983139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663641212101223113988759 2495461818151834670983139)
                ·
                  refine ⟨3743192727227752006474709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495461818151834670983139 3743192727227752006474709)
                  ·
                    refine ⟨87731079544400437651751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3743192727227752006474709 87731079544400437651751)
                    ·
                      rfl

theorem cell23_512567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_512567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512567 prefixEnd_512567 := by exact prefixLift 512567
  have htrace : WordTrace (prefixWord ++ tailWord_512567) baseStart_512567 baseEnd_512567 := by
    simpa [prefixWord, tailWord_512567, baseEnd_512567] using wordTrace_append hprefix tailTrace_512567
  have hstable : (prefixWord ++ tailWord_512567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512567).length < 2 ^ (prefixWord ++ tailWord_512567).sum := by decide
  have hdescent : baseEnd_512567 < baseStart_512567 := by decide
  rcases family_descends (prefixWord ++ tailWord_512567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512582 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_512582 : Nat := 118140960795 + 512582 * 2 ^ 59
def prefixEnd_512582 : Nat := 4983230072969 + 3 ^ 40 * 512582 * 2
def baseEnd_512582 : Nat := 263200940843018754267685

theorem tailTrace_512582 : CollatzResearch.WordTrace tailWord_512582 prefixEnd_512582 263200940843018754267685 := by
  unfold tailWord_512582
  simp only [CollatzResearch.WordTrace]
  refine ⟨584231294656575965035375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12463600952673620587421333 584231294656575965035375)
  ·
    refine ⟨876346941984863947553063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 584231294656575965035375 876346941984863947553063)
    ·
      refine ⟨1314520412977295921329595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 876346941984863947553063 1314520412977295921329595)
      ·
        refine ⟨1971780619465943881994393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1314520412977295921329595 1971780619465943881994393)
        ·
          refine ⟨1478835464599457911495795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1971780619465943881994393 1478835464599457911495795)
          ·
            refine ⟨2218253196899186867243693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478835464599457911495795 2218253196899186867243693)
            ·
              refine ⟨831844948837195075216385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2218253196899186867243693 831844948837195075216385)
              ·
                refine ⟨623883711627896306412289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831844948837195075216385 623883711627896306412289)
                ·
                  refine ⟨467912783720922229809217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623883711627896306412289 467912783720922229809217)
                  ·
                    refine ⟨350934587790691672356913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 467912783720922229809217 350934587790691672356913)
                    ·
                      refine ⟨263200940843018754267685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 350934587790691672356913 263200940843018754267685)
                      ·
                        rfl

theorem cell23_512582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_512582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512582 prefixEnd_512582 := by exact prefixLift 512582
  have htrace : WordTrace (prefixWord ++ tailWord_512582) baseStart_512582 baseEnd_512582 := by
    simpa [prefixWord, tailWord_512582, baseEnd_512582] using wordTrace_append hprefix tailTrace_512582
  have hstable : (prefixWord ++ tailWord_512582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512582).length < 2 ^ (prefixWord ++ tailWord_512582).sum := by decide
  have hdescent : baseEnd_512582 < baseStart_512582 := by decide
  rcases family_descends (prefixWord ++ tailWord_512582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512617 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_512617 : Nat := 118140960795 + 512617 * 2 ^ 59
def prefixEnd_512617 : Nat := 4983230072969 + 3 ^ 40 * 512617 * 2
def baseEnd_512617 : Nat := 263218912665926117330023

theorem tailTrace_512617 : CollatzResearch.WordTrace tailWord_512617 prefixEnd_512617 263218912665926117330023 := by
  unfold tailWord_512617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18696677983883631858656105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12464451989255754572437403 18696677983883631858656105)
  ·
    refine ⟨14022508487912723893992079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18696677983883631858656105 14022508487912723893992079)
    ·
      refine ⟨21033762731869085840988119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14022508487912723893992079 21033762731869085840988119)
      ·
        refine ⟨31550644097803628761482179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21033762731869085840988119 31550644097803628761482179)
        ·
          refine ⟨47325966146705443142223269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31550644097803628761482179 47325966146705443142223269)
          ·
            refine ⟨8873618652507270589166863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47325966146705443142223269 8873618652507270589166863)
            ·
              refine ⟨13310427978760905883750295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8873618652507270589166863 13310427978760905883750295)
              ·
                refine ⟨19965641968141358825625443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13310427978760905883750295 19965641968141358825625443)
                ·
                  refine ⟨29948462952212038238438165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19965641968141358825625443 29948462952212038238438165)
                  ·
                    refine ⟨1403834200884939292426789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29948462952212038238438165 1403834200884939292426789)
                    ·
                      refine ⟨263218912665926117330023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1403834200884939292426789 263218912665926117330023)
                      ·
                        rfl

theorem cell23_512617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_512617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512617 prefixEnd_512617 := by exact prefixLift 512617
  have htrace : WordTrace (prefixWord ++ tailWord_512617) baseStart_512617 baseEnd_512617 := by
    simpa [prefixWord, tailWord_512617, baseEnd_512617] using wordTrace_append hprefix tailTrace_512617
  have hstable : (prefixWord ++ tailWord_512617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512617).length < 2 ^ (prefixWord ++ tailWord_512617).sum := by decide
  have hdescent : baseEnd_512617 < baseStart_512617 := by decide
  rcases family_descends (prefixWord ++ tailWord_512617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512641 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_512641 : Nat := 118140960795 + 512641 * 2 ^ 59
def prefixEnd_512641 : Nat := 4983230072969 + 3 ^ 40 * 512641 * 2
def baseEnd_512641 : Nat := 263231236201634023429913

theorem tailTrace_512641 : CollatzResearch.WordTrace tailWord_512641 prefixEnd_512641 263231236201634023429913 := by
  unfold tailWord_512641
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697553335796683957529777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12465035557197789305019851 18697553335796683957529777)
  ·
    refine ⟨14023165001847512968147333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18697553335796683957529777 14023165001847512968147333)
    ·
      refine ⟨2629343437846408681527625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14023165001847512968147333 2629343437846408681527625)
      ·
        refine ⟨1972007578384806511145719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2629343437846408681527625 1972007578384806511145719)
        ·
          refine ⟨2958011367577209766718579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972007578384806511145719 2958011367577209766718579)
          ·
            refine ⟨4437017051365814650077869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958011367577209766718579 4437017051365814650077869)
            ·
              refine ⟨1663881394262180493779201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4437017051365814650077869 1663881394262180493779201)
              ·
                refine ⟨1247911045696635370334401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663881394262180493779201 1247911045696635370334401)
                ·
                  refine ⟨935933284272476527750801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1247911045696635370334401 935933284272476527750801)
                  ·
                    refine ⟨701949963204357395813101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 935933284272476527750801 701949963204357395813101)
                    ·
                      refine ⟨263231236201634023429913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 701949963204357395813101 263231236201634023429913)
                      ·
                        rfl

theorem cell23_512641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_512641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512641 prefixEnd_512641 := by exact prefixLift 512641
  have htrace : WordTrace (prefixWord ++ tailWord_512641) baseStart_512641 baseEnd_512641 := by
    simpa [prefixWord, tailWord_512641, baseEnd_512641] using wordTrace_append hprefix tailTrace_512641
  have hstable : (prefixWord ++ tailWord_512641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512641).length < 2 ^ (prefixWord ++ tailWord_512641).sum := by decide
  have hdescent : baseEnd_512641 < baseStart_512641 := by decide
  rcases family_descends (prefixWord ++ tailWord_512641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512644 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 8]
def baseStart_512644 : Nat := 118140960795 + 512644 * 2 ^ 59
def prefixEnd_512644 : Nat := 4983230072969 + 3 ^ 40 * 512644 * 2
def baseEnd_512644 : Nat := 29248086293733056854711

theorem tailTrace_512644 : CollatzResearch.WordTrace tailWord_512644 prefixEnd_512644 29248086293733056854711 := by
  unfold tailWord_512644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9348831377392907734944493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12465108503190543646592657 9348831377392907734944493)
  ·
    refine ⟨3505811766522340400604185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9348831377392907734944493 3505811766522340400604185)
    ·
      refine ⟨2629358824891755300453139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3505811766522340400604185 2629358824891755300453139)
      ·
        refine ⟨3944038237337632950679709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629358824891755300453139 3944038237337632950679709)
        ·
          refine ⟨1479014339001612356504891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3944038237337632950679709 1479014339001612356504891)
          ·
            refine ⟨2218521508502418534757337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479014339001612356504891 2218521508502418534757337)
            ·
              refine ⟨1663891131376813901068003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218521508502418534757337 1663891131376813901068003)
              ·
                refine ⟨2495836697065220851602005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663891131376813901068003 2495836697065220851602005)
                ·
                  refine ⟨29248086293733056854711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2495836697065220851602005 29248086293733056854711)
                  ·
                    rfl

theorem cell23_512644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_512644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512644 prefixEnd_512644 := by exact prefixLift 512644
  have htrace : WordTrace (prefixWord ++ tailWord_512644) baseStart_512644 baseEnd_512644 := by
    simpa [prefixWord, tailWord_512644, baseEnd_512644] using wordTrace_append hprefix tailTrace_512644
  have hstable : (prefixWord ++ tailWord_512644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512644).length < 2 ^ (prefixWord ++ tailWord_512644).sum := by decide
  have hdescent : baseEnd_512644 < baseStart_512644 := by decide
  rcases family_descends (prefixWord ++ tailWord_512644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512667 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5]
def baseStart_512667 : Nat := 118140960795 + 512667 * 2 ^ 59
def prefixEnd_512667 : Nat := 4983230072969 + 3 ^ 40 * 512667 * 2
def baseEnd_512667 : Nat := 263244586698650921704793

theorem tailTrace_512667 : CollatzResearch.WordTrace tailWord_512667 prefixEnd_512667 263244586698650921704793 := by
  unfold tailWord_512667
  simp only [CollatzResearch.WordTrace]
  refine ⟨18698501633702490397976255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12465667755801660265317503 18698501633702490397976255)
  ·
    refine ⟨28047752450553735596964383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18698501633702490397976255 28047752450553735596964383)
    ·
      refine ⟨42071628675830603395446575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28047752450553735596964383 42071628675830603395446575)
      ·
        refine ⟨63107443013745905093169863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42071628675830603395446575 63107443013745905093169863)
        ·
          refine ⟨94661164520618857639754795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63107443013745905093169863 94661164520618857639754795)
          ·
            refine ⟨141991746780928286459632193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94661164520618857639754795 141991746780928286459632193)
            ·
              refine ⟨106493810085696214844724145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141991746780928286459632193 106493810085696214844724145)
              ·
                refine ⟨79870357564272161133543109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106493810085696214844724145 79870357564272161133543109)
                ·
                  refine ⟨14975692043301030212539333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79870357564272161133543109 14975692043301030212539333)
                  ·
                    refine ⟨2807942258118943164851125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14975692043301030212539333 2807942258118943164851125)
                    ·
                      refine ⟨263244586698650921704793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2807942258118943164851125 263244586698650921704793)
                      ·
                        rfl

theorem cell23_512667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_512667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512667 prefixEnd_512667 := by exact prefixLift 512667
  have htrace : WordTrace (prefixWord ++ tailWord_512667) baseStart_512667 baseEnd_512667 := by
    simpa [prefixWord, tailWord_512667, baseEnd_512667] using wordTrace_append hprefix tailTrace_512667
  have hstable : (prefixWord ++ tailWord_512667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512667).length < 2 ^ (prefixWord ++ tailWord_512667).sum := by decide
  have hdescent : baseEnd_512667 < baseStart_512667 := by decide
  rcases family_descends (prefixWord ++ tailWord_512667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512681 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 2, 3, 2]
def baseStart_512681 : Nat := 118140960795 + 512681 * 2 ^ 59
def prefixEnd_512681 : Nat := 4983230072969 + 3 ^ 40 * 512681 * 2
def baseEnd_512681 : Nat := 263251775427813866929729

theorem tailTrace_512681 : CollatzResearch.WordTrace tailWord_512681 prefixEnd_512681 263251775427813866929729 := by
  unfold tailWord_512681
  simp only [CollatzResearch.WordTrace]
  refine ⟨18699012255651770788985897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12466008170434513859323931 18699012255651770788985897)
  ·
    refine ⟨14024259191738828091739423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18699012255651770788985897 14024259191738828091739423)
    ·
      refine ⟨21036388787608242137609135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14024259191738828091739423 21036388787608242137609135)
      ·
        refine ⟨31554583181412363206413703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21036388787608242137609135 31554583181412363206413703)
        ·
          refine ⟨47331874772118544809620555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31554583181412363206413703 47331874772118544809620555)
          ·
            refine ⟨70997812158177817214430833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47331874772118544809620555 70997812158177817214430833)
            ·
              refine ⟨53248359118633362910823125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70997812158177817214430833 53248359118633362910823125)
              ·
                refine ⟨1248008416842969443222417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53248359118633362910823125 1248008416842969443222417)
                ·
                  refine ⟨936006312632227082416813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248008416842969443222417 936006312632227082416813)
                  ·
                    refine ⟨351002367237085155906305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936006312632227082416813 351002367237085155906305)
                    ·
                      refine ⟨263251775427813866929729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351002367237085155906305 263251775427813866929729)
                      ·
                        rfl

theorem cell23_512681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 3, 2].length) (baseStart_512681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512681 prefixEnd_512681 := by exact prefixLift 512681
  have htrace : WordTrace (prefixWord ++ tailWord_512681) baseStart_512681 baseEnd_512681 := by
    simpa [prefixWord, tailWord_512681, baseEnd_512681] using wordTrace_append hprefix tailTrace_512681
  have hstable : (prefixWord ++ tailWord_512681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512681).length < 2 ^ (prefixWord ++ tailWord_512681).sum := by decide
  have hdescent : baseEnd_512681 < baseStart_512681 := by decide
  rcases family_descends (prefixWord ++ tailWord_512681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512688 : List Nat := [2, 1, 1, 1, 2, 1, 3, 7, 1, 1, 3]
def baseStart_512688 : Nat := 118140960795 + 512688 * 2 ^ 59
def prefixEnd_512688 : Nat := 4983230072969 + 3 ^ 40 * 512688 * 2
def baseEnd_512688 : Nat := 263255369792395339542197

theorem tailTrace_512688 : CollatzResearch.WordTrace tailWord_512688 prefixEnd_512688 263255369792395339542197 := by
  unfold tailWord_512688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349633783313205492245359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12466178377750940656327145 9349633783313205492245359)
  ·
    refine ⟨14024450674969808238368039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9349633783313205492245359 14024450674969808238368039)
    ·
      refine ⟨21036676012454712357552059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14024450674969808238368039 21036676012454712357552059)
      ·
        refine ⟨31555014018682068536328089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21036676012454712357552059 31555014018682068536328089)
        ·
          refine ⟨23666260514011551402246067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31555014018682068536328089 23666260514011551402246067)
          ·
            refine ⟨35499390771017327103369101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23666260514011551402246067 35499390771017327103369101)
            ·
              refine ⟨13312271539131497663763413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35499390771017327103369101 13312271539131497663763413)
              ·
                refine ⟨312006364198394476494455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13312271539131497663763413 312006364198394476494455)
                ·
                  refine ⟨468009546297591714741683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312006364198394476494455 468009546297591714741683)
                  ·
                    refine ⟨702014319446387572112525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 468009546297591714741683 702014319446387572112525)
                    ·
                      refine ⟨263255369792395339542197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702014319446387572112525 263255369792395339542197)
                      ·
                        rfl

theorem cell23_512688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 1, 3].length) (baseStart_512688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512688 prefixEnd_512688 := by exact prefixLift 512688
  have htrace : WordTrace (prefixWord ++ tailWord_512688) baseStart_512688 baseEnd_512688 := by
    simpa [prefixWord, tailWord_512688, baseEnd_512688] using wordTrace_append hprefix tailTrace_512688
  have hstable : (prefixWord ++ tailWord_512688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512688).length < 2 ^ (prefixWord ++ tailWord_512688).sum := by decide
  have hdescent : baseEnd_512688 < baseStart_512688 := by decide
  rcases family_descends (prefixWord ++ tailWord_512688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512721 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 2, 4]
def baseStart_512721 : Nat := 118140960795 + 512721 * 2 ^ 59
def prefixEnd_512721 : Nat := 4983230072969 + 3 ^ 40 * 512721 * 2
def baseEnd_512721 : Nat := 87757438217997903476515

theorem tailTrace_512721 : CollatzResearch.WordTrace tailWord_512721 prefixEnd_512721 87757438217997903476515 := by
  unfold tailWord_512721
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700471175506857620442017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12466980783671238413628011 18700471175506857620442017)
  ·
    refine ⟨14025353381630143215331513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18700471175506857620442017 14025353381630143215331513)
    ·
      refine ⟨10519015036222607411498635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14025353381630143215331513 10519015036222607411498635)
      ·
        refine ⟨15778522554333911117247953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519015036222607411498635 15778522554333911117247953)
        ·
          refine ⟨11833891915750433337935965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15778522554333911117247953 11833891915750433337935965)
          ·
            refine ⟨4437709468406412501725987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11833891915750433337935965 4437709468406412501725987)
            ·
              refine ⟨6656564202609618752588981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437709468406412501725987 6656564202609618752588981)
              ·
                refine ⟨624052893994651758055217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6656564202609618752588981 624052893994651758055217)
                ·
                  refine ⟨468039670495988818541413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624052893994651758055217 468039670495988818541413)
                  ·
                    refine ⟨87757438217997903476515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468039670495988818541413 87757438217997903476515)
                    ·
                      rfl

theorem cell23_512721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_512721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512721 prefixEnd_512721 := by exact prefixLift 512721
  have htrace : WordTrace (prefixWord ++ tailWord_512721) baseStart_512721 baseEnd_512721 := by
    simpa [prefixWord, tailWord_512721, baseEnd_512721] using wordTrace_append hprefix tailTrace_512721
  have hstable : (prefixWord ++ tailWord_512721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512721).length < 2 ^ (prefixWord ++ tailWord_512721).sum := by decide
  have hdescent : baseEnd_512721 < baseStart_512721 := by decide
  rcases family_descends (prefixWord ++ tailWord_512721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512728 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 5, 2, 2]
def baseStart_512728 : Nat := 118140960795 + 512728 * 2 ^ 59
def prefixEnd_512728 : Nat := 4983230072969 + 3 ^ 40 * 512728 * 2
def baseEnd_512728 : Nat := 263275909018575183042013

theorem tailTrace_512728 : CollatzResearch.WordTrace tailWord_512728 prefixEnd_512728 263275909018575183042013 := by
  unfold tailWord_512728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350363243240748907973419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12467150990987665210631225 9350363243240748907973419)
  ·
    refine ⟨14025544864861123361960129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9350363243240748907973419 14025544864861123361960129)
    ·
      refine ⟨10519158648645842521470097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14025544864861123361960129 10519158648645842521470097)
      ·
        refine ⟨7889368986484381891102573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10519158648645842521470097 7889368986484381891102573)
        ·
          refine ⟨2958513369931643209163465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7889368986484381891102573 2958513369931643209163465)
          ·
            refine ⟨2218885027448732406872599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958513369931643209163465 2218885027448732406872599)
            ·
              refine ⟨3328327541173098610308899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218885027448732406872599 3328327541173098610308899)
              ·
                refine ⟨4992491311759647915463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328327541173098610308899 4992491311759647915463349)
                ·
                  refine ⟨468046060477466992074689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4992491311759647915463349 468046060477466992074689)
                  ·
                    refine ⟨351034545358100244056017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 468046060477466992074689 351034545358100244056017)
                    ·
                      refine ⟨263275909018575183042013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351034545358100244056017 263275909018575183042013)
                      ·
                        rfl

theorem cell23_512728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_512728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512728 prefixEnd_512728 := by exact prefixLift 512728
  have htrace : WordTrace (prefixWord ++ tailWord_512728) baseStart_512728 baseEnd_512728 := by
    simpa [prefixWord, tailWord_512728, baseEnd_512728] using wordTrace_append hprefix tailTrace_512728
  have hstable : (prefixWord ++ tailWord_512728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512728).length < 2 ^ (prefixWord ++ tailWord_512728).sum := by decide
  have hdescent : baseEnd_512728 < baseStart_512728 := by decide
  rcases family_descends (prefixWord ++ tailWord_512728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512732 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_512732 : Nat := 118140960795 + 512732 * 2 ^ 59
def prefixEnd_512732 : Nat := 4983230072969 + 3 ^ 40 * 512732 * 2
def baseEnd_512732 : Nat := 263277962941193167391995

theorem tailTrace_512732 : CollatzResearch.WordTrace tailWord_512732 prefixEnd_512732 263277962941193167391995 := by
  unfold tailWord_512732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350436189233503249546225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12467248252311337666061633 9350436189233503249546225)
  ·
    refine ⟨7012827141925127437159669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9350436189233503249546225 7012827141925127437159669)
    ·
      refine ⟨657452544555480697233719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7012827141925127437159669 657452544555480697233719)
      ·
        refine ⟨986178816833221045850579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657452544555480697233719 986178816833221045850579)
        ·
          refine ⟨1479268225249831568775869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986178816833221045850579 1479268225249831568775869)
          ·
            refine ⟨554725584468686838290951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1479268225249831568775869 554725584468686838290951)
            ·
              refine ⟨832088376703030257436427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554725584468686838290951 832088376703030257436427)
              ·
                refine ⟨1248132565054545386154641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832088376703030257436427 1248132565054545386154641)
                ·
                  refine ⟨936099423790909039615981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248132565054545386154641 936099423790909039615981)
                  ·
                    refine ⟨351037283921590889855993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936099423790909039615981 351037283921590889855993)
                    ·
                      refine ⟨263277962941193167391995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351037283921590889855993 263277962941193167391995)
                      ·
                        rfl

theorem cell23_512732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_512732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512732 prefixEnd_512732 := by exact prefixLift 512732
  have htrace : WordTrace (prefixWord ++ tailWord_512732) baseStart_512732 baseEnd_512732 := by
    simpa [prefixWord, tailWord_512732, baseEnd_512732] using wordTrace_append hprefix tailTrace_512732
  have hstable : (prefixWord ++ tailWord_512732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512732).length < 2 ^ (prefixWord ++ tailWord_512732).sum := by decide
  have hdescent : baseEnd_512732 < baseStart_512732 := by decide
  rcases family_descends (prefixWord ++ tailWord_512732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512741 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_512741 : Nat := 118140960795 + 512741 * 2 ^ 59
def prefixEnd_512741 : Nat := 4983230072969 + 3 ^ 40 * 512741 * 2
def baseEnd_512741 : Nat := 263282584267083632179453

theorem tailTrace_512741 : CollatzResearch.WordTrace tailWord_512741 prefixEnd_512741 263282584267083632179453 := by
  unfold tailWord_512741
  simp only [CollatzResearch.WordTrace]
  refine ⟨18701200635434401036170077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12467467090289600690780051 18701200635434401036170077)
  ·
    refine ⟨7012950238287900388563779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18701200635434401036170077 7012950238287900388563779)
    ·
      refine ⟨10519425357431850582845669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012950238287900388563779 10519425357431850582845669)
      ·
        refine ⟨1972392254518471984283563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10519425357431850582845669 1972392254518471984283563)
        ·
          refine ⟨2958588381777707976425345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972392254518471984283563 2958588381777707976425345)
          ·
            refine ⟨2218941286333280982319009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958588381777707976425345 2218941286333280982319009)
            ·
              refine ⟨1664205964749960736739257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218941286333280982319009 1664205964749960736739257)
              ·
                refine ⟨1248154473562470552554443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664205964749960736739257 1248154473562470552554443)
                ·
                  refine ⟨1872231710343705828831665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248154473562470552554443 1872231710343705828831665)
                  ·
                    refine ⟨1404173782757779371623749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1872231710343705828831665 1404173782757779371623749)
                    ·
                      refine ⟨263282584267083632179453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1404173782757779371623749 263282584267083632179453)
                      ·
                        rfl

theorem cell23_512741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_512741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512741 prefixEnd_512741 := by exact prefixLift 512741
  have htrace : WordTrace (prefixWord ++ tailWord_512741) baseStart_512741 baseEnd_512741 := by
    simpa [prefixWord, tailWord_512741, baseEnd_512741] using wordTrace_append hprefix tailTrace_512741
  have hstable : (prefixWord ++ tailWord_512741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512741).length < 2 ^ (prefixWord ++ tailWord_512741).sum := by decide
  have hdescent : baseEnd_512741 < baseStart_512741 := by decide
  rcases family_descends (prefixWord ++ tailWord_512741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512745 : List Nat := [1, 2, 1, 1, 1, 2, 5, 5, 1, 2, 2]
def baseStart_512745 : Nat := 118140960795 + 512745 * 2 ^ 59
def prefixEnd_512745 : Nat := 4983230072969 + 3 ^ 40 * 512745 * 2
def baseEnd_512745 : Nat := 263284638189701616529435

theorem tailTrace_512745 : CollatzResearch.WordTrace tailWord_512745 prefixEnd_512745 263284638189701616529435 := by
  unfold tailWord_512745
  simp only [CollatzResearch.WordTrace]
  refine ⟨18701346527419909719315689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12467564351613273146210459 18701346527419909719315689)
  ·
    refine ⟨14026009895564932289486767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18701346527419909719315689 14026009895564932289486767)
    ·
      refine ⟨21039014843347398434230151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14026009895564932289486767 21039014843347398434230151)
      ·
        refine ⟨31558522265021097651345227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21039014843347398434230151 31558522265021097651345227)
        ·
          refine ⟨47337783397531646477017841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31558522265021097651345227 47337783397531646477017841)
          ·
            refine ⟨35503337548148734857763381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47337783397531646477017841 35503337548148734857763381)
            ·
              refine ⟨3328437895138943892915317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35503337548148734857763381 3328437895138943892915317)
              ·
                refine ⟨312041052669275989960811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3328437895138943892915317 312041052669275989960811)
                ·
                  refine ⟨468061579003913984941217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312041052669275989960811 468061579003913984941217)
                  ·
                    refine ⟨351046184252935488705913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 468061579003913984941217 351046184252935488705913)
                    ·
                      refine ⟨263284638189701616529435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351046184252935488705913 263284638189701616529435)
                      ·
                        rfl

theorem cell23_512745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 2, 2].length) (baseStart_512745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512745 prefixEnd_512745 := by exact prefixLift 512745
  have htrace : WordTrace (prefixWord ++ tailWord_512745) baseStart_512745 baseEnd_512745 := by
    simpa [prefixWord, tailWord_512745, baseEnd_512745] using wordTrace_append hprefix tailTrace_512745
  have hstable : (prefixWord ++ tailWord_512745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512745).length < 2 ^ (prefixWord ++ tailWord_512745).sum := by decide
  have hdescent : baseEnd_512745 < baseStart_512745 := by decide
  rcases family_descends (prefixWord ++ tailWord_512745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512813 : List Nat := [1, 5, 3, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_512813 : Nat := 118140960795 + 512813 * 2 ^ 59
def prefixEnd_512813 : Nat := 4983230072969 + 3 ^ 40 * 512813 * 2
def baseEnd_512813 : Nat := 263319554874207350479123

theorem tailTrace_512813 : CollatzResearch.WordTrace tailWord_512813 prefixEnd_512813 263319554874207350479123 := by
  unfold tailWord_512813
  simp only [CollatzResearch.WordTrace]
  refine ⟨18703826691173557332791093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12469217794115704888527395 18703826691173557332791093)
  ·
    refine ⟨1753483752297520999949165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18703826691173557332791093 1753483752297520999949165)
    ·
      refine ⟨657556407111570374980937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1753483752297520999949165 657556407111570374980937)
      ·
        refine ⟨493167305333677781235703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657556407111570374980937 493167305333677781235703)
        ·
          refine ⟨739750958000516671853555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493167305333677781235703 739750958000516671853555)
          ·
            refine ⟨1109626437000775007780333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739750958000516671853555 1109626437000775007780333)
            ·
              refine ⟨416109913875290627917625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1109626437000775007780333 416109913875290627917625)
              ·
                refine ⟨312082435406467970938219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416109913875290627917625 312082435406467970938219)
                ·
                  refine ⟨468123653109701956407329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312082435406467970938219 468123653109701956407329)
                  ·
                    refine ⟨351092739832276467305497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 468123653109701956407329 351092739832276467305497)
                    ·
                      refine ⟨263319554874207350479123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351092739832276467305497 263319554874207350479123)
                      ·
                        rfl

theorem cell23_512813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_512813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512813 prefixEnd_512813 := by exact prefixLift 512813
  have htrace : WordTrace (prefixWord ++ tailWord_512813) baseStart_512813 baseEnd_512813 := by
    simpa [prefixWord, tailWord_512813, baseEnd_512813] using wordTrace_append hprefix tailTrace_512813
  have hstable : (prefixWord ++ tailWord_512813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512813).length < 2 ^ (prefixWord ++ tailWord_512813).sum := by decide
  have hdescent : baseEnd_512813 < baseStart_512813 := by decide
  rcases family_descends (prefixWord ++ tailWord_512813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512829 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_512829 : Nat := 118140960795 + 512829 * 2 ^ 59
def prefixEnd_512829 : Nat := 4983230072969 + 3 ^ 40 * 512829 * 2
def baseEnd_512829 : Nat := 263327770564679287879049

theorem tailTrace_512829 : CollatzResearch.WordTrace tailWord_512829 prefixEnd_512829 263327770564679287879049 := by
  unfold tailWord_512829
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704410259115592065373541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12469606839410394710249027 18704410259115592065373541)
  ·
    refine ⟨3507076923584173512257539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18704410259115592065373541 3507076923584173512257539)
    ·
      refine ⟨5260615385376260268386309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507076923584173512257539 5260615385376260268386309)
      ·
        refine ⟨986365384758048800322433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5260615385376260268386309 986365384758048800322433)
        ·
          refine ⟨739774038568536600241825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 986365384758048800322433 739774038568536600241825)
          ·
            refine ⟨554830528926402450181369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739774038568536600241825 554830528926402450181369)
            ·
              refine ⟨416122896694801837636027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554830528926402450181369 416122896694801837636027)
              ·
                refine ⟨624184345042202756454041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416122896694801837636027 624184345042202756454041)
                ·
                  refine ⟨468138258781652067340531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624184345042202756454041 468138258781652067340531)
                  ·
                    refine ⟨702207388172478101010797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 468138258781652067340531 702207388172478101010797)
                    ·
                      refine ⟨263327770564679287879049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702207388172478101010797 263327770564679287879049)
                      ·
                        rfl

theorem cell23_512829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_512829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512829 prefixEnd_512829 := by exact prefixLift 512829
  have htrace : WordTrace (prefixWord ++ tailWord_512829) baseStart_512829 baseEnd_512829 := by
    simpa [prefixWord, tailWord_512829, baseEnd_512829] using wordTrace_append hprefix tailTrace_512829
  have hstable : (prefixWord ++ tailWord_512829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512829).length < 2 ^ (prefixWord ++ tailWord_512829).sum := by decide
  have hdescent : baseEnd_512829 < baseStart_512829 := by decide
  rcases family_descends (prefixWord ++ tailWord_512829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512835 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 2, 2, 2]
def baseStart_512835 : Nat := 118140960795 + 512835 * 2 ^ 59
def prefixEnd_512835 : Nat := 4983230072969 + 3 ^ 40 * 512835 * 2
def baseEnd_512835 : Nat := 263330851448606264404021

theorem tailTrace_512835 : CollatzResearch.WordTrace tailWord_512835 prefixEnd_512835 263330851448606264404021 := by
  unfold tailWord_512835
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704629097093855090091959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12469752731395903393394639 18704629097093855090091959)
  ·
    refine ⟨28056943645640782635137939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18704629097093855090091959 28056943645640782635137939)
    ·
      refine ⟨42085415468461173952706909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28056943645640782635137939 42085415468461173952706909)
      ·
        refine ⟨15782030800672940232265091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42085415468461173952706909 15782030800672940232265091)
        ·
          refine ⟨23673046201009410348397637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15782030800672940232265091 23673046201009410348397637)
          ·
            refine ⟨4438696162689264440324557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23673046201009410348397637 4438696162689264440324557)
            ·
              refine ⟨1664511061008474165121709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4438696162689264440324557 1664511061008474165121709)
              ·
                refine ⟨624191647878177811920641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1664511061008474165121709 624191647878177811920641)
                ·
                  refine ⟨468143735908633358940481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624191647878177811920641 468143735908633358940481)
                  ·
                    refine ⟨351107801931475019205361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 468143735908633358940481 351107801931475019205361)
                    ·
                      refine ⟨263330851448606264404021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351107801931475019205361 263330851448606264404021)
                      ·
                        rfl

theorem cell23_512835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_512835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512835 prefixEnd_512835 := by exact prefixLift 512835
  have htrace : WordTrace (prefixWord ++ tailWord_512835) baseStart_512835 baseEnd_512835 := by
    simpa [prefixWord, tailWord_512835, baseEnd_512835] using wordTrace_append hprefix tailTrace_512835
  have hstable : (prefixWord ++ tailWord_512835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512835).length < 2 ^ (prefixWord ++ tailWord_512835).sum := by decide
  have hdescent : baseEnd_512835 < baseStart_512835 := by decide
  rcases family_descends (prefixWord ++ tailWord_512835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512881 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_512881 : Nat := 118140960795 + 512881 * 2 ^ 59
def prefixEnd_512881 : Nat := 4983230072969 + 3 ^ 40 * 512881 * 2
def baseEnd_512881 : Nat := 263354471558713084428809

theorem tailTrace_512881 : CollatzResearch.WordTrace tailWord_512881 prefixEnd_512881 263354471558713084428809 := by
  unfold tailWord_512881
  simp only [CollatzResearch.WordTrace]
  refine ⟨18706306854927204946266497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12470871236618136630844331 18706306854927204946266497)
  ·
    refine ⟨14029730141195403709699873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18706306854927204946266497 14029730141195403709699873)
    ·
      refine ⟨10522297605896552782274905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14029730141195403709699873 10522297605896552782274905)
      ·
        refine ⟨7891723204422414586706179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10522297605896552782274905 7891723204422414586706179)
        ·
          refine ⟨11837584806633621880059269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7891723204422414586706179 11837584806633621880059269)
          ·
            refine ⟨2219547151243804102511113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11837584806633621880059269 2219547151243804102511113)
            ·
              refine ⟨1664660363432853076883335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219547151243804102511113 1664660363432853076883335)
              ·
                refine ⟨2496990545149279615325003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664660363432853076883335 2496990545149279615325003)
                ·
                  refine ⟨3745485817723919422987505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496990545149279615325003 3745485817723919422987505)
                  ·
                    refine ⟨2809114363292939567240629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3745485817723919422987505 2809114363292939567240629)
                    ·
                      refine ⟨263354471558713084428809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2809114363292939567240629 263354471558713084428809)
                      ·
                        rfl

theorem cell23_512881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_512881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512881 prefixEnd_512881 := by exact prefixLift 512881
  have htrace : WordTrace (prefixWord ++ tailWord_512881) baseStart_512881 baseEnd_512881 := by
    simpa [prefixWord, tailWord_512881, baseEnd_512881] using wordTrace_append hprefix tailTrace_512881
  have hstable : (prefixWord ++ tailWord_512881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512881).length < 2 ^ (prefixWord ++ tailWord_512881).sum := by decide
  have hdescent : baseEnd_512881 < baseStart_512881 := by decide
  rcases family_descends (prefixWord ++ tailWord_512881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512891 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 4]
def baseStart_512891 : Nat := 118140960795 + 512891 * 2 ^ 59
def prefixEnd_512891 : Nat := 4983230072969 + 3 ^ 40 * 512891 * 2
def baseEnd_512891 : Nat := 263359606365258045303763

theorem tailTrace_512891 : CollatzResearch.WordTrace tailWord_512891 prefixEnd_512891 263359606365258045303763 := by
  unfold tailWord_512891
  simp only [CollatzResearch.WordTrace]
  refine ⟨18706671584890976654130527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12471114389927317769420351 18706671584890976654130527)
  ·
    refine ⟨28060007377336464981195791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18706671584890976654130527 28060007377336464981195791)
    ·
      refine ⟨42090011066004697471793687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28060007377336464981195791 42090011066004697471793687)
      ·
        refine ⟨63135016599007046207690531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42090011066004697471793687 63135016599007046207690531)
        ·
          refine ⟨94702524898510569311535797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63135016599007046207690531 94702524898510569311535797)
          ·
            refine ⟨8878361709235365872956481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94702524898510569311535797 8878361709235365872956481)
            ·
              refine ⟨6658771281926524404717361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878361709235365872956481 6658771281926524404717361)
              ·
                refine ⟨4994078461444893303538021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658771281926524404717361 4994078461444893303538021)
                ·
                  refine ⟨936389711520917494413379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4994078461444893303538021 936389711520917494413379)
                  ·
                    refine ⟨1404584567281376241620069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936389711520917494413379 1404584567281376241620069)
                    ·
                      refine ⟨263359606365258045303763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1404584567281376241620069 263359606365258045303763)
                      ·
                        rfl

theorem cell23_512891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 4].length) (baseStart_512891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512891 prefixEnd_512891 := by exact prefixLift 512891
  have htrace : WordTrace (prefixWord ++ tailWord_512891) baseStart_512891 baseEnd_512891 := by
    simpa [prefixWord, tailWord_512891, baseEnd_512891] using wordTrace_append hprefix tailTrace_512891
  have hstable : (prefixWord ++ tailWord_512891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512891).length < 2 ^ (prefixWord ++ tailWord_512891).sum := by decide
  have hdescent : baseEnd_512891 < baseStart_512891 := by decide
  rcases family_descends (prefixWord ++ tailWord_512891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512908 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_512908 : Nat := 118140960795 + 512908 * 2 ^ 59
def prefixEnd_512908 : Nat := 4983230072969 + 3 ^ 40 * 512908 * 2
def baseEnd_512908 : Nat := 263368335536384478791185

theorem tailTrace_512908 : CollatzResearch.WordTrace tailWord_512908 prefixEnd_512908 263368335536384478791185 := by
  unfold tailWord_512908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353645812914694278749689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12471527750552925704999585 9353645812914694278749689)
  ·
    refine ⟨7015234359686020709062267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9353645812914694278749689 7015234359686020709062267)
    ·
      refine ⟨10522851539529031063593401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7015234359686020709062267 10522851539529031063593401)
      ·
        refine ⟨7892138654646773297695051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10522851539529031063593401 7892138654646773297695051)
        ·
          refine ⟨11838207981970159946542577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892138654646773297695051 11838207981970159946542577)
          ·
            refine ⟨8878655986477619959906933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11838207981970159946542577 8878655986477619959906933)
            ·
              refine ⟨832373998732276871241275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8878655986477619959906933 832373998732276871241275)
              ·
                refine ⟨1248560998098415306861913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832373998732276871241275 1248560998098415306861913)
                ·
                  refine ⟨936420748573811480146435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248560998098415306861913 936420748573811480146435)
                  ·
                    refine ⟨1404631122860717220219653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936420748573811480146435 1404631122860717220219653)
                    ·
                      refine ⟨263368335536384478791185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1404631122860717220219653 263368335536384478791185)
                      ·
                        rfl

theorem cell23_512908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_512908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512908 prefixEnd_512908 := by exact prefixLift 512908
  have htrace : WordTrace (prefixWord ++ tailWord_512908) baseStart_512908 baseEnd_512908 := by
    simpa [prefixWord, tailWord_512908, baseEnd_512908] using wordTrace_append hprefix tailTrace_512908
  have hstable : (prefixWord ++ tailWord_512908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512908).length < 2 ^ (prefixWord ++ tailWord_512908).sum := by decide
  have hdescent : baseEnd_512908 < baseStart_512908 := by decide
  rcases family_descends (prefixWord ++ tailWord_512908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512928 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3]
def baseStart_512928 : Nat := 118140960795 + 512928 * 2 ^ 59
def prefixEnd_512928 : Nat := 4983230072969 + 3 ^ 40 * 512928 * 2
def baseEnd_512928 : Nat := 263378605149474400541093

theorem tailTrace_512928 : CollatzResearch.WordTrace tailWord_512928 prefixEnd_512928 263378605149474400541093 := by
  unfold tailWord_512928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354010542878465986613719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12472014057171287982151625 9354010542878465986613719)
  ·
    refine ⟨14031015814317698979920579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9354010542878465986613719 14031015814317698979920579)
    ·
      refine ⟨21046523721476548469880869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14031015814317698979920579 21046523721476548469880869)
      ·
        refine ⟨3946223197776852838102663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21046523721476548469880869 3946223197776852838102663)
        ·
          refine ⟨5919334796665279257153995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946223197776852838102663 5919334796665279257153995)
          ·
            refine ⟨8879002194997918885730993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919334796665279257153995 8879002194997918885730993)
            ·
              refine ⟨6659251646248439164298245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8879002194997918885730993 6659251646248439164298245)
              ·
                refine ⟨1248609683671582343305921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6659251646248439164298245 1248609683671582343305921)
                ·
                  refine ⟨936457262753686757479441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248609683671582343305921 936457262753686757479441)
                  ·
                    refine ⟨702342947065265068109581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 936457262753686757479441 702342947065265068109581)
                    ·
                      refine ⟨263378605149474400541093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702342947065265068109581 263378605149474400541093)
                      ·
                        rfl

theorem cell23_512928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_512928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512928 prefixEnd_512928 := by exact prefixLift 512928
  have htrace : WordTrace (prefixWord ++ tailWord_512928) baseStart_512928 baseEnd_512928 := by
    simpa [prefixWord, tailWord_512928, baseEnd_512928] using wordTrace_append hprefix tailTrace_512928
  have hstable : (prefixWord ++ tailWord_512928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512928).length < 2 ^ (prefixWord ++ tailWord_512928).sum := by decide
  have hdescent : baseEnd_512928 < baseStart_512928 := by decide
  rcases family_descends (prefixWord ++ tailWord_512928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512958 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_512958 : Nat := 118140960795 + 512958 * 2 ^ 59
def prefixEnd_512958 : Nat := 4983230072969 + 3 ^ 40 * 512958 * 2
def baseEnd_512958 : Nat := 263394009569109283165955

theorem tailTrace_512958 : CollatzResearch.WordTrace tailWord_512958 prefixEnd_512958 263394009569109283165955 := by
  unfold tailWord_512958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338639409456030887102441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12472743517098831397879685 2338639409456030887102441)
  ·
    refine ⟨1753979557092023165326831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2338639409456030887102441 1753979557092023165326831)
    ·
      refine ⟨2630969335638034747990247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753979557092023165326831 2630969335638034747990247)
      ·
        refine ⟨3946454003457052121985371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630969335638034747990247 3946454003457052121985371)
        ·
          refine ⟨5919681005185578182978057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946454003457052121985371 5919681005185578182978057)
          ·
            refine ⟨4439760753889183637233543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5919681005185578182978057 4439760753889183637233543)
            ·
              refine ⟨6659641130833775455850315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439760753889183637233543 6659641130833775455850315)
              ·
                refine ⟨9989461696250663183775473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659641130833775455850315 9989461696250663183775473)
                ·
                  refine ⟨7492096272187997387831605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9989461696250663183775473 7492096272187997387831605)
                  ·
                    refine ⟨702384025517624755109213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7492096272187997387831605 702384025517624755109213)
                    ·
                      refine ⟨263394009569109283165955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702384025517624755109213 263394009569109283165955)
                      ·
                        rfl

theorem cell23_512958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_512958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512958 prefixEnd_512958 := by exact prefixLift 512958
  have htrace : WordTrace (prefixWord ++ tailWord_512958) baseStart_512958 baseEnd_512958 := by
    simpa [prefixWord, tailWord_512958, baseEnd_512958] using wordTrace_append hprefix tailTrace_512958
  have hstable : (prefixWord ++ tailWord_512958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512958).length < 2 ^ (prefixWord ++ tailWord_512958).sum := by decide
  have hdescent : baseEnd_512958 < baseStart_512958 := by decide
  rcases family_descends (prefixWord ++ tailWord_512958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512985 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 4, 3, 2]
def baseStart_512985 : Nat := 118140960795 + 512985 * 2 ^ 59
def prefixEnd_512985 : Nat := 4983230072969 + 3 ^ 40 * 512985 * 2
def baseEnd_512985 : Nat := 263407873546780677528331

theorem tailTrace_512985 : CollatzResearch.WordTrace tailWord_512985 prefixEnd_512985 263407873546780677528331 := by
  unfold tailWord_512985
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710100046550430708052409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12473400031033620472034939 18710100046550430708052409)
  ·
    refine ⟨14032575034912823031039307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18710100046550430708052409 14032575034912823031039307)
    ·
      refine ⟨21048862552369234546558961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14032575034912823031039307 21048862552369234546558961)
      ·
        refine ⟨15786646914276925909919221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21048862552369234546558961 15786646914276925909919221)
        ·
          refine ⟨1479998148213461804054927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15786646914276925909919221 1479998148213461804054927)
          ·
            refine ⟨2219997222320192706082391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479998148213461804054927 2219997222320192706082391)
            ·
              refine ⟨3329995833480289059123587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219997222320192706082391 3329995833480289059123587)
              ·
                refine ⟨4994993750220433588685381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329995833480289059123587 4994993750220433588685381)
                ·
                  refine ⟨936561328166331297878509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4994993750220433588685381 936561328166331297878509)
                  ·
                    refine ⟨351210498062374236704441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 936561328166331297878509 351210498062374236704441)
                    ·
                      refine ⟨263407873546780677528331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351210498062374236704441 263407873546780677528331)
                      ·
                        rfl

theorem cell23_512985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_512985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_512985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_512985 prefixEnd_512985 := by exact prefixLift 512985
  have htrace : WordTrace (prefixWord ++ tailWord_512985) baseStart_512985 baseEnd_512985 := by
    simpa [prefixWord, tailWord_512985, baseEnd_512985] using wordTrace_append hprefix tailTrace_512985
  have hstable : (prefixWord ++ tailWord_512985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512985).length < 2 ^ (prefixWord ++ tailWord_512985).sum := by decide
  have hdescent : baseEnd_512985 < baseStart_512985 := by decide
  rcases family_descends (prefixWord ++ tailWord_512985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513032 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_513032 : Nat := 118140960795 + 513032 * 2 ^ 59
def prefixEnd_513032 : Nat := 4983230072969 + 3 ^ 40 * 513032 * 2
def baseEnd_513032 : Nat := 263432007137541993640615

theorem tailTrace_513032 : CollatzResearch.WordTrace tailWord_513032 prefixEnd_513032 263432007137541993640615 := by
  unfold tailWord_513032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355907138690078867506675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12474542851586771823342233 9355907138690078867506675)
  ·
    refine ⟨14033860708035118301260013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9355907138690078867506675 14033860708035118301260013)
    ·
      refine ⟨5262697765513169362972505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14033860708035118301260013 5262697765513169362972505)
      ·
        refine ⟨3947023324134877022229379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5262697765513169362972505 3947023324134877022229379)
        ·
          refine ⟨5920534986202315533344069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947023324134877022229379 5920534986202315533344069)
          ·
            refine ⟨1110100309912934162502013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5920534986202315533344069 1110100309912934162502013)
            ·
              refine ⟨416287616217350310938255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1110100309912934162502013 416287616217350310938255)
              ·
                refine ⟨624431424326025466407383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416287616217350310938255 624431424326025466407383)
                ·
                  refine ⟨936647136489038199611075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624431424326025466407383 936647136489038199611075)
                  ·
                    refine ⟨1404970704733557299416613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936647136489038199611075 1404970704733557299416613)
                    ·
                      refine ⟨263432007137541993640615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1404970704733557299416613 263432007137541993640615)
                      ·
                        rfl

theorem cell23_513032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_513032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513032 prefixEnd_513032 := by exact prefixLift 513032
  have htrace : WordTrace (prefixWord ++ tailWord_513032) baseStart_513032 baseEnd_513032 := by
    simpa [prefixWord, tailWord_513032, baseEnd_513032] using wordTrace_append hprefix tailTrace_513032
  have hstable : (prefixWord ++ tailWord_513032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513032).length < 2 ^ (prefixWord ++ tailWord_513032).sum := by decide
  have hdescent : baseEnd_513032 < baseStart_513032 := by decide
  rcases family_descends (prefixWord ++ tailWord_513032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513035 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 5]
def baseStart_513035 : Nat := 118140960795 + 513035 * 2 ^ 59
def prefixEnd_513035 : Nat := 4983230072969 + 3 ^ 40 * 513035 * 2
def baseEnd_513035 : Nat := 263433547579505481903101

theorem tailTrace_513035 : CollatzResearch.WordTrace tailWord_513035 prefixEnd_513035 263433547579505481903101 := by
  unfold tailWord_513035
  simp only [CollatzResearch.WordTrace]
  refine ⟨18711923696369289247372559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12474615797579526164915039 18711923696369289247372559)
  ·
    refine ⟨28067885544553933871058839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18711923696369289247372559 28067885544553933871058839)
    ·
      refine ⟨42101828316830900806588259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28067885544553933871058839 42101828316830900806588259)
      ·
        refine ⟨63152742475246351209882389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42101828316830900806588259 63152742475246351209882389)
        ·
          refine ⟨2960284803527172712963237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63152742475246351209882389 2960284803527172712963237)
          ·
            refine ⟨555053400661344883680607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2960284803527172712963237 555053400661344883680607)
            ·
              refine ⟨832580100992017325520911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555053400661344883680607 832580100992017325520911)
              ·
                refine ⟨1248870151488025988281367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832580100992017325520911 1248870151488025988281367)
                ·
                  refine ⟨1873305227232038982422051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1248870151488025988281367 1873305227232038982422051)
                  ·
                    refine ⟨2809957840848058473633077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1873305227232038982422051 2809957840848058473633077)
                    ·
                      refine ⟨263433547579505481903101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2809957840848058473633077 263433547579505481903101)
                      ·
                        rfl

theorem cell23_513035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 5].length) (baseStart_513035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513035 prefixEnd_513035 := by exact prefixLift 513035
  have htrace : WordTrace (prefixWord ++ tailWord_513035) baseStart_513035 baseEnd_513035 := by
    simpa [prefixWord, tailWord_513035, baseEnd_513035] using wordTrace_append hprefix tailTrace_513035
  have hstable : (prefixWord ++ tailWord_513035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513035).length < 2 ^ (prefixWord ++ tailWord_513035).sum := by decide
  have hdescent : baseEnd_513035 < baseStart_513035 := by decide
  rcases family_descends (prefixWord ++ tailWord_513035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513086 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_513086 : Nat := 118140960795 + 513086 * 2 ^ 59
def prefixEnd_513086 : Nat := 4983230072969 + 3 ^ 40 * 513086 * 2
def baseEnd_513086 : Nat := 263459735092884782365367

theorem tailTrace_513086 : CollatzResearch.WordTrace tailWord_513086 prefixEnd_513086 263459735092884782365367 := by
  unfold tailWord_513086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2339222977398065619684889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12475855879456349971652741 2339222977398065619684889)
  ·
    refine ⟨1754417233048549214763667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2339222977398065619684889 1754417233048549214763667)
    ·
      refine ⟨2631625849572823822145501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754417233048549214763667 2631625849572823822145501)
      ·
        refine ⟨986859693589808933304563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2631625849572823822145501 986859693589808933304563)
        ·
          refine ⟨1480289540384713399956845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986859693589808933304563 1480289540384713399956845)
          ·
            refine ⟨555108577644267524983817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1480289540384713399956845 555108577644267524983817)
            ·
              refine ⟨416331433233200643737863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555108577644267524983817 416331433233200643737863)
              ·
                refine ⟨624497149849800965606795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416331433233200643737863 624497149849800965606795)
                ·
                  refine ⟨936745724774701448410193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624497149849800965606795 936745724774701448410193)
                  ·
                    refine ⟨702559293581026086307645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 936745724774701448410193 702559293581026086307645)
                    ·
                      refine ⟨263459735092884782365367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702559293581026086307645 263459735092884782365367)
                      ·
                        rfl

theorem cell23_513086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_513086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513086 prefixEnd_513086 := by exact prefixLift 513086
  have htrace : WordTrace (prefixWord ++ tailWord_513086) baseStart_513086 baseEnd_513086 := by
    simpa [prefixWord, tailWord_513086, baseEnd_513086] using wordTrace_append hprefix tailTrace_513086
  have hstable : (prefixWord ++ tailWord_513086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513086).length < 2 ^ (prefixWord ++ tailWord_513086).sum := by decide
  have hdescent : baseEnd_513086 < baseStart_513086 := by decide
  rcases family_descends (prefixWord ++ tailWord_513086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513098 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_513098 : Nat := 118140960795 + 513098 * 2 ^ 59
def prefixEnd_513098 : Nat := 4983230072969 + 3 ^ 40 * 513098 * 2
def baseEnd_513098 : Nat := 87821965620246245138437

theorem tailTrace_513098 : CollatzResearch.WordTrace tailWord_513098 prefixEnd_513098 87821965620246245138437 := by
  unfold tailWord_513098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678555373785262751728987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12476147663427367337943965 4678555373785262751728987)
  ·
    refine ⟨7017833060677894127593481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4678555373785262751728987 7017833060677894127593481)
    ·
      refine ⟨5263374795508420595695111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7017833060677894127593481 5263374795508420595695111)
      ·
        refine ⟨7895062193262630893542667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263374795508420595695111 7895062193262630893542667)
        ·
          refine ⟨11842593289893946340314001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895062193262630893542667 11842593289893946340314001)
          ·
            refine ⟨8881944967420459755235501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11842593289893946340314001 8881944967420459755235501)
            ·
              refine ⟨3330729362782672408213313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8881944967420459755235501 3330729362782672408213313)
              ·
                refine ⟨2498047022087004306159985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330729362782672408213313 2498047022087004306159985)
                ·
                  refine ⟨1873535266565253229619989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2498047022087004306159985 1873535266565253229619989)
                  ·
                    refine ⟨87821965620246245138437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1873535266565253229619989 87821965620246245138437)
                    ·
                      rfl

theorem cell23_513098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_513098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513098 prefixEnd_513098 := by exact prefixLift 513098
  have htrace : WordTrace (prefixWord ++ tailWord_513098) baseStart_513098 baseEnd_513098 := by
    simpa [prefixWord, tailWord_513098, baseEnd_513098] using wordTrace_append hprefix tailTrace_513098
  have hstable : (prefixWord ++ tailWord_513098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513098).length < 2 ^ (prefixWord ++ tailWord_513098).sum := by decide
  have hdescent : baseEnd_513098 < baseStart_513098 := by decide
  rcases family_descends (prefixWord ++ tailWord_513098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513105 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 3, 4, 2]
def baseStart_513105 : Nat := 118140960795 + 513105 * 2 ^ 59
def prefixEnd_513105 : Nat := 4983230072969 + 3 ^ 40 * 513105 * 2
def baseEnd_513105 : Nat := 263469491225320208027779

theorem tailTrace_513105 : CollatzResearch.WordTrace tailWord_513105 prefixEnd_513105 263469491225320208027779 := by
  unfold tailWord_513105
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714476806115691202420769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12476317870743794134947179 18714476806115691202420769)
  ·
    refine ⟨14035857604586768401815577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18714476806115691202420769 14035857604586768401815577)
    ·
      refine ⟨10526893203440076301361683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14035857604586768401815577 10526893203440076301361683)
      ·
        refine ⟨15790339805160114452042525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526893203440076301361683 15790339805160114452042525)
        ·
          refine ⟨5921377426935042919515947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15790339805160114452042525 5921377426935042919515947)
          ·
            refine ⟨8882066140402564379273921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921377426935042919515947 8882066140402564379273921)
            ·
              refine ⟨6661549605301923284455441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882066140402564379273921 6661549605301923284455441)
              ·
                refine ⟨4996162203976442463341581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6661549605301923284455441 4996162203976442463341581)
                ·
                  refine ⟨1873560826491165923753093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4996162203976442463341581 1873560826491165923753093)
                  ·
                    refine ⟨351292654967093610703705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1873560826491165923753093 351292654967093610703705)
                    ·
                      refine ⟨263469491225320208027779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351292654967093610703705 263469491225320208027779)
                      ·
                        rfl

theorem cell23_513105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_513105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513105 prefixEnd_513105 := by exact prefixLift 513105
  have htrace : WordTrace (prefixWord ++ tailWord_513105) baseStart_513105 baseEnd_513105 := by
    simpa [prefixWord, tailWord_513105, baseEnd_513105] using wordTrace_append hprefix tailTrace_513105
  have hstable : (prefixWord ++ tailWord_513105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513105).length < 2 ^ (prefixWord ++ tailWord_513105).sum := by decide
  have hdescent : baseEnd_513105 < baseStart_513105 := by decide
  rcases family_descends (prefixWord ++ tailWord_513105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513212 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_513212 : Nat := 118140960795 + 513212 * 2 ^ 59
def prefixEnd_513212 : Nat := 4983230072969 + 3 ^ 40 * 513212 * 2
def baseEnd_513212 : Nat := 263524433655351289389787

theorem tailTrace_513212 : CollatzResearch.WordTrace tailWord_513212 prefixEnd_513212 263524433655351289389787 := by
  unfold tailWord_513212
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359189708364024238282945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12478919611152032317710593 9359189708364024238282945)
  ·
    refine ⟨7019392281273018178712209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9359189708364024238282945 7019392281273018178712209)
    ·
      refine ⟨5264544210954763634034157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7019392281273018178712209 5264544210954763634034157)
      ·
        refine ⟨1974204079108036362762809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5264544210954763634034157 1974204079108036362762809)
        ·
          refine ⟨1480653059331027272072107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974204079108036362762809 1480653059331027272072107)
          ·
            refine ⟨2220979588996540908108161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480653059331027272072107 2220979588996540908108161)
            ·
              refine ⟨1665734691747405681081121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220979588996540908108161 1665734691747405681081121)
              ·
                refine ⟨1249301018810554260810841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665734691747405681081121 1249301018810554260810841)
                ·
                  refine ⟨936975764107915695608131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1249301018810554260810841 936975764107915695608131)
                  ·
                    refine ⟨1405463646161873543412197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936975764107915695608131 1405463646161873543412197)
                    ·
                      refine ⟨263524433655351289389787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1405463646161873543412197 263524433655351289389787)
                      ·
                        rfl

theorem cell23_513212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_513212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513212 prefixEnd_513212 := by exact prefixLift 513212
  have htrace : WordTrace (prefixWord ++ tailWord_513212) baseStart_513212 baseEnd_513212 := by
    simpa [prefixWord, tailWord_513212, baseEnd_513212] using wordTrace_append hprefix tailTrace_513212
  have hstable : (prefixWord ++ tailWord_513212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513212).length < 2 ^ (prefixWord ++ tailWord_513212).sum := by decide
  have hdescent : baseEnd_513212 < baseStart_513212 := by decide
  rcases family_descends (prefixWord ++ tailWord_513212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513249 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_513249 : Nat := 118140960795 + 513249 * 2 ^ 59
def prefixEnd_513249 : Nat := 4983230072969 + 3 ^ 40 * 513249 * 2
def baseEnd_513249 : Nat := 263543432439567644627117

theorem tailTrace_513249 : CollatzResearch.WordTrace tailWord_513249 prefixEnd_513249 263543432439567644627117 := by
  unfold tailWord_513249
  simp only [CollatzResearch.WordTrace]
  refine ⟨18719728917594003795662801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12479819278396002530441867 18719728917594003795662801)
  ·
    refine ⟨14039796688195502846747101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18719728917594003795662801 14039796688195502846747101)
    ·
      refine ⟨5264923758073313567530163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14039796688195502846747101 5264923758073313567530163)
      ·
        refine ⟨7897385637109970351295245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5264923758073313567530163 7897385637109970351295245)
        ·
          refine ⟨2961519613916238881735717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7897385637109970351295245 2961519613916238881735717)
          ·
            refine ⟨555284927609294790325447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2961519613916238881735717 555284927609294790325447)
            ·
              refine ⟨832927391413942185488171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555284927609294790325447 832927391413942185488171)
              ·
                refine ⟨1249391087120913278232257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832927391413942185488171 1249391087120913278232257)
                ·
                  refine ⟨937043315340684958674193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1249391087120913278232257 937043315340684958674193)
                  ·
                    refine ⟨702782486505513719005645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 937043315340684958674193 702782486505513719005645)
                    ·
                      refine ⟨263543432439567644627117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702782486505513719005645 263543432439567644627117)
                      ·
                        rfl

theorem cell23_513249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_513249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513249 prefixEnd_513249 := by exact prefixLift 513249
  have htrace : WordTrace (prefixWord ++ tailWord_513249) baseStart_513249 baseEnd_513249 := by
    simpa [prefixWord, tailWord_513249, baseEnd_513249] using wordTrace_append hprefix tailTrace_513249
  have hstable : (prefixWord ++ tailWord_513249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513249).length < 2 ^ (prefixWord ++ tailWord_513249).sum := by decide
  have hdescent : baseEnd_513249 < baseStart_513249 := by decide
  rcases family_descends (prefixWord ++ tailWord_513249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513279 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 3]
def baseStart_513279 : Nat := 118140960795 + 513279 * 2 ^ 59
def prefixEnd_513279 : Nat := 4983230072969 + 3 ^ 40 * 513279 * 2
def baseEnd_513279 : Nat := 263558836859202527251979

theorem tailTrace_513279 : CollatzResearch.WordTrace tailWord_513279 prefixEnd_513279 263558836859202527251979 := by
  unfold tailWord_513279
  simp only [CollatzResearch.WordTrace]
  refine ⟨18720823107485318919254891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12480548738323545946169927 18720823107485318919254891)
  ·
    refine ⟨28081234661227978378882337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18720823107485318919254891 28081234661227978378882337)
    ·
      refine ⟨21060925995920983784161753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28081234661227978378882337 21060925995920983784161753)
      ·
        refine ⟨15795694496940737838121315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21060925995920983784161753 15795694496940737838121315)
        ·
          refine ⟨23693541745411106757181973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15795694496940737838121315 23693541745411106757181973)
          ·
            refine ⟨1110634769316145629242905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23693541745411106757181973 1110634769316145629242905)
            ·
              refine ⟨832976076987109221932179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110634769316145629242905 832976076987109221932179)
              ·
                refine ⟨1249464115480663832898269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832976076987109221932179 1249464115480663832898269)
                ·
                  refine ⟨468549043305248937336851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249464115480663832898269 468549043305248937336851)
                  ·
                    refine ⟨702823564957873406005277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 468549043305248937336851 702823564957873406005277)
                    ·
                      refine ⟨263558836859202527251979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702823564957873406005277 263558836859202527251979)
                      ·
                        rfl

theorem cell23_513279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_513279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513279 prefixEnd_513279 := by exact prefixLift 513279
  have htrace : WordTrace (prefixWord ++ tailWord_513279) baseStart_513279 baseEnd_513279 := by
    simpa [prefixWord, tailWord_513279, baseEnd_513279] using wordTrace_append hprefix tailTrace_513279
  have hstable : (prefixWord ++ tailWord_513279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513279).length < 2 ^ (prefixWord ++ tailWord_513279).sum := by decide
  have hdescent : baseEnd_513279 < baseStart_513279 := by decide
  rcases family_descends (prefixWord ++ tailWord_513279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513305 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 3]
def baseStart_513305 : Nat := 118140960795 + 513305 * 2 ^ 59
def prefixEnd_513305 : Nat := 4983230072969 + 3 ^ 40 * 513305 * 2
def baseEnd_513305 : Nat := 263572187356219425526859

theorem tailTrace_513305 : CollatzResearch.WordTrace tailWord_513305 prefixEnd_513305 263572187356219425526859 := by
  unfold tailWord_513305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18721771405391125359701369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12481180936927416906467579 18721771405391125359701369)
  ·
    refine ⟨14041328554043344019776027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18721771405391125359701369 14041328554043344019776027)
    ·
      refine ⟨21061992831065016029664041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041328554043344019776027 21061992831065016029664041)
      ·
        refine ⟨15796494623298762022248031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21061992831065016029664041 15796494623298762022248031)
        ·
          refine ⟨23694741934948143033372047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15796494623298762022248031 23694741934948143033372047)
          ·
            refine ⟨35542112902422214550058071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23694741934948143033372047 35542112902422214550058071)
            ·
              refine ⟨53313169353633321825087107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35542112902422214550058071 53313169353633321825087107)
              ·
                refine ⟨79969754030449982737630661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53313169353633321825087107 79969754030449982737630661)
                ·
                  refine ⟨14994328880709371763305749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79969754030449982737630661 14994328880709371763305749)
                  ·
                    refine ⟨702859166283251801404957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14994328880709371763305749 702859166283251801404957)
                    ·
                      refine ⟨263572187356219425526859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702859166283251801404957 263572187356219425526859)
                      ·
                        rfl

theorem cell23_513305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_513305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513305 prefixEnd_513305 := by exact prefixLift 513305
  have htrace : WordTrace (prefixWord ++ tailWord_513305) baseStart_513305 baseEnd_513305 := by
    simpa [prefixWord, tailWord_513305, baseEnd_513305] using wordTrace_append hprefix tailTrace_513305
  have hstable : (prefixWord ++ tailWord_513305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513305).length < 2 ^ (prefixWord ++ tailWord_513305).sum := by decide
  have hdescent : baseEnd_513305 < baseStart_513305 := by decide
  rcases family_descends (prefixWord ++ tailWord_513305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513332 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_513332 : Nat := 118140960795 + 513332 * 2 ^ 59
def prefixEnd_513332 : Nat := 4983230072969 + 3 ^ 40 * 513332 * 2
def baseEnd_513332 : Nat := 263586051333890819889235

theorem tailTrace_513332 : CollatzResearch.WordTrace tailWord_513332 prefixEnd_513332 263586051333890819889235 := by
  unfold tailWord_513332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361378088146654485467125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12481837450862205980622833 9361378088146654485467125)
  ·
    refine ⟨877629195763748858012543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9361378088146654485467125 877629195763748858012543)
    ·
      refine ⟨1316443793645623287018815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877629195763748858012543 1316443793645623287018815)
      ·
        refine ⟨1974665690468434930528223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316443793645623287018815 1974665690468434930528223)
        ·
          refine ⟨2961998535702652395792335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974665690468434930528223 2961998535702652395792335)
          ·
            refine ⟨4442997803553978593688503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961998535702652395792335 4442997803553978593688503)
            ·
              refine ⟨6664496705330967890532755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442997803553978593688503 6664496705330967890532755)
              ·
                refine ⟨9996745057996451835799133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664496705330967890532755 9996745057996451835799133)
                ·
                  refine ⟨3748779396748669438424675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9996745057996451835799133 3748779396748669438424675)
                  ·
                    refine ⟨5623169095123004157637013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3748779396748669438424675 5623169095123004157637013)
                    ·
                      refine ⟨263586051333890819889235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5623169095123004157637013 263586051333890819889235)
                      ·
                        rfl

theorem cell23_513332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_513332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513332 prefixEnd_513332 := by exact prefixLift 513332
  have htrace : WordTrace (prefixWord ++ tailWord_513332) baseStart_513332 baseEnd_513332 := by
    simpa [prefixWord, tailWord_513332, baseEnd_513332] using wordTrace_append hprefix tailTrace_513332
  have hstable : (prefixWord ++ tailWord_513332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513332).length < 2 ^ (prefixWord ++ tailWord_513332).sum := by decide
  have hdescent : baseEnd_513332 < baseStart_513332 := by decide
  rcases family_descends (prefixWord ++ tailWord_513332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513342 : List Nat := [4, 2, 1, 2, 1, 1, 4, 8]
def baseStart_513342 : Nat := 118140960795 + 513342 * 2 ^ 59
def prefixEnd_513342 : Nat := 4983230072969 + 3 ^ 40 * 513342 * 2
def baseEnd_513342 : Nat := 9762636523719843732007

theorem tailTrace_513342 : CollatzResearch.WordTrace tailWord_513342 prefixEnd_513342 9762636523719843732007 := by
  unfold tailWord_513342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340390113282135084849785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12482080604171387119198853 2340390113282135084849785)
  ·
    refine ⟨1755292584961601313637339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2340390113282135084849785 1755292584961601313637339)
    ·
      refine ⟨2632938877442401970456009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755292584961601313637339 2632938877442401970456009)
      ·
        refine ⟨1974704158081801477842007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2632938877442401970456009 1974704158081801477842007)
        ·
          refine ⟨2962056237122702216763011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974704158081801477842007 2962056237122702216763011)
          ·
            refine ⟨4443084355684053325144517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962056237122702216763011 4443084355684053325144517)
            ·
              refine ⟨833078316690759998464597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4443084355684053325144517 833078316690759998464597)
              ·
                refine ⟨9762636523719843732007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 833078316690759998464597 9762636523719843732007)
                ·
                  rfl

theorem cell23_513342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_513342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513342 prefixEnd_513342 := by exact prefixLift 513342
  have htrace : WordTrace (prefixWord ++ tailWord_513342) baseStart_513342 baseEnd_513342 := by
    simpa [prefixWord, tailWord_513342, baseEnd_513342] using wordTrace_append hprefix tailTrace_513342
  have hstable : (prefixWord ++ tailWord_513342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513342).length < 2 ^ (prefixWord ++ tailWord_513342).sum := by decide
  have hdescent : baseEnd_513342 < baseStart_513342 := by decide
  rcases family_descends (prefixWord ++ tailWord_513342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513350 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_513350 : Nat := 118140960795 + 513350 * 2 ^ 59
def prefixEnd_513350 : Nat := 4983230072969 + 3 ^ 40 * 513350 * 2
def baseEnd_513350 : Nat := 87865097995223916488051

theorem tailTrace_513350 : CollatzResearch.WordTrace tailWord_513350 prefixEnd_513350 87865097995223916488051 := by
  unfold tailWord_513350
  simp only [CollatzResearch.WordTrace]
  refine ⟨585106646569628063909047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12482275126818732030059669 585106646569628063909047)
  ·
    refine ⟨877659969854442095863571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585106646569628063909047 877659969854442095863571)
    ·
      refine ⟨1316489954781663143795357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877659969854442095863571 1316489954781663143795357)
      ·
        refine ⟨493683733043123678923259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1316489954781663143795357 493683733043123678923259)
        ·
          refine ⟨740525599564685518384889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493683733043123678923259 740525599564685518384889)
          ·
            refine ⟨555394199673514138788667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740525599564685518384889 555394199673514138788667)
            ·
              refine ⟨833091299510271208183001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555394199673514138788667 833091299510271208183001)
              ·
                refine ⟨624818474632703406137251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833091299510271208183001 624818474632703406137251)
                ·
                  refine ⟨937227711949055109205877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624818474632703406137251 937227711949055109205877)
                  ·
                    refine ⟨87865097995223916488051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 937227711949055109205877 87865097995223916488051)
                    ·
                      rfl

theorem cell23_513350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_513350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513350 prefixEnd_513350 := by exact prefixLift 513350
  have htrace : WordTrace (prefixWord ++ tailWord_513350) baseStart_513350 baseEnd_513350 := by
    simpa [prefixWord, tailWord_513350, baseEnd_513350] using wordTrace_append hprefix tailTrace_513350
  have hstable : (prefixWord ++ tailWord_513350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513350).length < 2 ^ (prefixWord ++ tailWord_513350).sum := by decide
  have hdescent : baseEnd_513350 < baseStart_513350 := by decide
  rcases family_descends (prefixWord ++ tailWord_513350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513352 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_513352 : Nat := 118140960795 + 513352 * 2 ^ 59
def prefixEnd_513352 : Nat := 4983230072969 + 3 ^ 40 * 513352 * 2
def baseEnd_513352 : Nat := 263596320946980741639143

theorem tailTrace_513352 : CollatzResearch.WordTrace tailWord_513352 prefixEnd_513352 263596320946980741639143 := by
  unfold tailWord_513352
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361742818110426193331155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12482323757480568257774873 9361742818110426193331155)
  ·
    refine ⟨14042614227165639289996733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9361742818110426193331155 14042614227165639289996733)
    ·
      refine ⟨5265980335187114733748775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14042614227165639289996733 5265980335187114733748775)
      ·
        refine ⟨7898970502780672100623163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265980335187114733748775 7898970502780672100623163)
        ·
          refine ⟨11848455754171008150934745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898970502780672100623163 11848455754171008150934745)
          ·
            refine ⟨8886341815628256113201059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11848455754171008150934745 8886341815628256113201059)
            ·
              refine ⟨13329512723442384169801589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886341815628256113201059 13329512723442384169801589)
              ·
                refine ⟨1249641817822723515918899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13329512723442384169801589 1249641817822723515918899)
                ·
                  refine ⟨1874462726734085273878349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249641817822723515918899 1874462726734085273878349)
                  ·
                    refine ⟨702923522525281977704381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1874462726734085273878349 702923522525281977704381)
                    ·
                      refine ⟨263596320946980741639143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702923522525281977704381 263596320946980741639143)
                      ·
                        rfl

theorem cell23_513352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_513352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513352 prefixEnd_513352 := by exact prefixLift 513352
  have htrace : WordTrace (prefixWord ++ tailWord_513352) baseStart_513352 baseEnd_513352 := by
    simpa [prefixWord, tailWord_513352, baseEnd_513352] using wordTrace_append hprefix tailTrace_513352
  have hstable : (prefixWord ++ tailWord_513352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513352).length < 2 ^ (prefixWord ++ tailWord_513352).sum := by decide
  have hdescent : baseEnd_513352 < baseStart_513352 := by decide
  rcases family_descends (prefixWord ++ tailWord_513352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513356 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_513356 : Nat := 118140960795 + 513356 * 2 ^ 59
def prefixEnd_513356 : Nat := 4983230072969 + 3 ^ 40 * 513356 * 2
def baseEnd_513356 : Nat := 263598374869598725989125

theorem tailTrace_513356 : CollatzResearch.WordTrace tailWord_513356 prefixEnd_513356 263598374869598725989125 := by
  unfold tailWord_513356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361815764103180534903961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12482421018804240713205281 9361815764103180534903961)
  ·
    refine ⟨7021361823077385401177971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9361815764103180534903961 7021361823077385401177971)
    ·
      refine ⟨10532042734616078101766957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7021361823077385401177971 10532042734616078101766957)
      ·
        refine ⟨3949516025481029288162609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10532042734616078101766957 3949516025481029288162609)
        ·
          refine ⟨2962137019110771966121957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949516025481029288162609 2962137019110771966121957)
          ·
            refine ⟨555400691083269743647867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2962137019110771966121957 555400691083269743647867)
            ·
              refine ⟨833101036624904615471801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555400691083269743647867 833101036624904615471801)
              ·
                refine ⟨624825777468678461603851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833101036624904615471801 624825777468678461603851)
                ·
                  refine ⟨937238666203017692405777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624825777468678461603851 937238666203017692405777)
                  ·
                    refine ⟨702928999652263269304333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 937238666203017692405777 702928999652263269304333)
                    ·
                      refine ⟨263598374869598725989125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 702928999652263269304333 263598374869598725989125)
                      ·
                        rfl

theorem cell23_513356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_513356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513356 prefixEnd_513356 := by exact prefixLift 513356
  have htrace : WordTrace (prefixWord ++ tailWord_513356) baseStart_513356 baseEnd_513356 := by
    simpa [prefixWord, tailWord_513356, baseEnd_513356] using wordTrace_append hprefix tailTrace_513356
  have hstable : (prefixWord ++ tailWord_513356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513356).length < 2 ^ (prefixWord ++ tailWord_513356).sum := by decide
  have hdescent : baseEnd_513356 < baseStart_513356 := by decide
  rcases family_descends (prefixWord ++ tailWord_513356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513435 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8]
def baseStart_513435 : Nat := 118140960795 + 513435 * 2 ^ 59
def prefixEnd_513435 : Nat := 4983230072969 + 3 ^ 40 * 513435 * 2
def baseEnd_513435 : Nat := 263638939841303916901261

theorem tailTrace_513435 : CollatzResearch.WordTrace tailWord_513435 prefixEnd_513435 263638939841303916901261 := by
  unfold tailWord_513435
  simp only [CollatzResearch.WordTrace]
  refine ⟨18726512894920157561933759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12484341929946771707955839 18726512894920157561933759)
  ·
    refine ⟨28089769342380236342900639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18726512894920157561933759 28089769342380236342900639)
    ·
      refine ⟨42134654013570354514350959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28089769342380236342900639 42134654013570354514350959)
      ·
        refine ⟨63201981020355531771526439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42134654013570354514350959 63201981020355531771526439)
        ·
          refine ⟨94802971530533297657289659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63201981020355531771526439 94802971530533297657289659)
          ·
            refine ⟨142204457295799946485934489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94802971530533297657289659 142204457295799946485934489)
            ·
              refine ⟨106653342971849959864450867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142204457295799946485934489 106653342971849959864450867)
              ·
                refine ⟨159980014457774939796676301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106653342971849959864450867 159980014457774939796676301)
                ·
                  refine ⟨59992505421665602423753613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159980014457774939796676301 59992505421665602423753613)
                  ·
                    refine ⟨22497189533124600908907605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59992505421665602423753613 22497189533124600908907605)
                    ·
                      refine ⟨263638939841303916901261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22497189533124600908907605 263638939841303916901261)
                      ·
                        rfl

theorem cell23_513435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_513435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513435 prefixEnd_513435 := by exact prefixLift 513435
  have htrace : WordTrace (prefixWord ++ tailWord_513435) baseStart_513435 baseEnd_513435 := by
    simpa [prefixWord, tailWord_513435, baseEnd_513435] using wordTrace_append hprefix tailTrace_513435
  have hstable : (prefixWord ++ tailWord_513435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513435).length < 2 ^ (prefixWord ++ tailWord_513435).sum := by decide
  have hdescent : baseEnd_513435 < baseStart_513435 := by decide
  rcases family_descends (prefixWord ++ tailWord_513435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513569 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 3, 5]
def baseStart_513569 : Nat := 118140960795 + 513569 * 2 ^ 59
def prefixEnd_513569 : Nat := 4983230072969 + 3 ^ 40 * 513569 * 2
def baseEnd_513569 : Nat := 87902582083002130875215

theorem tailTrace_513569 : CollatzResearch.WordTrace tailWord_513569 prefixEnd_513569 87902582083002130875215 := by
  unfold tailWord_513569
  simp only [CollatzResearch.WordTrace]
  refine ⟨18731400276434698447311761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12487600184289798964874507 18731400276434698447311761)
  ·
    refine ⟨14048550207326023835483821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18731400276434698447311761 14048550207326023835483821)
    ·
      refine ⟨5268206327747258938306433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14048550207326023835483821 5268206327747258938306433)
      ·
        refine ⟨3951154745810444203729825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5268206327747258938306433 3951154745810444203729825)
        ·
          refine ⟨2963366059357833152797369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3951154745810444203729825 2963366059357833152797369)
          ·
            refine ⟨2222524544518374864598027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2963366059357833152797369 2222524544518374864598027)
            ·
              refine ⟨3333786816777562296897041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222524544518374864598027 3333786816777562296897041)
              ·
                refine ⟨2500340112583171722672781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333786816777562296897041 2500340112583171722672781)
                ·
                  refine ⟨937627542218689396002293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2500340112583171722672781 937627542218689396002293)
                  ·
                    refine ⟨87902582083002130875215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 937627542218689396002293 87902582083002130875215)
                    ·
                      rfl

theorem cell23_513569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_513569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513569 prefixEnd_513569 := by exact prefixLift 513569
  have htrace : WordTrace (prefixWord ++ tailWord_513569) baseStart_513569 baseEnd_513569 := by
    simpa [prefixWord, tailWord_513569, baseEnd_513569] using wordTrace_append hprefix tailTrace_513569
  have hstable : (prefixWord ++ tailWord_513569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513569).length < 2 ^ (prefixWord ++ tailWord_513569).sum := by decide
  have hdescent : baseEnd_513569 < baseStart_513569 := by decide
  rcases family_descends (prefixWord ++ tailWord_513569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513593 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 2, 3, 2]
def baseStart_513593 : Nat := 118140960795 + 513593 * 2 ^ 59
def prefixEnd_513593 : Nat := 4983230072969 + 3 ^ 40 * 513593 * 2
def baseEnd_513593 : Nat := 263720069784714298725535

theorem tailTrace_513593 : CollatzResearch.WordTrace tailWord_513593 prefixEnd_513593 263720069784714298725535 := by
  unfold tailWord_513593
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732275628347750546185433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12488183752231833697456955 18732275628347750546185433)
  ·
    refine ⟨14049206721260812909639075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18732275628347750546185433 14049206721260812909639075)
    ·
      refine ⟨21073810081891219364458613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049206721260812909639075 21073810081891219364458613)
      ·
        refine ⟨1975669695177301815417995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21073810081891219364458613 1975669695177301815417995)
        ·
          refine ⟨2963504542765952723126993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975669695177301815417995 2963504542765952723126993)
          ·
            refine ⟨2222628407074464542345245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2963504542765952723126993 2222628407074464542345245)
            ·
              refine ⟨833485652652924203379467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2222628407074464542345245 833485652652924203379467)
              ·
                refine ⟨1250228478979386305069201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833485652652924203379467 1250228478979386305069201)
                ·
                  refine ⟨937671359234539728801901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1250228478979386305069201 937671359234539728801901)
                  ·
                    refine ⟨351626759712952398300713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937671359234539728801901 351626759712952398300713)
                    ·
                      refine ⟨263720069784714298725535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351626759712952398300713 263720069784714298725535)
                      ·
                        rfl

theorem cell23_513593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_513593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513593 prefixEnd_513593 := by exact prefixLift 513593
  have htrace : WordTrace (prefixWord ++ tailWord_513593) baseStart_513593 baseEnd_513593 := by
    simpa [prefixWord, tailWord_513593, baseEnd_513593] using wordTrace_append hprefix tailTrace_513593
  have hstable : (prefixWord ++ tailWord_513593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513593).length < 2 ^ (prefixWord ++ tailWord_513593).sum := by decide
  have hdescent : baseEnd_513593 < baseStart_513593 := by decide
  rcases family_descends (prefixWord ++ tailWord_513593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513599 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 1, 6]
def baseStart_513599 : Nat := 118140960795 + 513599 * 2 ^ 59
def prefixEnd_513599 : Nat := 4983230072969 + 3 ^ 40 * 513599 * 2
def baseEnd_513599 : Nat := 87907716889547091750169

theorem tailTrace_513599 : CollatzResearch.WordTrace tailWord_513599 prefixEnd_513599 87907716889547091750169 := by
  unfold tailWord_513599
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732494466326013570903851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12488329644217342380602567 18732494466326013570903851)
  ·
    refine ⟨28098741699489020356355777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18732494466326013570903851 28098741699489020356355777)
    ·
      refine ⟨21074056274616765267266833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28098741699489020356355777 21074056274616765267266833)
      ·
        refine ⟨15805542205962573950450125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21074056274616765267266833 15805542205962573950450125)
        ·
          refine ⟨5927078327235965231418797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15805542205962573950450125 5927078327235965231418797)
          ·
            refine ⟨2222654372713486961782049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5927078327235965231418797 2222654372713486961782049)
            ·
              refine ⟨1666990779535115221336537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222654372713486961782049 1666990779535115221336537)
              ·
                refine ⟨1250243084651336416002403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666990779535115221336537 1250243084651336416002403)
                ·
                  refine ⟨1875364626977004624003605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250243084651336416002403 1875364626977004624003605)
                  ·
                    refine ⟨87907716889547091750169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1875364626977004624003605 87907716889547091750169)
                    ·
                      rfl

theorem cell23_513599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_513599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513599 prefixEnd_513599 := by exact prefixLift 513599
  have htrace : WordTrace (prefixWord ++ tailWord_513599) baseStart_513599 baseEnd_513599 := by
    simpa [prefixWord, tailWord_513599, baseEnd_513599] using wordTrace_append hprefix tailTrace_513599
  have hstable : (prefixWord ++ tailWord_513599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513599).length < 2 ^ (prefixWord ++ tailWord_513599).sum := by decide
  have hdescent : baseEnd_513599 < baseStart_513599 := by decide
  rcases family_descends (prefixWord ++ tailWord_513599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513623 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 3, 2, 2]
def baseStart_513623 : Nat := 118140960795 + 513623 * 2 ^ 59
def prefixEnd_513623 : Nat := 4983230072969 + 3 ^ 40 * 513623 * 2
def baseEnd_513623 : Nat := 263735474204349181350397

theorem tailTrace_513623 : CollatzResearch.WordTrace tailWord_513623 prefixEnd_513623 263735474204349181350397 := by
  unfold tailWord_513623
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733369818239065669777523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12488913212159377113185015 18733369818239065669777523)
  ·
    refine ⟨28100054727358598504666285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18733369818239065669777523 28100054727358598504666285)
    ·
      refine ⟨10537520522759474439249857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28100054727358598504666285 10537520522759474439249857)
      ·
        refine ⟨7903140392069605829437393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10537520522759474439249857 7903140392069605829437393)
        ·
          refine ⟨5927355294052204372078045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7903140392069605829437393 5927355294052204372078045)
          ·
            refine ⟨2222758235269576639529267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5927355294052204372078045 2222758235269576639529267)
            ·
              refine ⟨3334137352904364959293901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222758235269576639529267 3334137352904364959293901)
              ·
                refine ⟨1250301507339136859735213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3334137352904364959293901 1250301507339136859735213)
                ·
                  refine ⟨468863065252176322400705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250301507339136859735213 468863065252176322400705)
                  ·
                    refine ⟨351647298939132241800529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 468863065252176322400705 351647298939132241800529)
                    ·
                      refine ⟨263735474204349181350397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351647298939132241800529 263735474204349181350397)
                      ·
                        rfl

theorem cell23_513623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_513623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513623 prefixEnd_513623 := by exact prefixLift 513623
  have htrace : WordTrace (prefixWord ++ tailWord_513623) baseStart_513623 baseEnd_513623 := by
    simpa [prefixWord, tailWord_513623, baseEnd_513623] using wordTrace_append hprefix tailTrace_513623
  have hstable : (prefixWord ++ tailWord_513623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513623).length < 2 ^ (prefixWord ++ tailWord_513623).sum := by decide
  have hdescent : baseEnd_513623 < baseStart_513623 := by decide
  rcases family_descends (prefixWord ++ tailWord_513623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513633 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 2, 4]
def baseStart_513633 : Nat := 118140960795 + 513633 * 2 ^ 59
def prefixEnd_513633 : Nat := 4983230072969 + 3 ^ 40 * 513633 * 2
def baseEnd_513633 : Nat := 87913536336964714075117

theorem tailTrace_513633 : CollatzResearch.WordTrace tailWord_513633 prefixEnd_513633 87913536336964714075117 := by
  unfold tailWord_513633
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733734548202837377641553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12489156365468558251761035 18733734548202837377641553)
  ·
    refine ⟨14050300911152128033231165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18733734548202837377641553 14050300911152128033231165)
    ·
      refine ⟨5268862841682048012461687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14050300911152128033231165 5268862841682048012461687)
      ·
        refine ⟨7903294262523072018692531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268862841682048012461687 7903294262523072018692531)
        ·
          refine ⟨11854941393784608028038797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903294262523072018692531 11854941393784608028038797)
          ·
            refine ⟨4445603022669228010514549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11854941393784608028038797 4445603022669228010514549)
            ·
              refine ⟨416775283375240125985739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4445603022669228010514549 416775283375240125985739)
              ·
                refine ⟨625162925062860188978609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416775283375240125985739 625162925062860188978609)
                ·
                  refine ⟨468872193797145141733957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625162925062860188978609 468872193797145141733957)
                  ·
                    refine ⟨87913536336964714075117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468872193797145141733957 87913536336964714075117)
                    ·
                      rfl

theorem cell23_513633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_513633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513633 prefixEnd_513633 := by exact prefixLift 513633
  have htrace : WordTrace (prefixWord ++ tailWord_513633) baseStart_513633 baseEnd_513633 := by
    simpa [prefixWord, tailWord_513633, baseEnd_513633] using wordTrace_append hprefix tailTrace_513633
  have hstable : (prefixWord ++ tailWord_513633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513633).length < 2 ^ (prefixWord ++ tailWord_513633).sum := by decide
  have hdescent : baseEnd_513633 < baseStart_513633 := by decide
  rcases family_descends (prefixWord ++ tailWord_513633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513636 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_513636 : Nat := 118140960795 + 513636 * 2 ^ 59
def prefixEnd_513636 : Nat := 4983230072969 + 3 ^ 40 * 513636 * 2
def baseEnd_513636 : Nat := 263742149452857630487837

theorem tailTrace_513636 : CollatzResearch.WordTrace tailWord_513636 prefixEnd_513636 263742149452857630487837 := by
  unfold tailWord_513636
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366921983595984445000381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12489229311461312593333841 9366921983595984445000381)
  ·
    refine ⟨3512595743848494166875143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9366921983595984445000381 3512595743848494166875143)
    ·
      refine ⟨5268893615772741250312715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512595743848494166875143 5268893615772741250312715)
      ·
        refine ⟨7903340423659111875469073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5268893615772741250312715 7903340423659111875469073)
        ·
          refine ⟨5927505317744333906601805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7903340423659111875469073 5927505317744333906601805)
          ·
            refine ⟨2222814494154125214975677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5927505317744333906601805 2222814494154125214975677)
            ·
              refine ⟨833555435307796955615879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2222814494154125214975677 833555435307796955615879)
              ·
                refine ⟨1250333152961695433423819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833555435307796955615879 1250333152961695433423819)
                ·
                  refine ⟨1875499729442543150135729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250333152961695433423819 1875499729442543150135729)
                  ·
                    refine ⟨1406624797081907362601797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875499729442543150135729 1406624797081907362601797)
                    ·
                      refine ⟨263742149452857630487837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1406624797081907362601797 263742149452857630487837)
                      ·
                        rfl

theorem cell23_513636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_513636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513636 prefixEnd_513636 := by exact prefixLift 513636
  have htrace : WordTrace (prefixWord ++ tailWord_513636) baseStart_513636 baseEnd_513636 := by
    simpa [prefixWord, tailWord_513636, baseEnd_513636] using wordTrace_append hprefix tailTrace_513636
  have hstable : (prefixWord ++ tailWord_513636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513636).length < 2 ^ (prefixWord ++ tailWord_513636).sum := by decide
  have hdescent : baseEnd_513636 < baseStart_513636 := by decide
  rcases family_descends (prefixWord ++ tailWord_513636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513640 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_513640 : Nat := 118140960795 + 513640 * 2 ^ 59
def prefixEnd_513640 : Nat := 4983230072969 + 3 ^ 40 * 513640 * 2
def baseEnd_513640 : Nat := 263744203375475614837819

theorem tailTrace_513640 : CollatzResearch.WordTrace tailWord_513640 prefixEnd_513640 263744203375475614837819 := by
  unfold tailWord_513640
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366994929588738786573187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12489326572784985048764249 9366994929588738786573187)
  ·
    refine ⟨14050492394383108179859781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9366994929588738786573187 14050492394383108179859781)
    ·
      refine ⟨2634467323946832783723709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14050492394383108179859781 2634467323946832783723709)
      ·
        refine ⟨987925246480062293896391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2634467323946832783723709 987925246480062293896391)
        ·
          refine ⟨1481887869720093440844587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987925246480062293896391 1481887869720093440844587)
          ·
            refine ⟨2222831804580140161266881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481887869720093440844587 2222831804580140161266881)
            ·
              refine ⟨1667123853435105120950161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222831804580140161266881 1667123853435105120950161)
              ·
                refine ⟨1250342890076328840712621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667123853435105120950161 1250342890076328840712621)
                ·
                  refine ⟨468878583778623315267233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250342890076328840712621 468878583778623315267233)
                  ·
                    refine ⟨351658937833967486450425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 468878583778623315267233 351658937833967486450425)
                    ·
                      refine ⟨263744203375475614837819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351658937833967486450425 263744203375475614837819)
                      ·
                        rfl

theorem cell23_513640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_513640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513640 prefixEnd_513640 := by exact prefixLift 513640
  have htrace : WordTrace (prefixWord ++ tailWord_513640) baseStart_513640 baseEnd_513640 := by
    simpa [prefixWord, tailWord_513640, baseEnd_513640] using wordTrace_append hprefix tailTrace_513640
  have hstable : (prefixWord ++ tailWord_513640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513640).length < 2 ^ (prefixWord ++ tailWord_513640).sum := by decide
  have hdescent : baseEnd_513640 < baseStart_513640 := by decide
  rcases family_descends (prefixWord ++ tailWord_513640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513646 : List Nat := [4, 1, 2, 2, 3, 1, 1, 9]
def baseStart_513646 : Nat := 118140960795 + 513646 * 2 ^ 59
def prefixEnd_513646 : Nat := 4983230072969 + 3 ^ 40 * 513646 * 2
def baseEnd_513646 : Nat := 9768417935533429309733

theorem tailTrace_513646 : CollatzResearch.WordTrace tailWord_513646 prefixEnd_513646 9768417935533429309733 := by
  unfold tailWord_513646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341776087144467574733099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12489472464770493731909861 2341776087144467574733099)
  ·
    refine ⟨3512664130716701362099649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2341776087144467574733099 3512664130716701362099649)
    ·
      refine ⟨2634498098037526021574737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3512664130716701362099649 2634498098037526021574737)
      ·
        refine ⟨1975873573528144516181053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2634498098037526021574737 1975873573528144516181053)
        ·
          refine ⟨740952590073054193567895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1975873573528144516181053 740952590073054193567895)
          ·
            refine ⟨1111428885109581290351843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740952590073054193567895 1111428885109581290351843)
            ·
              refine ⟨1667143327664371935527765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111428885109581290351843 1667143327664371935527765)
              ·
                refine ⟨9768417935533429309733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1667143327664371935527765 9768417935533429309733)
                ·
                  rfl

theorem cell23_513646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_513646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513646 prefixEnd_513646 := by exact prefixLift 513646
  have htrace : WordTrace (prefixWord ++ tailWord_513646) baseStart_513646 baseEnd_513646 := by
    simpa [prefixWord, tailWord_513646, baseEnd_513646] using wordTrace_append hprefix tailTrace_513646
  have hstable : (prefixWord ++ tailWord_513646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513646).length < 2 ^ (prefixWord ++ tailWord_513646).sum := by decide
  have hdescent : baseEnd_513646 < baseStart_513646 := by decide
  rcases family_descends (prefixWord ++ tailWord_513646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513669 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_513669 : Nat := 118140960795 + 513669 * 2 ^ 59
def prefixEnd_513669 : Nat := 4983230072969 + 3 ^ 40 * 513669 * 2
def baseEnd_513669 : Nat := 263759094314456001375185

theorem tailTrace_513669 : CollatzResearch.WordTrace tailWord_513669 prefixEnd_513669 263759094314456001375185 := by
  unfold tailWord_513669
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735047576072415525952061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12490031717381610350634707 18735047576072415525952061)
  ·
    refine ⟨7025642841027155822232023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18735047576072415525952061 7025642841027155822232023)
    ·
      refine ⟨10538464261540733733348035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7025642841027155822232023 10538464261540733733348035)
      ·
        refine ⟨15807696392311100600022053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538464261540733733348035 15807696392311100600022053)
        ·
          refine ⟨2963943073558331362504135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15807696392311100600022053 2963943073558331362504135)
          ·
            refine ⟨4445914610337497043756203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963943073558331362504135 4445914610337497043756203)
            ·
              refine ⟨6668871915506245565634305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445914610337497043756203 6668871915506245565634305)
              ·
                refine ⟨5001653936629684174225729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6668871915506245565634305 5001653936629684174225729)
                ·
                  refine ⟨3751240452472263130669297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5001653936629684174225729 3751240452472263130669297)
                  ·
                    refine ⟨2813430339354197348001973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3751240452472263130669297 2813430339354197348001973)
                    ·
                      refine ⟨263759094314456001375185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2813430339354197348001973 263759094314456001375185)
                      ·
                        rfl

theorem cell23_513669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_513669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513669 prefixEnd_513669 := by exact prefixLift 513669
  have htrace : WordTrace (prefixWord ++ tailWord_513669) baseStart_513669 baseEnd_513669 := by
    simpa [prefixWord, tailWord_513669, baseEnd_513669] using wordTrace_append hprefix tailTrace_513669
  have hstable : (prefixWord ++ tailWord_513669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513669).length < 2 ^ (prefixWord ++ tailWord_513669).sum := by decide
  have hdescent : baseEnd_513669 < baseStart_513669 := by decide
  rcases family_descends (prefixWord ++ tailWord_513669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513674 : List Nat := [3, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_513674 : Nat := 118140960795 + 513674 * 2 ^ 59
def prefixEnd_513674 : Nat := 4983230072969 + 3 ^ 40 * 513674 * 2
def baseEnd_513674 : Nat := 263761661717728481812663

theorem tailTrace_513674 : CollatzResearch.WordTrace tailWord_513674 prefixEnd_513674 263761661717728481812663 := by
  unfold tailWord_513674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4683807485263575344971019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12490153294036200919922717 4683807485263575344971019)
  ·
    refine ⟨7025711227895363017456529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4683807485263575344971019 7025711227895363017456529)
    ·
      refine ⟨5269283420921522263092397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7025711227895363017456529 5269283420921522263092397)
      ·
        refine ⟨1975981282845570848659649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5269283420921522263092397 1975981282845570848659649)
        ·
          refine ⟨1481985962134178136494737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975981282845570848659649 1481985962134178136494737)
          ·
            refine ⟨1111489471600633602371053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481985962134178136494737 1111489471600633602371053)
            ·
              refine ⟨416808551850237600889145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1111489471600633602371053 416808551850237600889145)
              ·
                refine ⟨312606413887678200666859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416808551850237600889145 312606413887678200666859)
                ·
                  refine ⟨468909620831517301000289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312606413887678200666859 468909620831517301000289)
                  ·
                    refine ⟨351682215623637975750217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 468909620831517301000289 351682215623637975750217)
                    ·
                      refine ⟨263761661717728481812663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351682215623637975750217 263761661717728481812663)
                      ·
                        rfl

theorem cell23_513674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_513674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513674 prefixEnd_513674 := by exact prefixLift 513674
  have htrace : WordTrace (prefixWord ++ tailWord_513674) baseStart_513674 baseEnd_513674 := by
    simpa [prefixWord, tailWord_513674, baseEnd_513674] using wordTrace_append hprefix tailTrace_513674
  have hstable : (prefixWord ++ tailWord_513674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513674).length < 2 ^ (prefixWord ++ tailWord_513674).sum := by decide
  have hdescent : baseEnd_513674 < baseStart_513674 := by decide
  rcases family_descends (prefixWord ++ tailWord_513674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513684 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_513684 : Nat := 118140960795 + 513684 * 2 ^ 59
def prefixEnd_513684 : Nat := 4983230072969 + 3 ^ 40 * 513684 * 2
def baseEnd_513684 : Nat := 87922265508091147562539

theorem tailTrace_513684 : CollatzResearch.WordTrace tailWord_513684 prefixEnd_513684 87922265508091147562539 := by
  unfold tailWord_513684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9367797335509036543874053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12490396447345382058498737 9367797335509036543874053)
  ·
    refine ⟨1756462000407944351976385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9367797335509036543874053 1756462000407944351976385)
    ·
      refine ⟨1317346500305958263982289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1756462000407944351976385 1317346500305958263982289)
      ·
        refine ⟨988009875229468697986717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1317346500305958263982289 988009875229468697986717)
        ·
          refine ⟨370503703211050761745019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 988009875229468697986717 370503703211050761745019)
          ·
            refine ⟨555755554816576142617529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370503703211050761745019 555755554816576142617529)
            ·
              refine ⟨416816666112432106963147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555755554816576142617529 416816666112432106963147)
              ·
                refine ⟨625224999168648160444721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416816666112432106963147 625224999168648160444721)
                ·
                  refine ⟨468918749376486120333541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625224999168648160444721 468918749376486120333541)
                  ·
                    refine ⟨87922265508091147562539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468918749376486120333541 87922265508091147562539)
                    ·
                      rfl

theorem cell23_513684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_513684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513684 prefixEnd_513684 := by exact prefixLift 513684
  have htrace : WordTrace (prefixWord ++ tailWord_513684) baseStart_513684 baseEnd_513684 := by
    simpa [prefixWord, tailWord_513684, baseEnd_513684] using wordTrace_append hprefix tailTrace_513684
  have hstable : (prefixWord ++ tailWord_513684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513684).length < 2 ^ (prefixWord ++ tailWord_513684).sum := by decide
  have hdescent : baseEnd_513684 < baseStart_513684 := by decide
  rcases family_descends (prefixWord ++ tailWord_513684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513699 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5]
def baseStart_513699 : Nat := 118140960795 + 513699 * 2 ^ 59
def prefixEnd_513699 : Nat := 4983230072969 + 3 ^ 40 * 513699 * 2
def baseEnd_513699 : Nat := 263774498734090884000047

theorem tailTrace_513699 : CollatzResearch.WordTrace tailWord_513699 prefixEnd_513699 263774498734090884000047 := by
  unfold tailWord_513699
  simp only [CollatzResearch.WordTrace]
  refine ⟨18736141765963730649544151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12490761177309153766362767 18736141765963730649544151)
  ·
    refine ⟨28104212648945595974316227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18736141765963730649544151 28104212648945595974316227)
    ·
      refine ⟨42156318973418393961474341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28104212648945595974316227 42156318973418393961474341)
      ·
        refine ⟨7904309807515948867776439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42156318973418393961474341 7904309807515948867776439)
        ·
          refine ⟨11856464711273923301664659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7904309807515948867776439 11856464711273923301664659)
          ·
            refine ⟨17784697066910884952496989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11856464711273923301664659 17784697066910884952496989)
            ·
              refine ⟨6669261400091581857186371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17784697066910884952496989 6669261400091581857186371)
              ·
                refine ⟨10003892100137372785779557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669261400091581857186371 10003892100137372785779557)
                ·
                  refine ⟨1875729768775757397333667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10003892100137372785779557 1875729768775757397333667)
                  ·
                    refine ⟨2813594653163636096000501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1875729768775757397333667 2813594653163636096000501)
                    ·
                      refine ⟨263774498734090884000047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2813594653163636096000501 263774498734090884000047)
                      ·
                        rfl

theorem cell23_513699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_513699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513699 prefixEnd_513699 := by exact prefixLift 513699
  have htrace : WordTrace (prefixWord ++ tailWord_513699) baseStart_513699 baseEnd_513699 := by
    simpa [prefixWord, tailWord_513699, baseEnd_513699] using wordTrace_append hprefix tailTrace_513699
  have hstable : (prefixWord ++ tailWord_513699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513699).length < 2 ^ (prefixWord ++ tailWord_513699).sum := by decide
  have hdescent : baseEnd_513699 < baseStart_513699 := by decide
  rcases family_descends (prefixWord ++ tailWord_513699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513700 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_513700 : Nat := 118140960795 + 513700 * 2 ^ 59
def prefixEnd_513700 : Nat := 4983230072969 + 3 ^ 40 * 513700 * 2
def baseEnd_513700 : Nat := 263775012214745380087543

theorem tailTrace_513700 : CollatzResearch.WordTrace tailWord_513700 prefixEnd_513700 263775012214745380087543 := by
  unfold tailWord_513700
  simp only [CollatzResearch.WordTrace]
  refine ⟨9368089119480053910165277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12490785492640071880220369 9368089119480053910165277)
  ·
    refine ⟨3513033419805020216311979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9368089119480053910165277 3513033419805020216311979)
    ·
      refine ⟨5269550129707530324467969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3513033419805020216311979 5269550129707530324467969)
      ·
        refine ⟨3952162597280647743350977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5269550129707530324467969 3952162597280647743350977)
        ·
          refine ⟨2964121947960485807513233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3952162597280647743350977 2964121947960485807513233)
          ·
            refine ⟨2223091460970364355634925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964121947960485807513233 2223091460970364355634925)
            ·
              refine ⟨833659297863886633363097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2223091460970364355634925 833659297863886633363097)
              ·
                refine ⟨625244473397914975022323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833659297863886633363097 625244473397914975022323)
                ·
                  refine ⟨937866710096872462533485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625244473397914975022323 937866710096872462533485)
                  ·
                    refine ⟨351700016286327173450057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 937866710096872462533485 351700016286327173450057)
                    ·
                      refine ⟨263775012214745380087543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351700016286327173450057 263775012214745380087543)
                      ·
                        rfl

theorem cell23_513700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_513700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513700 prefixEnd_513700 := by exact prefixLift 513700
  have htrace : WordTrace (prefixWord ++ tailWord_513700) baseStart_513700 baseEnd_513700 := by
    simpa [prefixWord, tailWord_513700, baseEnd_513700] using wordTrace_append hprefix tailTrace_513700
  have hstable : (prefixWord ++ tailWord_513700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513700).length < 2 ^ (prefixWord ++ tailWord_513700).sum := by decide
  have hdescent : baseEnd_513700 < baseStart_513700 := by decide
  rcases family_descends (prefixWord ++ tailWord_513700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513786 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_513786 : Nat := 118140960795 + 513786 * 2 ^ 59
def prefixEnd_513786 : Nat := 4983230072969 + 3 ^ 40 * 513786 * 2
def baseEnd_513786 : Nat := 263819171551032043612147

theorem tailTrace_513786 : CollatzResearch.WordTrace tailWord_513786 prefixEnd_513786 263819171551032043612147 := by
  unfold tailWord_513786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4684828729162136126990303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12492876611099029671974141 4684828729162136126990303)
  ·
    refine ⟨7027243093743204190485455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4684828729162136126990303 7027243093743204190485455)
    ·
      refine ⟨10540864640614806285728183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027243093743204190485455 10540864640614806285728183)
      ·
        refine ⟨15811296960922209428592275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10540864640614806285728183 15811296960922209428592275)
        ·
          refine ⟨23716945441383314142888413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15811296960922209428592275 23716945441383314142888413)
          ·
            refine ⟨8893854540518742803583155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23716945441383314142888413 8893854540518742803583155)
            ·
              refine ⟨13340781810778114205374733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8893854540518742803583155 13340781810778114205374733)
              ·
                refine ⟨5002793179041792827015525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13340781810778114205374733 5002793179041792827015525)
                ·
                  refine ⟨938023721070336155065411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5002793179041792827015525 938023721070336155065411)
                  ·
                    refine ⟨1407035581605504232598117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 938023721070336155065411 1407035581605504232598117)
                    ·
                      refine ⟨263819171551032043612147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1407035581605504232598117 263819171551032043612147)
                      ·
                        rfl

theorem cell23_513786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_513786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513786 prefixEnd_513786 := by exact prefixLift 513786
  have htrace : WordTrace (prefixWord ++ tailWord_513786) baseStart_513786 baseEnd_513786 := by
    simpa [prefixWord, tailWord_513786, baseEnd_513786] using wordTrace_append hprefix tailTrace_513786
  have hstable : (prefixWord ++ tailWord_513786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513786).length < 2 ^ (prefixWord ++ tailWord_513786).sum := by decide
  have hdescent : baseEnd_513786 < baseStart_513786 := by decide
  rcases family_descends (prefixWord ++ tailWord_513786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513803 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 2, 4, 2]
def baseStart_513803 : Nat := 118140960795 + 513803 * 2 ^ 59
def prefixEnd_513803 : Nat := 4983230072969 + 3 ^ 40 * 513803 * 2
def baseEnd_513803 : Nat := 263827900722158477099569

theorem tailTrace_513803 : CollatzResearch.WordTrace tailWord_513803 prefixEnd_513803 263827900722158477099569 := by
  unfold tailWord_513803
  simp only [CollatzResearch.WordTrace]
  refine ⟨18739934957586956411330063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12493289971724637607553375 18739934957586956411330063)
  ·
    refine ⟨28109902436380434616995095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18739934957586956411330063 28109902436380434616995095)
    ·
      refine ⟨42164853654570651925492643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28109902436380434616995095 42164853654570651925492643)
      ·
        refine ⟨63247280481855977888238965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42164853654570651925492643 63247280481855977888238965)
        ·
          refine ⟨5929432545173997927022403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63247280481855977888238965 5929432545173997927022403)
          ·
            refine ⟨8894148817760996890533605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929432545173997927022403 8894148817760996890533605)
            ·
              refine ⟨1667652903330186916975051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8894148817760996890533605 1667652903330186916975051)
              ·
                refine ⟨2501479354995280375462577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667652903330186916975051 2501479354995280375462577)
                ·
                  refine ⟨1876109516246460281596933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2501479354995280375462577 1876109516246460281596933)
                  ·
                    refine ⟨351770534296211302799425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876109516246460281596933 351770534296211302799425)
                    ·
                      refine ⟨263827900722158477099569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351770534296211302799425 263827900722158477099569)
                      ·
                        rfl

theorem cell23_513803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4, 2].length) (baseStart_513803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513803 prefixEnd_513803 := by exact prefixLift 513803
  have htrace : WordTrace (prefixWord ++ tailWord_513803) baseStart_513803 baseEnd_513803 := by
    simpa [prefixWord, tailWord_513803, baseEnd_513803] using wordTrace_append hprefix tailTrace_513803
  have hstable : (prefixWord ++ tailWord_513803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513803).length < 2 ^ (prefixWord ++ tailWord_513803).sum := by decide
  have hdescent : baseEnd_513803 < baseStart_513803 := by decide
  rcases family_descends (prefixWord ++ tailWord_513803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513813 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_513813 : Nat := 118140960795 + 513813 * 2 ^ 59
def prefixEnd_513813 : Nat := 4983230072969 + 3 ^ 40 * 513813 * 2
def baseEnd_513813 : Nat := 87944345176234479324841

theorem tailTrace_513813 : CollatzResearch.WordTrace tailWord_513813 prefixEnd_513813 87944345176234479324841 := by
  unfold tailWord_513813
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740299687550728119194093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12493533125033818746129395 18740299687550728119194093)
  ·
    refine ⟨7027612382831523044697785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18740299687550728119194093 7027612382831523044697785)
    ·
      refine ⟨5270709287123642283523339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7027612382831523044697785 5270709287123642283523339)
      ·
        refine ⟨7906063930685463425285009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270709287123642283523339 7906063930685463425285009)
        ·
          refine ⟨5929547948014097568963757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7906063930685463425285009 5929547948014097568963757)
          ·
            refine ⟨2223580480505286588361409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5929547948014097568963757 2223580480505286588361409)
            ·
              refine ⟨1667685360378964941271057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223580480505286588361409 1667685360378964941271057)
              ·
                refine ⟨1250764020284223705953293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667685360378964941271057 1250764020284223705953293)
                ·
                  refine ⟨469036507606583889732485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250764020284223705953293 469036507606583889732485)
                  ·
                    refine ⟨87944345176234479324841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 469036507606583889732485 87944345176234479324841)
                    ·
                      rfl

theorem cell23_513813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_513813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513813 prefixEnd_513813 := by exact prefixLift 513813
  have htrace : WordTrace (prefixWord ++ tailWord_513813) baseStart_513813 baseEnd_513813 := by
    simpa [prefixWord, tailWord_513813, baseEnd_513813] using wordTrace_append hprefix tailTrace_513813
  have hstable : (prefixWord ++ tailWord_513813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513813).length < 2 ^ (prefixWord ++ tailWord_513813).sum := by decide
  have hdescent : baseEnd_513813 < baseStart_513813 := by decide
  rcases family_descends (prefixWord ++ tailWord_513813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513823 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 3]
def baseStart_513823 : Nat := 118140960795 + 513823 * 2 ^ 59
def prefixEnd_513823 : Nat := 4983230072969 + 3 ^ 40 * 513823 * 2
def baseEnd_513823 : Nat := 263838170335248398849477

theorem tailTrace_513823 : CollatzResearch.WordTrace tailWord_513823 prefixEnd_513823 263838170335248398849477 := by
  unfold tailWord_513823
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740664417514499827058123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12493776278342999884705415 18740664417514499827058123)
  ·
    refine ⟨28110996626271749740587185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18740664417514499827058123 28110996626271749740587185)
    ·
      refine ⟨21083247469703812305440389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28110996626271749740587185 21083247469703812305440389)
      ·
        refine ⟨3953108900569464807270073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21083247469703812305440389 3953108900569464807270073)
        ·
          refine ⟨2964831675427098605452555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953108900569464807270073 2964831675427098605452555)
          ·
            refine ⟨4447247513140647908178833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964831675427098605452555 4447247513140647908178833)
            ·
              refine ⟨3335435634855485931134125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4447247513140647908178833 3335435634855485931134125)
              ·
                refine ⟨1250788363070807224175297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3335435634855485931134125 1250788363070807224175297)
                ·
                  refine ⟨938091272303105418131473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1250788363070807224175297 938091272303105418131473)
                  ·
                    refine ⟨703568454227329063598605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 938091272303105418131473 703568454227329063598605)
                    ·
                      refine ⟨263838170335248398849477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 703568454227329063598605 263838170335248398849477)
                      ·
                        rfl

theorem cell23_513823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_513823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513823 prefixEnd_513823 := by exact prefixLift 513823
  have htrace : WordTrace (prefixWord ++ tailWord_513823) baseStart_513823 baseEnd_513823 := by
    simpa [prefixWord, tailWord_513823, baseEnd_513823] using wordTrace_append hprefix tailTrace_513823
  have hstable : (prefixWord ++ tailWord_513823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513823).length < 2 ^ (prefixWord ++ tailWord_513823).sum := by decide
  have hdescent : baseEnd_513823 < baseStart_513823 := by decide
  rcases family_descends (prefixWord ++ tailWord_513823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513826 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 10]
def baseStart_513826 : Nat := 118140960795 + 513826 * 2 ^ 59
def prefixEnd_513826 : Nat := 4983230072969 + 3 ^ 40 * 513826 * 2
def baseEnd_513826 : Nat := 29315523419690209679107

theorem tailTrace_513826 : CollatzResearch.WordTrace tailWord_513826 prefixEnd_513826 29315523419690209679107 := by
  unfold tailWord_513826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685193459125907834854333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12493849224335754226278221 4685193459125907834854333)
  ·
    refine ⟨1756947547172215438070375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4685193459125907834854333 1756947547172215438070375)
    ·
      refine ⟨2635421320758323157105563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1756947547172215438070375 2635421320758323157105563)
      ·
        refine ⟨3953131981137484735658345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635421320758323157105563 3953131981137484735658345)
        ·
          refine ⟨2964848985853113551743759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953131981137484735658345 2964848985853113551743759)
          ·
            refine ⟨4447273478779670327615639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964848985853113551743759 4447273478779670327615639)
            ·
              refine ⟨6670910218169505491423459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4447273478779670327615639 6670910218169505491423459)
              ·
                refine ⟨10006365327254258237135189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670910218169505491423459 10006365327254258237135189)
                ·
                  refine ⟨29315523419690209679107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10006365327254258237135189 29315523419690209679107)
                  ·
                    rfl

theorem cell23_513826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_513826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513826 prefixEnd_513826 := by exact prefixLift 513826
  have htrace : WordTrace (prefixWord ++ tailWord_513826) baseStart_513826 baseEnd_513826 := by
    simpa [prefixWord, tailWord_513826, baseEnd_513826] using wordTrace_append hprefix tailTrace_513826
  have hstable : (prefixWord ++ tailWord_513826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513826).length < 2 ^ (prefixWord ++ tailWord_513826).sum := by decide
  have hdescent : baseEnd_513826 < baseStart_513826 := by decide
  rcases family_descends (prefixWord ++ tailWord_513826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513863 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_513863 : Nat := 118140960795 + 513863 * 2 ^ 59
def prefixEnd_513863 : Nat := 4983230072969 + 3 ^ 40 * 513863 * 2
def baseEnd_513863 : Nat := 263858709561428242349293

theorem tailTrace_513863 : CollatzResearch.WordTrace tailWord_513863 prefixEnd_513863 263858709561428242349293 := by
  unfold tailWord_513863
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742123337369586658514243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12494748891579724439009495 18742123337369586658514243)
  ·
    refine ⟨28113185006054379987771365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18742123337369586658514243 28113185006054379987771365)
    ·
      refine ⟨5271222188635196247707131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28113185006054379987771365 5271222188635196247707131)
      ·
        refine ⟨7906833282952794371560697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271222188635196247707131 7906833282952794371560697)
        ·
          refine ⟨5930124962214595778670523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7906833282952794371560697 5930124962214595778670523)
          ·
            refine ⟨8895187443321893668005785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930124962214595778670523 8895187443321893668005785)
            ·
              refine ⟨6671390582491420251004339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8895187443321893668005785 6671390582491420251004339)
              ·
                refine ⟨10007085873737130376506509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671390582491420251004339 10007085873737130376506509)
                ·
                  refine ⟨3752657202651423891189941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10007085873737130376506509 3752657202651423891189941)
                  ·
                    refine ⟨351811612748570989799057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3752657202651423891189941 351811612748570989799057)
                    ·
                      refine ⟨263858709561428242349293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351811612748570989799057 263858709561428242349293)
                      ·
                        rfl

theorem cell23_513863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_513863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513863 prefixEnd_513863 := by exact prefixLift 513863
  have htrace : WordTrace (prefixWord ++ tailWord_513863) baseStart_513863 baseEnd_513863 := by
    simpa [prefixWord, tailWord_513863, baseEnd_513863] using wordTrace_append hprefix tailTrace_513863
  have hstable : (prefixWord ++ tailWord_513863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513863).length < 2 ^ (prefixWord ++ tailWord_513863).sum := by decide
  have hdescent : baseEnd_513863 < baseStart_513863 := by decide
  rcases family_descends (prefixWord ++ tailWord_513863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513873 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 3, 5]
def baseStart_513873 : Nat := 118140960795 + 513873 * 2 ^ 59
def prefixEnd_513873 : Nat := 4983230072969 + 3 ^ 40 * 513873 * 2
def baseEnd_513873 : Nat := 87954614789324401074749

theorem tailTrace_513873 : CollatzResearch.WordTrace tailWord_513873 prefixEnd_513873 87954614789324401074749 := by
  unfold tailWord_513873
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742488067333358366378273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12494992044888905577585515 18742488067333358366378273)
  ·
    refine ⟨14056866050500018774783705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18742488067333358366378273 14056866050500018774783705)
    ·
      refine ⟨10542649537875014081087779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14056866050500018774783705 10542649537875014081087779)
      ·
        refine ⟨15813974306812521121631669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10542649537875014081087779 15813974306812521121631669)
        ·
          refine ⟨1482560091263673855152969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15813974306812521121631669 1482560091263673855152969)
          ·
            refine ⟨1111920068447755391364727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1482560091263673855152969 1111920068447755391364727)
            ·
              refine ⟨1667880102671633087047091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111920068447755391364727 1667880102671633087047091)
              ·
                refine ⟨2501820154007449630570637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667880102671633087047091 2501820154007449630570637)
                ·
                  refine ⟨938182557752793611463989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2501820154007449630570637 938182557752793611463989)
                  ·
                    refine ⟨87954614789324401074749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 938182557752793611463989 87954614789324401074749)
                    ·
                      rfl

theorem cell23_513873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_513873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513873 prefixEnd_513873 := by exact prefixLift 513873
  have htrace : WordTrace (prefixWord ++ tailWord_513873) baseStart_513873 baseEnd_513873 := by
    simpa [prefixWord, tailWord_513873, baseEnd_513873] using wordTrace_append hprefix tailTrace_513873
  have hstable : (prefixWord ++ tailWord_513873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513873).length < 2 ^ (prefixWord ++ tailWord_513873).sum := by decide
  have hdescent : baseEnd_513873 < baseStart_513873 := by decide
  rcases family_descends (prefixWord ++ tailWord_513873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513898 : List Nat := [3, 1, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_513898 : Nat := 118140960795 + 513898 * 2 ^ 59
def prefixEnd_513898 : Nat := 4983230072969 + 3 ^ 40 * 513898 * 2
def baseEnd_513898 : Nat := 87958893794778535137211

theorem tailTrace_513898 : CollatzResearch.WordTrace tailWord_513898 prefixEnd_513898 87958893794778535137211 := by
  unfold tailWord_513898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685849973060696909009587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12495599928161858424025565 4685849973060696909009587)
  ·
    refine ⟨7028774959591045363514381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685849973060696909009587 7028774959591045363514381)
    ·
      refine ⟨2635790609846642011317893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7028774959591045363514381 2635790609846642011317893)
      ·
        refine ⟨494210739346245377122105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2635790609846642011317893 494210739346245377122105)
        ·
          refine ⟨370658054509684032841579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494210739346245377122105 370658054509684032841579)
          ·
            refine ⟨555987081764526049262369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370658054509684032841579 555987081764526049262369)
            ·
              refine ⟨416990311323394536946777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555987081764526049262369 416990311323394536946777)
              ·
                refine ⟨312742733492545902710083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416990311323394536946777 312742733492545902710083)
                ·
                  refine ⟨469114100238818854065125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312742733492545902710083 469114100238818854065125)
                  ·
                    refine ⟨87958893794778535137211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 469114100238818854065125 87958893794778535137211)
                    ·
                      rfl

theorem cell23_513898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_513898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513898 prefixEnd_513898 := by exact prefixLift 513898
  have htrace : WordTrace (prefixWord ++ tailWord_513898) baseStart_513898 baseEnd_513898 := by
    simpa [prefixWord, tailWord_513898, baseEnd_513898] using wordTrace_append hprefix tailTrace_513898
  have hstable : (prefixWord ++ tailWord_513898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513898).length < 2 ^ (prefixWord ++ tailWord_513898).sum := by decide
  have hdescent : baseEnd_513898 < baseStart_513898 := by decide
  rcases family_descends (prefixWord ++ tailWord_513898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513913 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 3]
def baseStart_513913 : Nat := 118140960795 + 513913 * 2 ^ 59
def prefixEnd_513913 : Nat := 4983230072969 + 3 ^ 40 * 513913 * 2
def baseEnd_513913 : Nat := 263884383594153046724063

theorem tailTrace_513913 : CollatzResearch.WordTrace tailWord_513913 prefixEnd_513913 263884383594153046724063 := by
  unfold tailWord_513913
  simp only [CollatzResearch.WordTrace]
  refine ⟨18743946987188445197834393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12495964658125630131889595 18743946987188445197834393)
  ·
    refine ⟨14057960240391333898375795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18743946987188445197834393 14057960240391333898375795)
    ·
      refine ⟨21086940360587000847563693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14057960240391333898375795 21086940360587000847563693)
      ·
        refine ⟨7907602635220125317836385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21086940360587000847563693 7907602635220125317836385)
        ·
          refine ⟨5930701976415093988377289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7907602635220125317836385 5930701976415093988377289)
          ·
            refine ⟨4448026482311320491282967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5930701976415093988377289 4448026482311320491282967)
            ·
              refine ⟨6672039723466980736924451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448026482311320491282967 6672039723466980736924451)
              ·
                refine ⟨10008059585200471105386677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672039723466980736924451 10008059585200471105386677)
                ·
                  refine ⟨938255586112544166130001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10008059585200471105386677 938255586112544166130001)
                  ·
                    refine ⟨703691689584408124597501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 938255586112544166130001 703691689584408124597501)
                    ·
                      refine ⟨263884383594153046724063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 703691689584408124597501 263884383594153046724063)
                      ·
                        rfl

theorem cell23_513913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_513913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513913 prefixEnd_513913 := by exact prefixLift 513913
  have htrace : WordTrace (prefixWord ++ tailWord_513913) baseStart_513913 baseEnd_513913 := by
    simpa [prefixWord, tailWord_513913, baseEnd_513913] using wordTrace_append hprefix tailTrace_513913
  have hstable : (prefixWord ++ tailWord_513913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513913).length < 2 ^ (prefixWord ++ tailWord_513913).sum := by decide
  have hdescent : baseEnd_513913 < baseStart_513913 := by decide
  rcases family_descends (prefixWord ++ tailWord_513913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513923 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4]
def baseStart_513923 : Nat := 118140960795 + 513923 * 2 ^ 59
def prefixEnd_513923 : Nat := 4983230072969 + 3 ^ 40 * 513923 * 2
def baseEnd_513923 : Nat := 263889518400698007599017

theorem tailTrace_513923 : CollatzResearch.WordTrace tailWord_513923 prefixEnd_513923 263889518400698007599017 := by
  unfold tailWord_513923
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744311717152216905698423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12496207811434811270465615 18744311717152216905698423)
  ·
    refine ⟨28116467575728325358547635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18744311717152216905698423 28116467575728325358547635)
    ·
      refine ⟨42174701363592488037821453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28116467575728325358547635 42174701363592488037821453)
      ·
        refine ⟨15815513011347183014183045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42174701363592488037821453 15815513011347183014183045)
        ·
          refine ⟨2965408689627596815159321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15815513011347183014183045 2965408689627596815159321)
          ·
            refine ⟨2224056517220697611369491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2965408689627596815159321 2224056517220697611369491)
            ·
              refine ⟨3336084775831046417054237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224056517220697611369491 3336084775831046417054237)
              ·
                refine ⟨1251031790936642406395339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336084775831046417054237 1251031790936642406395339)
                ·
                  refine ⟨1876547686404963609593009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251031790936642406395339 1876547686404963609593009)
                  ·
                    refine ⟨1407410764803722707194757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1876547686404963609593009 1407410764803722707194757)
                    ·
                      refine ⟨263889518400698007599017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1407410764803722707194757 263889518400698007599017)
                      ·
                        rfl

theorem cell23_513923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_513923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513923 prefixEnd_513923 := by exact prefixLift 513923
  have htrace : WordTrace (prefixWord ++ tailWord_513923) baseStart_513923 baseEnd_513923 := by
    simpa [prefixWord, tailWord_513923, baseEnd_513923] using wordTrace_append hprefix tailTrace_513923
  have hstable : (prefixWord ++ tailWord_513923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513923).length < 2 ^ (prefixWord ++ tailWord_513923).sum := by decide
  have hdescent : baseEnd_513923 < baseStart_513923 := by decide
  rcases family_descends (prefixWord ++ tailWord_513923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513940 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_513940 : Nat := 118140960795 + 513940 * 2 ^ 59
def prefixEnd_513940 : Nat := 4983230072969 + 3 ^ 40 * 513940 * 2
def baseEnd_513940 : Nat := 263898247571824441086439

theorem tailTrace_513940 : CollatzResearch.WordTrace tailWord_513940 prefixEnd_513940 263898247571824441086439 := by
  unfold tailWord_513940
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372465879045314404533637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12496621172060419206044849 9372465879045314404533637)
  ·
    refine ⟨1757337352320996450850057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9372465879045314404533637 1757337352320996450850057)
    ·
      refine ⟨1318003014240747338137543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757337352320996450850057 1318003014240747338137543)
      ·
        refine ⟨1977004521361121007206315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318003014240747338137543 1977004521361121007206315)
        ·
          refine ⟨2965506782041681510809473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977004521361121007206315 2965506782041681510809473)
          ·
            refine ⟨2224130086531261133107105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2965506782041681510809473 2224130086531261133107105)
            ·
              refine ⟨1668097564898445849830329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224130086531261133107105 1668097564898445849830329)
              ·
                refine ⟨1251073173673834387372747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668097564898445849830329 1251073173673834387372747)
                ·
                  refine ⟨1876609760510751581059121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251073173673834387372747 1876609760510751581059121)
                  ·
                    refine ⟨1407457320383063685794341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1876609760510751581059121 1407457320383063685794341)
                    ·
                      refine ⟨263898247571824441086439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1407457320383063685794341 263898247571824441086439)
                      ·
                        rfl

theorem cell23_513940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_513940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513940 prefixEnd_513940 := by exact prefixLift 513940
  have htrace : WordTrace (prefixWord ++ tailWord_513940) baseStart_513940 baseEnd_513940 := by
    simpa [prefixWord, tailWord_513940, baseEnd_513940] using wordTrace_append hprefix tailTrace_513940
  have hstable : (prefixWord ++ tailWord_513940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513940).length < 2 ^ (prefixWord ++ tailWord_513940).sum := by decide
  have hdescent : baseEnd_513940 < baseStart_513940 := by decide
  rcases family_descends (prefixWord ++ tailWord_513940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513954 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_513954 : Nat := 118140960795 + 513954 * 2 ^ 59
def prefixEnd_513954 : Nat := 4983230072969 + 3 ^ 40 * 513954 * 2
def baseEnd_513954 : Nat := 87968478766995795437125

theorem tailTrace_513954 : CollatzResearch.WordTrace tailWord_513954 prefixEnd_513954 87968478766995795437125 := by
  unfold tailWord_513954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686360595009977300019229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12496961586693272800051277 4686360595009977300019229)
  ·
    refine ⟨1757385223128741487507211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4686360595009977300019229 1757385223128741487507211)
    ·
      refine ⟨2636077834693112231260817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757385223128741487507211 2636077834693112231260817)
      ·
        refine ⟨1977058376019834173445613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2636077834693112231260817 1977058376019834173445613)
        ·
          refine ⟨741396891007437815042105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1977058376019834173445613 741396891007437815042105)
          ·
            refine ⟨556047668255578361281579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741396891007437815042105 556047668255578361281579)
            ·
              refine ⟨834071502383367541922369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556047668255578361281579 834071502383367541922369)
              ·
                refine ⟨625553626787525656441777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834071502383367541922369 625553626787525656441777)
                ·
                  refine ⟨469165220090644242331333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625553626787525656441777 469165220090644242331333)
                  ·
                    refine ⟨87968478766995795437125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 469165220090644242331333 87968478766995795437125)
                    ·
                      rfl

theorem cell23_513954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_513954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513954 prefixEnd_513954 := by exact prefixLift 513954
  have htrace : WordTrace (prefixWord ++ tailWord_513954) baseStart_513954 baseEnd_513954 := by
    simpa [prefixWord, tailWord_513954, baseEnd_513954] using wordTrace_append hprefix tailTrace_513954
  have hstable : (prefixWord ++ tailWord_513954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513954).length < 2 ^ (prefixWord ++ tailWord_513954).sum := by decide
  have hdescent : baseEnd_513954 < baseStart_513954 := by decide
  rcases family_descends (prefixWord ++ tailWord_513954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513970 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_513970 : Nat := 118140960795 + 513970 * 2 ^ 59
def prefixEnd_513970 : Nat := 4983230072969 + 3 ^ 40 * 513970 * 2
def baseEnd_513970 : Nat := 263913651991459323711301

theorem tailTrace_513970 : CollatzResearch.WordTrace tailWord_513970 prefixEnd_513970 263913651991459323711301 := by
  unfold tailWord_513970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686506486995485983164841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12497350631987962621772909 4686506486995485983164841)
  ·
    refine ⟨3514879865246614487373631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4686506486995485983164841 3514879865246614487373631)
    ·
      refine ⟨5272319797869921731060447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3514879865246614487373631 5272319797869921731060447)
      ·
        refine ⟨7908479696804882596590671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5272319797869921731060447 7908479696804882596590671)
        ·
          refine ⟨11862719545207323894886007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908479696804882596590671 11862719545207323894886007)
          ·
            refine ⟨17794079317810985842329011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11862719545207323894886007 17794079317810985842329011)
            ·
              refine ⟨26691118976716478763493517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17794079317810985842329011 26691118976716478763493517)
              ·
                refine ⟨10009169616268679536310069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26691118976716478763493517 10009169616268679536310069)
                ·
                  refine ⟨938359651525188706529069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10009169616268679536310069 938359651525188706529069)
                  ·
                    refine ⟨351884869321945764948401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938359651525188706529069 351884869321945764948401)
                    ·
                      refine ⟨263913651991459323711301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351884869321945764948401 263913651991459323711301)
                      ·
                        rfl

theorem cell23_513970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_513970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_513970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_513970 prefixEnd_513970 := by exact prefixLift 513970
  have htrace : WordTrace (prefixWord ++ tailWord_513970) baseStart_513970 baseEnd_513970 := by
    simpa [prefixWord, tailWord_513970, baseEnd_513970] using wordTrace_append hprefix tailTrace_513970
  have hstable : (prefixWord ++ tailWord_513970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513970).length < 2 ^ (prefixWord ++ tailWord_513970).sum := by decide
  have hdescent : baseEnd_513970 < baseStart_513970 := by decide
  rcases family_descends (prefixWord ++ tailWord_513970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514000 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 1, 4, 2]
def baseStart_514000 : Nat := 118140960795 + 514000 * 2 ^ 59
def prefixEnd_514000 : Nat := 4983230072969 + 3 ^ 40 * 514000 * 2
def baseEnd_514000 : Nat := 263929056411094206336163

theorem tailTrace_514000 : CollatzResearch.WordTrace tailWord_514000 prefixEnd_514000 263929056411094206336163 := by
  unfold tailWord_514000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9373560068936629528125727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12498080091915506037500969 9373560068936629528125727)
  ·
    refine ⟨14060340103404944292188591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9373560068936629528125727 14060340103404944292188591)
    ·
      refine ⟨21090510155107416438282887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14060340103404944292188591 21090510155107416438282887)
      ·
        refine ⟨31635765232661124657424331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21090510155107416438282887 31635765232661124657424331)
        ·
          refine ⟨47453647848991686986136497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31635765232661124657424331 47453647848991686986136497)
          ·
            refine ⟨35590235886743765239602373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47453647848991686986136497 35590235886743765239602373)
            ·
              refine ⟨6673169228764455982425445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35590235886743765239602373 6673169228764455982425445)
              ·
                refine ⟨1251219230393335496704771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6673169228764455982425445 1251219230393335496704771)
                ·
                  refine ⟨1876828845590003245057157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251219230393335496704771 1876828845590003245057157)
                  ·
                    refine ⟨351905408548125608448217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876828845590003245057157 351905408548125608448217)
                    ·
                      refine ⟨263929056411094206336163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351905408548125608448217 263929056411094206336163)
                      ·
                        rfl

theorem cell23_514000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 4, 2].length) (baseStart_514000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514000 prefixEnd_514000 := by exact prefixLift 514000
  have htrace : WordTrace (prefixWord ++ tailWord_514000) baseStart_514000 baseEnd_514000 := by
    simpa [prefixWord, tailWord_514000, baseEnd_514000] using wordTrace_append hprefix tailTrace_514000
  have hstable : (prefixWord ++ tailWord_514000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514000).length < 2 ^ (prefixWord ++ tailWord_514000).sum := by decide
  have hdescent : baseEnd_514000 < baseStart_514000 := by decide
  rcases family_descends (prefixWord ++ tailWord_514000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514012 : List Nat := [2, 2, 6, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_514012 : Nat := 118140960795 + 514012 * 2 ^ 59
def prefixEnd_514012 : Nat := 4983230072969 + 3 ^ 40 * 514012 * 2
def baseEnd_514012 : Nat := 263935218178948159386109

theorem tailTrace_514012 : CollatzResearch.WordTrace tailWord_514012 prefixEnd_514012 263935218178948159386109 := by
  unfold tailWord_514012
  simp only [CollatzResearch.WordTrace]
  refine ⟨9373778906914892552844145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12498371875886523403792193 9373778906914892552844145)
  ·
    refine ⟨7030334180186169414633109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9373778906914892552844145 7030334180186169414633109)
    ·
      refine ⟨329546914696226691310927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7030334180186169414633109 329546914696226691310927)
      ·
        refine ⟨494320372044340036966391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329546914696226691310927 494320372044340036966391)
        ·
          refine ⟨741480558066510055449587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494320372044340036966391 741480558066510055449587)
          ·
            refine ⟨1112220837099765083174381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741480558066510055449587 1112220837099765083174381)
            ·
              refine ⟨417082813912411906190393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1112220837099765083174381 417082813912411906190393)
              ·
                refine ⟨312812110434308929642795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417082813912411906190393 312812110434308929642795)
                ·
                  refine ⟨469218165651463394464193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312812110434308929642795 469218165651463394464193)
                  ·
                    refine ⟨351913624238597545848145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 469218165651463394464193 351913624238597545848145)
                    ·
                      refine ⟨263935218178948159386109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351913624238597545848145 263935218178948159386109)
                      ·
                        rfl

theorem cell23_514012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_514012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514012 prefixEnd_514012 := by exact prefixLift 514012
  have htrace : WordTrace (prefixWord ++ tailWord_514012) baseStart_514012 baseEnd_514012 := by
    simpa [prefixWord, tailWord_514012, baseEnd_514012] using wordTrace_append hprefix tailTrace_514012
  have hstable : (prefixWord ++ tailWord_514012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514012).length < 2 ^ (prefixWord ++ tailWord_514012).sum := by decide
  have hdescent : baseEnd_514012 < baseStart_514012 := by decide
  rcases family_descends (prefixWord ++ tailWord_514012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514017 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_514017 : Nat := 118140960795 + 514017 * 2 ^ 59
def prefixEnd_514017 : Nat := 4983230072969 + 3 ^ 40 * 514017 * 2
def baseEnd_514017 : Nat := 263937785582220639823585

theorem tailTrace_514017 : CollatzResearch.WordTrace tailWord_514017 prefixEnd_514017 263937785582220639823585 := by
  unfold tailWord_514017
  simp only [CollatzResearch.WordTrace]
  refine ⟨18747740178811670959620305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12498493452541113973080203 18747740178811670959620305)
  ·
    refine ⟨14060805134108753219715229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18747740178811670959620305 14060805134108753219715229)
    ·
      refine ⟨5272801925290782457393211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14060805134108753219715229 5272801925290782457393211)
      ·
        refine ⟨7909202887936173686089817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5272801925290782457393211 7909202887936173686089817)
        ·
          refine ⟨5931902165952130264567363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7909202887936173686089817 5931902165952130264567363)
          ·
            refine ⟨8897853248928195396851045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931902165952130264567363 8897853248928195396851045)
            ·
              refine ⟨1668347484174036636909571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8897853248928195396851045 1668347484174036636909571)
              ·
                refine ⟨2502521226261054955364357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668347484174036636909571 2502521226261054955364357)
                ·
                  refine ⟨469222729923947804130817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2502521226261054955364357 469222729923947804130817)
                  ·
                    refine ⟨351917047442960853098113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 469222729923947804130817 351917047442960853098113)
                    ·
                      refine ⟨263937785582220639823585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351917047442960853098113 263937785582220639823585)
                      ·
                        rfl

theorem cell23_514017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_514017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514017 prefixEnd_514017 := by exact prefixLift 514017
  have htrace : WordTrace (prefixWord ++ tailWord_514017) baseStart_514017 baseEnd_514017 := by
    simpa [prefixWord, tailWord_514017, baseEnd_514017] using wordTrace_append hprefix tailTrace_514017
  have hstable : (prefixWord ++ tailWord_514017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514017).length < 2 ^ (prefixWord ++ tailWord_514017).sum := by decide
  have hdescent : baseEnd_514017 < baseStart_514017 := by decide
  rcases family_descends (prefixWord ++ tailWord_514017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514038 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_514038 : Nat := 118140960795 + 514038 * 2 ^ 59
def prefixEnd_514038 : Nat := 4983230072969 + 3 ^ 40 * 514038 * 2
def baseEnd_514038 : Nat := 263948568675965057660989

theorem tailTrace_514038 : CollatzResearch.WordTrace tailWord_514038 prefixEnd_514038 263948568675965057660989 := by
  unfold tailWord_514038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171781631983474471633423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12499004074490394364089845 1171781631983474471633423)
  ·
    refine ⟨1757672447975211707450135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171781631983474471633423 1757672447975211707450135)
    ·
      refine ⟨2636508671962817561175203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757672447975211707450135 2636508671962817561175203)
      ·
        refine ⟨3954763007944226341762805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636508671962817561175203 3954763007944226341762805)
        ·
          refine ⟨370759031994771219540263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3954763007944226341762805 370759031994771219540263)
          ·
            refine ⟨556138547992156829310395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370759031994771219540263 556138547992156829310395)
            ·
              refine ⟨834207821988235243965593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556138547992156829310395 834207821988235243965593)
              ·
                refine ⟨625655866491176432974195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834207821988235243965593 625655866491176432974195)
                ·
                  refine ⟨938483799736764649461293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625655866491176432974195 938483799736764649461293)
                  ·
                    refine ⟨351931424901286743547985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938483799736764649461293 351931424901286743547985)
                    ·
                      refine ⟨263948568675965057660989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351931424901286743547985 263948568675965057660989)
                      ·
                        rfl

theorem cell23_514038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_514038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514038 prefixEnd_514038 := by exact prefixLift 514038
  have htrace : WordTrace (prefixWord ++ tailWord_514038) baseStart_514038 baseEnd_514038 := by
    simpa [prefixWord, tailWord_514038, baseEnd_514038] using wordTrace_append hprefix tailTrace_514038
  have hstable : (prefixWord ++ tailWord_514038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514038).length < 2 ^ (prefixWord ++ tailWord_514038).sum := by decide
  have hdescent : baseEnd_514038 < baseStart_514038 := by decide
  rcases family_descends (prefixWord ++ tailWord_514038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514073 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_514073 : Nat := 118140960795 + 514073 * 2 ^ 59
def prefixEnd_514073 : Nat := 4983230072969 + 3 ^ 40 * 514073 * 2
def baseEnd_514073 : Nat := 263966540498872420723327

theorem tailTrace_514073 : CollatzResearch.WordTrace tailWord_514073 prefixEnd_514073 263966540498872420723327 := by
  unfold tailWord_514073
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749782666608792523658873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12499855111072528349105915 18749782666608792523658873)
  ·
    refine ⟨14062336999956594392744155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18749782666608792523658873 14062336999956594392744155)
    ·
      refine ⟨21093505499934891589116233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14062336999956594392744155 21093505499934891589116233)
      ·
        refine ⟨15820129124951168691837175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21093505499934891589116233 15820129124951168691837175)
        ·
          refine ⟨23730193687426753037755763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15820129124951168691837175 23730193687426753037755763)
          ·
            refine ⟨35595290531140129556633645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23730193687426753037755763 35595290531140129556633645)
            ·
              refine ⟨13348233949177548583737617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35595290531140129556633645 13348233949177548583737617)
              ·
                refine ⟨10011175461883161437803213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13348233949177548583737617 10011175461883161437803213)
                ·
                  refine ⟨3754190798206185539176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10011175461883161437803213 3754190798206185539176205)
                  ·
                    refine ⟨1407821549327319577191077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3754190798206185539176205 1407821549327319577191077)
                    ·
                      refine ⟨263966540498872420723327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1407821549327319577191077 263966540498872420723327)
                      ·
                        rfl

theorem cell23_514073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_514073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514073 prefixEnd_514073 := by exact prefixLift 514073
  have htrace : WordTrace (prefixWord ++ tailWord_514073) baseStart_514073 baseEnd_514073 := by
    simpa [prefixWord, tailWord_514073, baseEnd_514073] using wordTrace_append hprefix tailTrace_514073
  have hstable : (prefixWord ++ tailWord_514073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514073).length < 2 ^ (prefixWord ++ tailWord_514073).sum := by decide
  have hdescent : baseEnd_514073 < baseStart_514073 := by decide
  rcases family_descends (prefixWord ++ tailWord_514073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514074 : List Nat := [3, 1, 1, 3, 1, 5, 2, 2, 5]
def baseStart_514074 : Nat := 118140960795 + 514074 * 2 ^ 59
def prefixEnd_514074 : Nat := 4983230072969 + 3 ^ 40 * 514074 * 2
def baseEnd_514074 : Nat := 29329672664391879645647

theorem tailTrace_514074 : CollatzResearch.WordTrace tailWord_514074 prefixEnd_514074 29329672664391879645647 := by
  unfold tailWord_514074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687454784901292423611319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12499879426403446462963517 4687454784901292423611319)
  ·
    refine ⟨7031182177351938635416979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4687454784901292423611319 7031182177351938635416979)
    ·
      refine ⟨10546773266027907953125469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7031182177351938635416979 10546773266027907953125469)
      ·
        refine ⟨3955039974760465482422051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10546773266027907953125469 3955039974760465482422051)
        ·
          refine ⟨5932559962140698223633077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955039974760465482422051 5932559962140698223633077)
          ·
            refine ⟨556177496450690458465601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5932559962140698223633077 556177496450690458465601)
            ·
              refine ⟨417133122338017843849201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556177496450690458465601 417133122338017843849201)
              ·
                refine ⟨312849841753513382886901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417133122338017843849201 312849841753513382886901)
                ·
                  refine ⟨29329672664391879645647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312849841753513382886901 29329672664391879645647)
                  ·
                    rfl

theorem cell23_514074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_514074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514074 prefixEnd_514074 := by exact prefixLift 514074
  have htrace : WordTrace (prefixWord ++ tailWord_514074) baseStart_514074 baseEnd_514074 := by
    simpa [prefixWord, tailWord_514074, baseEnd_514074] using wordTrace_append hprefix tailTrace_514074
  have hstable : (prefixWord ++ tailWord_514074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514074).length < 2 ^ (prefixWord ++ tailWord_514074).sum := by decide
  have hdescent : baseEnd_514074 < baseStart_514074 := by decide
  rcases family_descends (prefixWord ++ tailWord_514074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514077 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_514077 : Nat := 118140960795 + 514077 * 2 ^ 59
def prefixEnd_514077 : Nat := 4983230072969 + 3 ^ 40 * 514077 * 2
def baseEnd_514077 : Nat := 263968594421490405073309

theorem tailTrace_514077 : CollatzResearch.WordTrace tailWord_514077 prefixEnd_514077 263968594421490405073309 := by
  unfold tailWord_514077
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749928558594301206804485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12499952372396200804536323 18749928558594301206804485)
  ·
    refine ⟨3515611604736431476275841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18749928558594301206804485 3515611604736431476275841)
    ·
      refine ⟨2636708703552323607206881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3515611604736431476275841 2636708703552323607206881)
      ·
        refine ⟨1977531527664242705405161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2636708703552323607206881 1977531527664242705405161)
        ·
          refine ⟨1483148645748182029053871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1977531527664242705405161 1483148645748182029053871)
          ·
            refine ⟨2224722968622273043580807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483148645748182029053871 2224722968622273043580807)
            ·
              refine ⟨3337084452933409565371211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224722968622273043580807 3337084452933409565371211)
              ·
                refine ⟨5005626679400114348056817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337084452933409565371211 5005626679400114348056817)
                ·
                  refine ⟨3754220009550085761042613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5005626679400114348056817 3754220009550085761042613)
                  ·
                    refine ⟨351958125895320540097745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3754220009550085761042613 351958125895320540097745)
                    ·
                      refine ⟨263968594421490405073309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 351958125895320540097745 263968594421490405073309)
                      ·
                        rfl

theorem cell23_514077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_514077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514077 prefixEnd_514077 := by exact prefixLift 514077
  have htrace : WordTrace (prefixWord ++ tailWord_514077) baseStart_514077 baseEnd_514077 := by
    simpa [prefixWord, tailWord_514077, baseEnd_514077] using wordTrace_append hprefix tailTrace_514077
  have hstable : (prefixWord ++ tailWord_514077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514077).length < 2 ^ (prefixWord ++ tailWord_514077).sum := by decide
  have hdescent : baseEnd_514077 < baseStart_514077 := by decide
  rcases family_descends (prefixWord ++ tailWord_514077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514104 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 2, 5]
def baseStart_514104 : Nat := 118140960795 + 514104 * 2 ^ 59
def prefixEnd_514104 : Nat := 4983230072969 + 3 ^ 40 * 514104 * 2
def baseEnd_514104 : Nat := 87994152799720599811895

theorem tailTrace_514104 : CollatzResearch.WordTrace tailWord_514104 prefixEnd_514104 87994152799720599811895 := by
  unfold tailWord_514104
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375456664748242409018683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12500608886330989878691577 9375456664748242409018683)
  ·
    refine ⟨14063184997122363613528025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9375456664748242409018683 14063184997122363613528025)
    ·
      refine ⟨10547388747841772710146019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14063184997122363613528025 10547388747841772710146019)
      ·
        refine ⟨15821083121762659065219029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10547388747841772710146019 15821083121762659065219029)
        ·
          refine ⟨370806635666312321841071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15821083121762659065219029 370806635666312321841071)
          ·
            refine ⟨556209953499468482761607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370806635666312321841071 556209953499468482761607)
            ·
              refine ⟨834314930249202724142411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556209953499468482761607 834314930249202724142411)
              ·
                refine ⟨1251472395373804086213617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834314930249202724142411 1251472395373804086213617)
                ·
                  refine ⟨938604296530353064660213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1251472395373804086213617 938604296530353064660213)
                  ·
                    refine ⟨87994152799720599811895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 938604296530353064660213 87994152799720599811895)
                    ·
                      rfl

theorem cell23_514104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_514104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514104 prefixEnd_514104 := by exact prefixLift 514104
  have htrace : WordTrace (prefixWord ++ tailWord_514104) baseStart_514104 baseEnd_514104 := by
    simpa [prefixWord, tailWord_514104, baseEnd_514104] using wordTrace_append hprefix tailTrace_514104
  have hstable : (prefixWord ++ tailWord_514104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514104).length < 2 ^ (prefixWord ++ tailWord_514104).sum := by decide
  have hdescent : baseEnd_514104 < baseStart_514104 := by decide
  rcases family_descends (prefixWord ++ tailWord_514104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514143 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 9]
def baseStart_514143 : Nat := 118140960795 + 514143 * 2 ^ 59
def prefixEnd_514143 : Nat := 4983230072969 + 3 ^ 40 * 514143 * 2
def baseEnd_514143 : Nat := 88000828048229048949335

theorem tailTrace_514143 : CollatzResearch.WordTrace tailWord_514143 prefixEnd_514143 88000828048229048949335 := by
  unfold tailWord_514143
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752335776355194478707083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12501557184236796319138055 18752335776355194478707083)
  ·
    refine ⟨28128503664532791718060625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18752335776355194478707083 28128503664532791718060625)
    ·
      refine ⟨21096377748399593788545469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28128503664532791718060625 21096377748399593788545469)
      ·
        refine ⟨7911141655649847670704551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21096377748399593788545469 7911141655649847670704551)
        ·
          refine ⟨11866712483474771506056827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911141655649847670704551 11866712483474771506056827)
          ·
            refine ⟨17800068725212157259085241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866712483474771506056827 17800068725212157259085241)
            ·
              refine ⟨13350051543909117944313931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17800068725212157259085241 13350051543909117944313931)
              ·
                refine ⟨20025077315863676916470897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13350051543909117944313931 20025077315863676916470897)
                ·
                  refine ⟨15018807986897757687353173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20025077315863676916470897 15018807986897757687353173)
                  ·
                    refine ⟨88000828048229048949335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15018807986897757687353173 88000828048229048949335)
                    ·
                      rfl

theorem cell23_514143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_514143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514143 prefixEnd_514143 := by exact prefixLift 514143
  have htrace : WordTrace (prefixWord ++ tailWord_514143) baseStart_514143 baseEnd_514143 := by
    simpa [prefixWord, tailWord_514143, baseEnd_514143] using wordTrace_append hprefix tailTrace_514143
  have hstable : (prefixWord ++ tailWord_514143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514143).length < 2 ^ (prefixWord ++ tailWord_514143).sum := by decide
  have hdescent : baseEnd_514143 < baseStart_514143 := by decide
  rcases family_descends (prefixWord ++ tailWord_514143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514167 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 1, 5, 2]
def baseStart_514167 : Nat := 118140960795 + 514167 * 2 ^ 59
def prefixEnd_514167 : Nat := 4983230072969 + 3 ^ 40 * 514167 * 2
def baseEnd_514167 : Nat := 264014807680395052947895

theorem tailTrace_514167 : CollatzResearch.WordTrace tailWord_514167 prefixEnd_514167 264014807680395052947895 := by
  unfold tailWord_514167
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753211128268246577580755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12502140752178831051720503 18753211128268246577580755)
  ·
    refine ⟨28129816692402369866371133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18753211128268246577580755 28129816692402369866371133)
    ·
      refine ⟨10548681259650888699889175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28129816692402369866371133 10548681259650888699889175)
      ·
        refine ⟨15823021889476333049833763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548681259650888699889175 15823021889476333049833763)
        ·
          refine ⟨23734532834214499574750645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15823021889476333049833763 23734532834214499574750645)
          ·
            refine ⟨2225112453207609335132873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23734532834214499574750645 2225112453207609335132873)
            ·
              refine ⟨1668834339905707001349655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225112453207609335132873 1668834339905707001349655)
              ·
                refine ⟨2503251509858560502024483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668834339905707001349655 2503251509858560502024483)
                ·
                  refine ⟨3754877264787840753036725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503251509858560502024483 3754877264787840753036725)
                  ·
                    refine ⟨352019743573860070597193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3754877264787840753036725 352019743573860070597193)
                    ·
                      refine ⟨264014807680395052947895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352019743573860070597193 264014807680395052947895)
                      ·
                        rfl

theorem cell23_514167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_514167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514167 prefixEnd_514167 := by exact prefixLift 514167
  have htrace : WordTrace (prefixWord ++ tailWord_514167) baseStart_514167 baseEnd_514167 := by
    simpa [prefixWord, tailWord_514167, baseEnd_514167] using wordTrace_append hprefix tailTrace_514167
  have hstable : (prefixWord ++ tailWord_514167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514167).length < 2 ^ (prefixWord ++ tailWord_514167).sum := by decide
  have hdescent : baseEnd_514167 < baseStart_514167 := by decide
  rcases family_descends (prefixWord ++ tailWord_514167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514184 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_514184 : Nat := 118140960795 + 514184 * 2 ^ 59
def prefixEnd_514184 : Nat := 4983230072969 + 3 ^ 40 * 514184 * 2
def baseEnd_514184 : Nat := 264023536851521486435317

theorem tailTrace_514184 : CollatzResearch.WordTrace tailWord_514184 prefixEnd_514184 264023536851521486435317 := by
  unfold tailWord_514184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9376915584603329240474803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12502554112804438987299737 9376915584603329240474803)
  ·
    refine ⟨14065373376904993860712205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9376915584603329240474803 14065373376904993860712205)
    ·
      refine ⟨5274515016339372697767077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14065373376904993860712205 5274515016339372697767077)
      ·
        refine ⟨988971565563632380831327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5274515016339372697767077 988971565563632380831327)
        ·
          refine ⟨1483457348345448571246991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988971565563632380831327 1483457348345448571246991)
          ·
            refine ⟨2225186022518172856870487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483457348345448571246991 2225186022518172856870487)
            ·
              refine ⟨3337779033777259285305731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225186022518172856870487 3337779033777259285305731)
              ·
                refine ⟨5006668550665888927958597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337779033777259285305731 5006668550665888927958597)
                ·
                  refine ⟨938750353249854173992237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5006668550665888927958597 938750353249854173992237)
                  ·
                    refine ⟨352031382468695315247089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938750353249854173992237 352031382468695315247089)
                    ·
                      refine ⟨264023536851521486435317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352031382468695315247089 264023536851521486435317)
                      ·
                        rfl

theorem cell23_514184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_514184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514184 prefixEnd_514184 := by exact prefixLift 514184
  have htrace : WordTrace (prefixWord ++ tailWord_514184) baseStart_514184 baseEnd_514184 := by
    simpa [prefixWord, tailWord_514184, baseEnd_514184] using wordTrace_append hprefix tailTrace_514184
  have hstable : (prefixWord ++ tailWord_514184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514184).length < 2 ^ (prefixWord ++ tailWord_514184).sum := by decide
  have hdescent : baseEnd_514184 < baseStart_514184 := by decide
  rcases family_descends (prefixWord ++ tailWord_514184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514218 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_514218 : Nat := 118140960795 + 514218 * 2 ^ 59
def prefixEnd_514218 : Nat := 4983230072969 + 3 ^ 40 * 514218 * 2
def baseEnd_514218 : Nat := 264040995193774353410161

theorem tailTrace_514218 : CollatzResearch.WordTrace tailWord_514218 prefixEnd_514218 264040995193774353410161 := by
  unfold tailWord_514218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688767812770870571921827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12503380834055654858458205 4688767812770870571921827)
  ·
    refine ⟨7033151719156305857882741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4688767812770870571921827 7033151719156305857882741)
    ·
      refine ⟨659357973670903674176507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7033151719156305857882741 659357973670903674176507)
      ·
        refine ⟨989036960506355511264761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659357973670903674176507 989036960506355511264761)
        ·
          refine ⟨741777720379766633448571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989036960506355511264761 741777720379766633448571)
          ·
            refine ⟨1112666580569649950172857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741777720379766633448571 1112666580569649950172857)
            ·
              refine ⟨834499935427237462629643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112666580569649950172857 834499935427237462629643)
              ·
                refine ⟨1251749903140856193944465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834499935427237462629643 1251749903140856193944465)
                ·
                  refine ⟨938812427355642145458349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1251749903140856193944465 938812427355642145458349)
                  ·
                    refine ⟨352054660258365804546881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 938812427355642145458349 352054660258365804546881)
                    ·
                      refine ⟨264040995193774353410161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352054660258365804546881 264040995193774353410161)
                      ·
                        rfl

theorem cell23_514218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_514218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514218 prefixEnd_514218 := by exact prefixLift 514218
  have htrace : WordTrace (prefixWord ++ tailWord_514218) baseStart_514218 baseEnd_514218 := by
    simpa [prefixWord, tailWord_514218, baseEnd_514218] using wordTrace_append hprefix tailTrace_514218
  have hstable : (prefixWord ++ tailWord_514218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514218).length < 2 ^ (prefixWord ++ tailWord_514218).sum := by decide
  have hdescent : baseEnd_514218 < baseStart_514218 := by decide
  rcases family_descends (prefixWord ++ tailWord_514218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514242 : List Nat := [3, 5, 1, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_514242 : Nat := 118140960795 + 514242 * 2 ^ 59
def prefixEnd_514242 : Nat := 4983230072969 + 3 ^ 40 * 514242 * 2
def baseEnd_514242 : Nat := 264053318729482259510051

theorem tailTrace_514242 : CollatzResearch.WordTrace tailWord_514242 prefixEnd_514242 264053318729482259510051 := by
  unfold tailWord_514242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688986650749133596640245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12503964401997689591040653 4688986650749133596640245)
  ·
    refine ⟨439592498507731274685023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4688986650749133596640245 439592498507731274685023)
    ·
      refine ⟨659388747761596912027535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439592498507731274685023 659388747761596912027535)
      ·
        refine ⟨989083121642395368041303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659388747761596912027535 989083121642395368041303)
        ·
          refine ⟨1483624682463593052061955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989083121642395368041303 1483624682463593052061955)
          ·
            refine ⟨2225437023695389578092933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483624682463593052061955 2225437023695389578092933)
            ·
              refine ⟨417269441942885545892425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2225437023695389578092933 417269441942885545892425)
              ·
                refine ⟨312952081457164159419319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417269441942885545892425 312952081457164159419319)
                ·
                  refine ⟨469428122185746239128979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312952081457164159419319 469428122185746239128979)
                  ·
                    refine ⟨704142183278619358693469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 469428122185746239128979 704142183278619358693469)
                    ·
                      refine ⟨264053318729482259510051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 704142183278619358693469 264053318729482259510051)
                      ·
                        rfl

theorem cell23_514242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_514242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514242 prefixEnd_514242 := by exact prefixLift 514242
  have htrace : WordTrace (prefixWord ++ tailWord_514242) baseStart_514242 baseEnd_514242 := by
    simpa [prefixWord, tailWord_514242, baseEnd_514242] using wordTrace_append hprefix tailTrace_514242
  have hstable : (prefixWord ++ tailWord_514242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514242).length < 2 ^ (prefixWord ++ tailWord_514242).sum := by decide
  have hdescent : baseEnd_514242 < baseStart_514242 := by decide
  rcases family_descends (prefixWord ++ tailWord_514242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514250 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_514250 : Nat := 118140960795 + 514250 * 2 ^ 59
def prefixEnd_514250 : Nat := 4983230072969 + 3 ^ 40 * 514250 * 2
def baseEnd_514250 : Nat := 88019142191572742736671

theorem tailTrace_514250 : CollatzResearch.WordTrace tailWord_514250 prefixEnd_514250 88019142191572742736671 := by
  unfold tailWord_514250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689059596741887938213051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12504158924645034501901469 4689059596741887938213051)
  ·
    refine ⟨7033589395112831907319577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689059596741887938213051 7033589395112831907319577)
    ·
      refine ⟨5275192046334623930489683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7033589395112831907319577 5275192046334623930489683)
      ·
        refine ⟨7912788069501935895734525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275192046334623930489683 7912788069501935895734525)
        ·
          refine ⟨2967295526063225960900447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7912788069501935895734525 2967295526063225960900447)
          ·
            refine ⟨4450943289094838941350671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967295526063225960900447 4450943289094838941350671)
            ·
              refine ⟨6676414933642258412026007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4450943289094838941350671 6676414933642258412026007)
              ·
                refine ⟨10014622400463387618039011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676414933642258412026007 10014622400463387618039011)
                ·
                  refine ⟨15021933600695081427058517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10014622400463387618039011 15021933600695081427058517)
                  ·
                    refine ⟨88019142191572742736671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15021933600695081427058517 88019142191572742736671)
                    ·
                      rfl

theorem cell23_514250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_514250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514250 prefixEnd_514250 := by exact prefixLift 514250
  have htrace : WordTrace (prefixWord ++ tailWord_514250) baseStart_514250 baseEnd_514250 := by
    simpa [prefixWord, tailWord_514250, baseEnd_514250] using wordTrace_append hprefix tailTrace_514250
  have hstable : (prefixWord ++ tailWord_514250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514250).length < 2 ^ (prefixWord ++ tailWord_514250).sum := by decide
  have hdescent : baseEnd_514250 < baseStart_514250 := by decide
  rcases family_descends (prefixWord ++ tailWord_514250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514264 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_514264 : Nat := 118140960795 + 514264 * 2 ^ 59
def prefixEnd_514264 : Nat := 4983230072969 + 3 ^ 40 * 514264 * 2
def baseEnd_514264 : Nat := 264064615303881173434949

theorem tailTrace_514264 : CollatzResearch.WordTrace tailWord_514264 prefixEnd_514264 264064615303881173434949 := by
  unfold tailWord_514264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378374504458416071930923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12504499339277888095907897 9378374504458416071930923)
  ·
    refine ⟨14067561756687624107896385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9378374504458416071930923 14067561756687624107896385)
    ·
      refine ⟨10550671317515718080922289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14067561756687624107896385 10550671317515718080922289)
      ·
        refine ⟨7913003488136788560691717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10550671317515718080922289 7913003488136788560691717)
        ·
          refine ⟨1483688154025647855129697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7913003488136788560691717 1483688154025647855129697)
          ·
            refine ⟨1112766115519235891347273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483688154025647855129697 1112766115519235891347273)
            ·
              refine ⟨834574586639426918510455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112766115519235891347273 834574586639426918510455)
              ·
                refine ⟨1251861879959140377765683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834574586639426918510455 1251861879959140377765683)
                ·
                  refine ⟨1877792819938710566648525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251861879959140377765683 1877792819938710566648525)
                  ·
                    refine ⟨704172307477016462493197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1877792819938710566648525 704172307477016462493197)
                    ·
                      refine ⟨264064615303881173434949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 704172307477016462493197 264064615303881173434949)
                      ·
                        rfl

theorem cell23_514264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_514264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514264 prefixEnd_514264 := by exact prefixLift 514264
  have htrace : WordTrace (prefixWord ++ tailWord_514264) baseStart_514264 baseEnd_514264 := by
    simpa [prefixWord, tailWord_514264, baseEnd_514264] using wordTrace_append hprefix tailTrace_514264
  have hstable : (prefixWord ++ tailWord_514264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514264).length < 2 ^ (prefixWord ++ tailWord_514264).sum := by decide
  have hdescent : baseEnd_514264 < baseStart_514264 := by decide
  rcases family_descends (prefixWord ++ tailWord_514264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514285 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_514285 : Nat := 118140960795 + 514285 * 2 ^ 59
def prefixEnd_514285 : Nat := 4983230072969 + 3 ^ 40 * 514285 * 2
def baseEnd_514285 : Nat := 264075398397625591272353

theorem tailTrace_514285 : CollatzResearch.WordTrace tailWord_514285 prefixEnd_514285 264075398397625591272353 := by
  unfold tailWord_514285
  simp only [CollatzResearch.WordTrace]
  refine ⟨18757514941840752730376309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12505009961227168486917539 18757514941840752730376309)
  ·
    refine ⟨1758517025797570568472779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18757514941840752730376309 1758517025797570568472779)
    ·
      refine ⟨2637775538696355852709169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1758517025797570568472779 2637775538696355852709169)
      ·
        refine ⟨1978331654022266889531877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637775538696355852709169 1978331654022266889531877)
        ·
          refine ⟨370937185129175041787227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1978331654022266889531877 370937185129175041787227)
          ·
            refine ⟨556405777693762562680841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370937185129175041787227 556405777693762562680841)
            ·
              refine ⟨417304333270321922010631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556405777693762562680841 417304333270321922010631)
              ·
                refine ⟨625956499905482883015947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417304333270321922010631 625956499905482883015947)
                ·
                  refine ⟨938934749858224324523921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625956499905482883015947 938934749858224324523921)
                  ·
                    refine ⟨704201062393668243392941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 938934749858224324523921 704201062393668243392941)
                    ·
                      refine ⟨264075398397625591272353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 704201062393668243392941 264075398397625591272353)
                      ·
                        rfl

theorem cell23_514285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_514285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514285 prefixEnd_514285 := by exact prefixLift 514285
  have htrace : WordTrace (prefixWord ++ tailWord_514285) baseStart_514285 baseEnd_514285 := by
    simpa [prefixWord, tailWord_514285, baseEnd_514285] using wordTrace_append hprefix tailTrace_514285
  have hstable : (prefixWord ++ tailWord_514285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514285).length < 2 ^ (prefixWord ++ tailWord_514285).sum := by decide
  have hdescent : baseEnd_514285 < baseStart_514285 := by decide
  rcases family_descends (prefixWord ++ tailWord_514285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514321 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 1, 4, 2]
def baseStart_514321 : Nat := 118140960795 + 514321 * 2 ^ 59
def prefixEnd_514321 : Nat := 4983230072969 + 3 ^ 40 * 514321 * 2
def baseEnd_514321 : Nat := 264093883701187450422187

theorem tailTrace_514321 : CollatzResearch.WordTrace tailWord_514321 prefixEnd_514321 264093883701187450422187 := by
  unfold tailWord_514321
  simp only [CollatzResearch.WordTrace]
  refine ⟨18758827969710330878686817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12505885313140220585791211 18758827969710330878686817)
  ·
    refine ⟨14069120977282748159015113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18758827969710330878686817 14069120977282748159015113)
    ·
      refine ⟨10551840732962061119261335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14069120977282748159015113 10551840732962061119261335)
      ·
        refine ⟨15827761099443091678892003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10551840732962061119261335 15827761099443091678892003)
        ·
          refine ⟨23741641649164637518338005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15827761099443091678892003 23741641649164637518338005)
          ·
            refine ⟨556444726152296191836047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23741641649164637518338005 556444726152296191836047)
            ·
              refine ⟨834667089228444287754071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556444726152296191836047 834667089228444287754071)
              ·
                refine ⟨1252000633842666431631107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834667089228444287754071 1252000633842666431631107)
                ·
                  refine ⟨1878000950763999647446661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252000633842666431631107 1878000950763999647446661)
                  ·
                    refine ⟨352125178268249933896249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1878000950763999647446661 352125178268249933896249)
                    ·
                      refine ⟨264093883701187450422187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352125178268249933896249 264093883701187450422187)
                      ·
                        rfl

theorem cell23_514321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_514321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514321 prefixEnd_514321 := by exact prefixLift 514321
  have htrace : WordTrace (prefixWord ++ tailWord_514321) baseStart_514321 baseEnd_514321 := by
    simpa [prefixWord, tailWord_514321, baseEnd_514321] using wordTrace_append hprefix tailTrace_514321
  have hstable : (prefixWord ++ tailWord_514321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514321).length < 2 ^ (prefixWord ++ tailWord_514321).sum := by decide
  have hdescent : baseEnd_514321 < baseStart_514321 := by decide
  rcases family_descends (prefixWord ++ tailWord_514321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514327 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 7]
def baseStart_514327 : Nat := 118140960795 + 514327 * 2 ^ 59
def prefixEnd_514327 : Nat := 4983230072969 + 3 ^ 40 * 514327 * 2
def baseEnd_514327 : Nat := 29344107176123825216351

theorem tailTrace_514327 : CollatzResearch.WordTrace tailWord_514327 prefixEnd_514327 29344107176123825216351 := by
  unfold tailWord_514327
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759046807688593903405235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12506031205125729268936823 18759046807688593903405235)
  ·
    refine ⟨28138570211532890855107853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18759046807688593903405235 28138570211532890855107853)
    ·
      refine ⟨10551963829324834070665445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28138570211532890855107853 10551963829324834070665445)
      ·
        refine ⟨1978493217998406388249771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10551963829324834070665445 1978493217998406388249771)
        ·
          refine ⟨2967739826997609582374657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978493217998406388249771 2967739826997609582374657)
          ·
            refine ⟨2225804870248207186780993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967739826997609582374657 2225804870248207186780993)
            ·
              refine ⟨1669353652686155390085745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225804870248207186780993 1669353652686155390085745)
              ·
                refine ⟨1252015239514616542564309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669353652686155390085745 1252015239514616542564309)
                ·
                  refine ⟨29344107176123825216351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1252015239514616542564309 29344107176123825216351)
                  ·
                    rfl

theorem cell23_514327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 7].length) (baseStart_514327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514327 prefixEnd_514327 := by exact prefixLift 514327
  have htrace : WordTrace (prefixWord ++ tailWord_514327) baseStart_514327 baseEnd_514327 := by
    simpa [prefixWord, tailWord_514327, baseEnd_514327] using wordTrace_append hprefix tailTrace_514327
  have hstable : (prefixWord ++ tailWord_514327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514327).length < 2 ^ (prefixWord ++ tailWord_514327).sum := by decide
  have hdescent : baseEnd_514327 < baseStart_514327 := by decide
  rcases family_descends (prefixWord ++ tailWord_514327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514337 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_514337 : Nat := 118140960795 + 514337 * 2 ^ 59
def prefixEnd_514337 : Nat := 4983230072969 + 3 ^ 40 * 514337 * 2
def baseEnd_514337 : Nat := 264102099391659387822113

theorem tailTrace_514337 : CollatzResearch.WordTrace tailWord_514337 prefixEnd_514337 264102099391659387822113 := by
  unfold tailWord_514337
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759411537652365611269265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12506274358434910407512843 18759411537652365611269265)
  ·
    refine ⟨14069558653239274208451949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18759411537652365611269265 14069558653239274208451949)
    ·
      refine ⟨5276084494964727828169481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14069558653239274208451949 5276084494964727828169481)
      ·
        refine ⟨3957063371223545871127111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5276084494964727828169481 3957063371223545871127111)
        ·
          refine ⟨5935595056835318806690667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957063371223545871127111 5935595056835318806690667)
          ·
            refine ⟨8903392585252978210036001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935595056835318806690667 8903392585252978210036001)
            ·
              refine ⟨6677544438939733657527001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903392585252978210036001 6677544438939733657527001)
              ·
                refine ⟨5008158329204800243145251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6677544438939733657527001 5008158329204800243145251)
                ·
                  refine ⟨7512237493807200364717877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5008158329204800243145251 7512237493807200364717877)
                  ·
                    refine ⟨704272265044425034192301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7512237493807200364717877 704272265044425034192301)
                    ·
                      refine ⟨264102099391659387822113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 704272265044425034192301 264102099391659387822113)
                      ·
                        rfl

theorem cell23_514337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_514337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514337 prefixEnd_514337 := by exact prefixLift 514337
  have htrace : WordTrace (prefixWord ++ tailWord_514337) baseStart_514337 baseEnd_514337 := by
    simpa [prefixWord, tailWord_514337, baseEnd_514337] using wordTrace_append hprefix tailTrace_514337
  have hstable : (prefixWord ++ tailWord_514337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514337).length < 2 ^ (prefixWord ++ tailWord_514337).sum := by decide
  have hdescent : baseEnd_514337 < baseStart_514337 := by decide
  rcases family_descends (prefixWord ++ tailWord_514337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514364 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_514364 : Nat := 118140960795 + 514364 * 2 ^ 59
def prefixEnd_514364 : Nat := 4983230072969 + 3 ^ 40 * 514364 * 2
def baseEnd_514364 : Nat := 264115963369330782184489

theorem tailTrace_514364 : CollatzResearch.WordTrace tailWord_514364 prefixEnd_514364 264115963369330782184489 := by
  unfold tailWord_514364
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380198154277274611251073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12506930872369699481668097 9380198154277274611251073)
  ·
    refine ⟨7035148615707955958438305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9380198154277274611251073 7035148615707955958438305)
    ·
      refine ⟨5276361461780966968828729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7035148615707955958438305 5276361461780966968828729)
      ·
        refine ⟨3957271096335725226621547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5276361461780966968828729 3957271096335725226621547)
        ·
          refine ⟨5935906644503587839932321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957271096335725226621547 5935906644503587839932321)
          ·
            refine ⟨4451929983377690879949241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5935906644503587839932321 4451929983377690879949241)
            ·
              refine ⟨3338947487533268159961931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451929983377690879949241 3338947487533268159961931)
              ·
                refine ⟨5008421231299902239942897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338947487533268159961931 5008421231299902239942897)
                ·
                  refine ⟨3756315923474926679957173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5008421231299902239942897 3756315923474926679957173)
                  ·
                    refine ⟨352154617825774376245985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3756315923474926679957173 352154617825774376245985)
                    ·
                      refine ⟨264115963369330782184489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352154617825774376245985 264115963369330782184489)
                      ·
                        rfl

theorem cell23_514364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_514364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514364 prefixEnd_514364 := by exact prefixLift 514364
  have htrace : WordTrace (prefixWord ++ tailWord_514364) baseStart_514364 baseEnd_514364 := by
    simpa [prefixWord, tailWord_514364, baseEnd_514364] using wordTrace_append hprefix tailTrace_514364
  have hstable : (prefixWord ++ tailWord_514364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514364).length < 2 ^ (prefixWord ++ tailWord_514364).sum := by decide
  have hdescent : baseEnd_514364 < baseStart_514364 := by decide
  rcases family_descends (prefixWord ++ tailWord_514364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514367 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_514367 : Nat := 118140960795 + 514367 * 2 ^ 59
def prefixEnd_514367 : Nat := 4983230072969 + 3 ^ 40 * 514367 * 2
def baseEnd_514367 : Nat := 264117503811294270446975

theorem tailTrace_514367 : CollatzResearch.WordTrace tailWord_514367 prefixEnd_514367 264117503811294270446975 := by
  unfold tailWord_514367
  simp only [CollatzResearch.WordTrace]
  refine ⟨18760505727543680734861355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12507003818362453823240903 18760505727543680734861355)
  ·
    refine ⟨28140758591315521102292033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18760505727543680734861355 28140758591315521102292033)
    ·
      refine ⟨21105568943486640826719025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28140758591315521102292033 21105568943486640826719025)
      ·
        refine ⟨15829176707614980620039269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21105568943486640826719025 15829176707614980620039269)
        ·
          refine ⟨2967970632677808866257363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15829176707614980620039269 2967970632677808866257363)
          ·
            refine ⟨4451955949016713299386045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967970632677808866257363 4451955949016713299386045)
            ·
              refine ⟨1669483480881267487269767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4451955949016713299386045 1669483480881267487269767)
              ·
                refine ⟨2504225221321901230904651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669483480881267487269767 2504225221321901230904651)
                ·
                  refine ⟨3756337831982851846356977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504225221321901230904651 3756337831982851846356977)
                  ·
                    refine ⟨2817253373987138884767733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3756337831982851846356977 2817253373987138884767733)
                    ·
                      refine ⟨264117503811294270446975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2817253373987138884767733 264117503811294270446975)
                      ·
                        rfl

theorem cell23_514367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_514367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514367 prefixEnd_514367 := by exact prefixLift 514367
  have htrace : WordTrace (prefixWord ++ tailWord_514367) baseStart_514367 baseEnd_514367 := by
    simpa [prefixWord, tailWord_514367, baseEnd_514367] using wordTrace_append hprefix tailTrace_514367
  have hstable : (prefixWord ++ tailWord_514367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514367).length < 2 ^ (prefixWord ++ tailWord_514367).sum := by decide
  have hdescent : baseEnd_514367 < baseStart_514367 := by decide
  rcases family_descends (prefixWord ++ tailWord_514367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514377 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_514377 : Nat := 118140960795 + 514377 * 2 ^ 59
def prefixEnd_514377 : Nat := 4983230072969 + 3 ^ 40 * 514377 * 2
def baseEnd_514377 : Nat := 264122638617839231321929

theorem tailTrace_514377 : CollatzResearch.WordTrace tailWord_514377 prefixEnd_514377 264122638617839231321929 := by
  unfold tailWord_514377
  simp only [CollatzResearch.WordTrace]
  refine ⟨18760870457507452442725385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12507246971671634961816923 18760870457507452442725385)
  ·
    refine ⟨14070652843130589332044039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18760870457507452442725385 14070652843130589332044039)
    ·
      refine ⟨21105979264695883998066059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14070652843130589332044039 21105979264695883998066059)
      ·
        refine ⟨31658968897043825997099089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21105979264695883998066059 31658968897043825997099089)
        ·
          refine ⟨23744226672782869497824317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31658968897043825997099089 23744226672782869497824317)
          ·
            refine ⟨8904085002293576061684119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23744226672782869497824317 8904085002293576061684119)
            ·
              refine ⟨13356127503440364092526179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8904085002293576061684119 13356127503440364092526179)
              ·
                refine ⟨20034191255160546138789269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13356127503440364092526179 20034191255160546138789269)
                ·
                  refine ⟨939102715085650600255747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20034191255160546138789269 939102715085650600255747)
                  ·
                    refine ⟨1408654072628475900383621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 939102715085650600255747 1408654072628475900383621)
                    ·
                      refine ⟨264122638617839231321929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1408654072628475900383621 264122638617839231321929)
                      ·
                        rfl

theorem cell23_514377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_514377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514377 prefixEnd_514377 := by exact prefixLift 514377
  have htrace : WordTrace (prefixWord ++ tailWord_514377) baseStart_514377 baseEnd_514377 := by
    simpa [prefixWord, tailWord_514377, baseEnd_514377] using wordTrace_append hprefix tailTrace_514377
  have hstable : (prefixWord ++ tailWord_514377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514377).length < 2 ^ (prefixWord ++ tailWord_514377).sum := by decide
  have hdescent : baseEnd_514377 < baseStart_514377 := by decide
  rcases family_descends (prefixWord ++ tailWord_514377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514394 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2]
def baseStart_514394 : Nat := 118140960795 + 514394 * 2 ^ 59
def prefixEnd_514394 : Nat := 4983230072969 + 3 ^ 40 * 514394 * 2
def baseEnd_514394 : Nat := 264131367788965664809351

theorem tailTrace_514394 : CollatzResearch.WordTrace tailWord_514394 prefixEnd_514394 264131367788965664809351 := by
  unfold tailWord_514394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690372624611466086523559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12507660332297242897396157 4690372624611466086523559)
  ·
    refine ⟨7035558936917199129785339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4690372624611466086523559 7035558936917199129785339)
    ·
      refine ⟨10553338405375798694678009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7035558936917199129785339 10553338405375798694678009)
      ·
        refine ⟨7915003804031849021008507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10553338405375798694678009 7915003804031849021008507)
        ·
          refine ⟨11872505706047773531512761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7915003804031849021008507 11872505706047773531512761)
          ·
            refine ⟨8904379279535830148634571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11872505706047773531512761 8904379279535830148634571)
            ·
              refine ⟨13356568919303745222951857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8904379279535830148634571 13356568919303745222951857)
              ·
                refine ⟨10017426689477808917213893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13356568919303745222951857 10017426689477808917213893)
                ·
                  refine ⟨1878267504277089171977605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10017426689477808917213893 1878267504277089171977605)
                  ·
                    refine ⟨352175157051954219745801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1878267504277089171977605 352175157051954219745801)
                    ·
                      refine ⟨264131367788965664809351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352175157051954219745801 264131367788965664809351)
                      ·
                        rfl

theorem cell23_514394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_514394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514394 prefixEnd_514394 := by exact prefixLift 514394
  have htrace : WordTrace (prefixWord ++ tailWord_514394) baseStart_514394 baseEnd_514394 := by
    simpa [prefixWord, tailWord_514394, baseEnd_514394] using wordTrace_append hprefix tailTrace_514394
  have hstable : (prefixWord ++ tailWord_514394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514394).length < 2 ^ (prefixWord ++ tailWord_514394).sum := by decide
  have hdescent : baseEnd_514394 < baseStart_514394 := by decide
  rcases family_descends (prefixWord ++ tailWord_514394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514518 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_514518 : Nat := 118140960795 + 514518 * 2 ^ 59
def prefixEnd_514518 : Nat := 4983230072969 + 3 ^ 40 * 514518 * 2
def baseEnd_514518 : Nat := 264195039390123179658781

theorem tailTrace_514518 : CollatzResearch.WordTrace tailWord_514518 prefixEnd_514518 264195039390123179658781 := by
  unfold tailWord_514518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172875821874789595225513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12510675433331089015738805 1172875821874789595225513)
  ·
    refine ⟨879656866406092196419135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1172875821874789595225513 879656866406092196419135)
    ·
      refine ⟨1319485299609138294628703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879656866406092196419135 1319485299609138294628703)
      ·
        refine ⟨1979227949413707441943055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319485299609138294628703 1979227949413707441943055)
        ·
          refine ⟨2968841924120561162914583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979227949413707441943055 2968841924120561162914583)
          ·
            refine ⟨4453262886180841744371875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968841924120561162914583 4453262886180841744371875)
            ·
              refine ⟨6679894329271262616557813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453262886180841744371875 6679894329271262616557813)
              ·
                refine ⟨626240093369180870302295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6679894329271262616557813 626240093369180870302295)
                ·
                  refine ⟨939360140053771305453443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626240093369180870302295 939360140053771305453443)
                  ·
                    refine ⟨1409040210080656958180165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 939360140053771305453443 1409040210080656958180165)
                    ·
                      refine ⟨264195039390123179658781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1409040210080656958180165 264195039390123179658781)
                      ·
                        rfl

theorem cell23_514518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_514518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514518 prefixEnd_514518 := by exact prefixLift 514518
  have htrace : WordTrace (prefixWord ++ tailWord_514518) baseStart_514518 baseEnd_514518 := by
    simpa [prefixWord, tailWord_514518, baseEnd_514518] using wordTrace_append hprefix tailTrace_514518
  have hstable : (prefixWord ++ tailWord_514518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514518).length < 2 ^ (prefixWord ++ tailWord_514518).sum := by decide
  have hdescent : baseEnd_514518 < baseStart_514518 := by decide
  rcases family_descends (prefixWord ++ tailWord_514518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514521 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 3]
def baseStart_514521 : Nat := 118140960795 + 514521 * 2 ^ 59
def prefixEnd_514521 : Nat := 4983230072969 + 3 ^ 40 * 514521 * 2
def baseEnd_514521 : Nat := 264196579832086667921267

theorem tailTrace_514521 : CollatzResearch.WordTrace tailWord_514521 prefixEnd_514521 264196579832086667921267 := by
  unfold tailWord_514521
  simp only [CollatzResearch.WordTrace]
  refine ⟨18766122568985765035967417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12510748379323843357311611 18766122568985765035967417)
  ·
    refine ⟨14074591926739323776975563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18766122568985765035967417 14074591926739323776975563)
    ·
      refine ⟨21111887890108985665463345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14074591926739323776975563 21111887890108985665463345)
      ·
        refine ⟨15833915917581739249097509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21111887890108985665463345 15833915917581739249097509)
        ·
          refine ⟨2968859234546576109205783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15833915917581739249097509 2968859234546576109205783)
          ·
            refine ⟨4453288851819864163808675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968859234546576109205783 4453288851819864163808675)
            ·
              refine ⟨6679933277729796245713013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453288851819864163808675 6679933277729796245713013)
              ·
                refine ⟨626243744787168398035595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6679933277729796245713013 626243744787168398035595)
                ·
                  refine ⟨939365617180752597053393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626243744787168398035595 939365617180752597053393)
                  ·
                    refine ⟨704524212885564447790045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 939365617180752597053393 704524212885564447790045)
                    ·
                      refine ⟨264196579832086667921267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 704524212885564447790045 264196579832086667921267)
                      ·
                        rfl

theorem cell23_514521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_514521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514521 prefixEnd_514521 := by exact prefixLift 514521
  have htrace : WordTrace (prefixWord ++ tailWord_514521) baseStart_514521 baseEnd_514521 := by
    simpa [prefixWord, tailWord_514521, baseEnd_514521] using wordTrace_append hprefix tailTrace_514521
  have hstable : (prefixWord ++ tailWord_514521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514521).length < 2 ^ (prefixWord ++ tailWord_514521).sum := by decide
  have hdescent : baseEnd_514521 < baseStart_514521 := by decide
  rcases family_descends (prefixWord ++ tailWord_514521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514541 : List Nat := [1, 5, 1, 3, 1, 2, 2, 8]
def baseStart_514541 : Nat := 118140960795 + 514541 * 2 ^ 59
def prefixEnd_514541 : Nat := 4983230072969 + 3 ^ 40 * 514541 * 2
def baseEnd_514541 : Nat := 9785438868339873691525

theorem tailTrace_514541 : CollatzResearch.WordTrace tailWord_514541 prefixEnd_514541 9785438868339873691525 := by
  unfold tailWord_514541
  simp only [CollatzResearch.WordTrace]
  refine ⟨18766852028913308451695477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12511234685942205634463651 18766852028913308451695477)
  ·
    refine ⟨1759392377710622667346451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18766852028913308451695477 1759392377710622667346451)
    ·
      refine ⟨2639088566565934001019677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1759392377710622667346451 2639088566565934001019677)
      ·
        refine ⟨989658212462225250382379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2639088566565934001019677 989658212462225250382379)
        ·
          refine ⟨1484487318693337875573569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989658212462225250382379 1484487318693337875573569)
          ·
            refine ⟨1113365489020003406680177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484487318693337875573569 1113365489020003406680177)
            ·
              refine ⟨835024116765002555010133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113365489020003406680177 835024116765002555010133)
              ·
                refine ⟨9785438868339873691525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 835024116765002555010133 9785438868339873691525)
                ·
                  rfl

theorem cell23_514541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 8].length) (baseStart_514541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514541 prefixEnd_514541 := by exact prefixLift 514541
  have htrace : WordTrace (prefixWord ++ tailWord_514541) baseStart_514541 baseEnd_514541 := by
    simpa [prefixWord, tailWord_514541, baseEnd_514541] using wordTrace_append hprefix tailTrace_514541
  have hstable : (prefixWord ++ tailWord_514541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514541).length < 2 ^ (prefixWord ++ tailWord_514541).sum := by decide
  have hdescent : baseEnd_514541 < baseStart_514541 := by decide
  rcases family_descends (prefixWord ++ tailWord_514541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514591 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 5, 4, 2]
def baseStart_514591 : Nat := 118140960795 + 514591 * 2 ^ 59
def prefixEnd_514591 : Nat := 4983230072969 + 3 ^ 40 * 514591 * 2
def baseEnd_514591 : Nat := 264232523477901394045945

theorem tailTrace_514591 : CollatzResearch.WordTrace tailWord_514591 prefixEnd_514591 264232523477901394045945 := by
  unfold tailWord_514591
  simp only [CollatzResearch.WordTrace]
  refine ⟨18768675678732166991015627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12512450452488111327343751 18768675678732166991015627)
  ·
    refine ⟨28153013518098250486523441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18768675678732166991015627 28153013518098250486523441)
    ·
      refine ⟨21114760138573687864892581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28153013518098250486523441 21114760138573687864892581)
      ·
        refine ⟨3959017525982566474667359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21114760138573687864892581 3959017525982566474667359)
        ·
          refine ⟨5938526288973849712001039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959017525982566474667359 5938526288973849712001039)
          ·
            refine ⟨8907789433460774568001559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938526288973849712001039 8907789433460774568001559)
            ·
              refine ⟨13361684150191161852002339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907789433460774568001559 13361684150191161852002339)
              ·
                refine ⟨20042526225286742778003509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361684150191161852002339 20042526225286742778003509)
                ·
                  refine ⟨1878986833620632135437829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20042526225286742778003509 1878986833620632135437829)
                  ·
                    refine ⟨352310031303868525394593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1878986833620632135437829 352310031303868525394593)
                    ·
                      refine ⟨264232523477901394045945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352310031303868525394593 264232523477901394045945)
                      ·
                        rfl

theorem cell23_514591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_514591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514591 prefixEnd_514591 := by exact prefixLift 514591
  have htrace : WordTrace (prefixWord ++ tailWord_514591) baseStart_514591 baseEnd_514591 := by
    simpa [prefixWord, tailWord_514591, baseEnd_514591] using wordTrace_append hprefix tailTrace_514591
  have hstable : (prefixWord ++ tailWord_514591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514591).length < 2 ^ (prefixWord ++ tailWord_514591).sum := by decide
  have hdescent : baseEnd_514591 < baseStart_514591 := by decide
  rcases family_descends (prefixWord ++ tailWord_514591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514641 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_514641 : Nat := 118140960795 + 514641 * 2 ^ 59
def prefixEnd_514641 : Nat := 4983230072969 + 3 ^ 40 * 514641 * 2
def baseEnd_514641 : Nat := 264258197510626198420715

theorem tailTrace_514641 : CollatzResearch.WordTrace tailWord_514641 prefixEnd_514641 264258197510626198420715 := by
  unfold tailWord_514641
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770499328551025530335777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12513666219034017020223851 18770499328551025530335777)
  ·
    refine ⟨14077874496413269147751833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18770499328551025530335777 14077874496413269147751833)
    ·
      refine ⟨10558405872309951860813875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14077874496413269147751833 10558405872309951860813875)
      ·
        refine ⟨15837608808464927791220813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558405872309951860813875 15837608808464927791220813)
        ·
          refine ⟨5939103303174347921707805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15837608808464927791220813 5939103303174347921707805)
          ·
            refine ⟨2227163738690380470640427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5939103303174347921707805 2227163738690380470640427)
            ·
              refine ⟨3340745608035570705960641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227163738690380470640427 3340745608035570705960641)
              ·
                refine ⟨2505559206026678029470481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340745608035570705960641 2505559206026678029470481)
                ·
                  refine ⟨1879169404520008522102861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505559206026678029470481 1879169404520008522102861)
                  ·
                    refine ⟨704688526695003195788573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879169404520008522102861 704688526695003195788573)
                    ·
                      refine ⟨264258197510626198420715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 704688526695003195788573 264258197510626198420715)
                      ·
                        rfl

theorem cell23_514641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_514641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514641 prefixEnd_514641 := by exact prefixLift 514641
  have htrace : WordTrace (prefixWord ++ tailWord_514641) baseStart_514641 baseEnd_514641 := by
    simpa [prefixWord, tailWord_514641, baseEnd_514641] using wordTrace_append hprefix tailTrace_514641
  have hstable : (prefixWord ++ tailWord_514641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514641).length < 2 ^ (prefixWord ++ tailWord_514641).sum := by decide
  have hdescent : baseEnd_514641 < baseStart_514641 := by decide
  rcases family_descends (prefixWord ++ tailWord_514641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514681 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_514681 : Nat := 118140960795 + 514681 * 2 ^ 59
def prefixEnd_514681 : Nat := 4983230072969 + 3 ^ 40 * 514681 * 2
def baseEnd_514681 : Nat := 264278736736806041920531

theorem tailTrace_514681 : CollatzResearch.WordTrace tailWord_514681 prefixEnd_514681 264278736736806041920531 := by
  unfold tailWord_514681
  simp only [CollatzResearch.WordTrace]
  refine ⟨18771958248406112361791897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12514638832270741574527931 18771958248406112361791897)
  ·
    refine ⟨14078968686304584271343923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18771958248406112361791897 14078968686304584271343923)
    ·
      refine ⟨21118453029456876407015885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14078968686304584271343923 21118453029456876407015885)
      ·
        refine ⟨7919419886046328652630957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21118453029456876407015885 7919419886046328652630957)
        ·
          refine ⟨2969782457267373244736609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7919419886046328652630957 2969782457267373244736609)
          ·
            refine ⟨2227336842950529933552457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969782457267373244736609 2227336842950529933552457)
            ·
              refine ⟨1670502632212897450164343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227336842950529933552457 1670502632212897450164343)
              ·
                refine ⟨2505753948319346175246515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670502632212897450164343 2505753948319346175246515)
                ·
                  refine ⟨3758630922479019262869773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505753948319346175246515 3758630922479019262869773)
                  ·
                    refine ⟨1409486595929632223576165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3758630922479019262869773 1409486595929632223576165)
                    ·
                      refine ⟨264278736736806041920531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1409486595929632223576165 264278736736806041920531)
                      ·
                        rfl

theorem cell23_514681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_514681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514681 prefixEnd_514681 := by exact prefixLift 514681
  have htrace : WordTrace (prefixWord ++ tailWord_514681) baseStart_514681 baseEnd_514681 := by
    simpa [prefixWord, tailWord_514681, baseEnd_514681] using wordTrace_append hprefix tailTrace_514681
  have hstable : (prefixWord ++ tailWord_514681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514681).length < 2 ^ (prefixWord ++ tailWord_514681).sum := by decide
  have hdescent : baseEnd_514681 < baseStart_514681 := by decide
  rcases family_descends (prefixWord ++ tailWord_514681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514691 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 5, 4]
def baseStart_514691 : Nat := 118140960795 + 514691 * 2 ^ 59
def prefixEnd_514691 : Nat := 4983230072969 + 3 ^ 40 * 514691 * 2
def baseEnd_514691 : Nat := 88094623847783667598495

theorem tailTrace_514691 : CollatzResearch.WordTrace tailWord_514691 prefixEnd_514691 88094623847783667598495 := by
  unfold tailWord_514691
  simp only [CollatzResearch.WordTrace]
  refine ⟨18772322978369884069655927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12514881985579922713103951 18772322978369884069655927)
  ·
    refine ⟨28158484467554826104483891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18772322978369884069655927 28158484467554826104483891)
    ·
      refine ⟨42237726701332239156725837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28158484467554826104483891 42237726701332239156725837)
      ·
        refine ⟨15839147512999589683772189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42237726701332239156725837 15839147512999589683772189)
        ·
          refine ⟨5939680317374846131414571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15839147512999589683772189 5939680317374846131414571)
          ·
            refine ⟨8909520476062269197121857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5939680317374846131414571 8909520476062269197121857)
            ·
              refine ⟨6682140357046701897841393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8909520476062269197121857 6682140357046701897841393)
              ·
                refine ⟨5011605267785026423381045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682140357046701897841393 5011605267785026423381045)
                ·
                  refine ⟨469837993854846227191973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5011605267785026423381045 469837993854846227191973)
                  ·
                    refine ⟨88094623847783667598495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 469837993854846227191973 88094623847783667598495)
                    ·
                      rfl

theorem cell23_514691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 4].length) (baseStart_514691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514691 prefixEnd_514691 := by exact prefixLift 514691
  have htrace : WordTrace (prefixWord ++ tailWord_514691) baseStart_514691 baseEnd_514691 := by
    simpa [prefixWord, tailWord_514691, baseEnd_514691] using wordTrace_append hprefix tailTrace_514691
  have hstable : (prefixWord ++ tailWord_514691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514691).length < 2 ^ (prefixWord ++ tailWord_514691).sum := by decide
  have hdescent : baseEnd_514691 < baseStart_514691 := by decide
  rcases family_descends (prefixWord ++ tailWord_514691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514788 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_514788 : Nat := 118140960795 + 514788 * 2 ^ 59
def prefixEnd_514788 : Nat := 4983230072969 + 3 ^ 40 * 514788 * 2
def baseEnd_514788 : Nat := 264333679166837123282539

theorem tailTrace_514788 : CollatzResearch.WordTrace tailWord_514788 prefixEnd_514788 264333679166837123282539 := by
  unfold tailWord_514788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9387930429509234817968509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12517240572678979757291345 9387930429509234817968509)
  ·
    refine ⟨3520473911065963056738191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9387930429509234817968509 3520473911065963056738191)
    ·
      refine ⟨5280710866598944585107287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520473911065963056738191 5280710866598944585107287)
      ·
        refine ⟨7921066299898416877660931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280710866598944585107287 7921066299898416877660931)
        ·
          refine ⟨11881599449847625316491397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7921066299898416877660931 11881599449847625316491397)
          ·
            refine ⟨2227799896846429746842137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11881599449847625316491397 2227799896846429746842137)
            ·
              refine ⟨1670849922634822310131603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227799896846429746842137 1670849922634822310131603)
              ·
                refine ⟨2506274883952233465197405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670849922634822310131603 2506274883952233465197405)
                ·
                  refine ⟨939853081482087549449027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2506274883952233465197405 939853081482087549449027)
                  ·
                    refine ⟨1409779622223131324173541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 939853081482087549449027 1409779622223131324173541)
                    ·
                      refine ⟨264333679166837123282539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1409779622223131324173541 264333679166837123282539)
                      ·
                        rfl

theorem cell23_514788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_514788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514788 prefixEnd_514788 := by exact prefixLift 514788
  have htrace : WordTrace (prefixWord ++ tailWord_514788) baseStart_514788 baseEnd_514788 := by
    simpa [prefixWord, tailWord_514788, baseEnd_514788] using wordTrace_append hprefix tailTrace_514788
  have hstable : (prefixWord ++ tailWord_514788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514788).length < 2 ^ (prefixWord ++ tailWord_514788).sum := by decide
  have hdescent : baseEnd_514788 < baseStart_514788 := by decide
  rcases family_descends (prefixWord ++ tailWord_514788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514798 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_514798 : Nat := 118140960795 + 514798 * 2 ^ 59
def prefixEnd_514798 : Nat := 4983230072969 + 3 ^ 40 * 514798 * 2
def baseEnd_514798 : Nat := 88112937991127361385831

theorem tailTrace_514798 : CollatzResearch.WordTrace tailWord_514798 prefixEnd_514798 88112937991127361385831 := by
  unfold tailWord_514798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347028198622780167975131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12517483725988160895867365 2347028198622780167975131)
  ·
    refine ⟨3520542297934170251962697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2347028198622780167975131 3520542297934170251962697)
    ·
      refine ⟨2640406723450627688972023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3520542297934170251962697 2640406723450627688972023)
      ·
        refine ⟨3960610085175941533458035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640406723450627688972023 3960610085175941533458035)
        ·
          refine ⟨5940915127763912300187053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960610085175941533458035 5940915127763912300187053)
          ·
            refine ⟨2227843172911467112570145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5940915127763912300187053 2227843172911467112570145)
            ·
              refine ⟨1670882379683600334427609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227843172911467112570145 1670882379683600334427609)
              ·
                refine ⟨1253161784762700250820707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670882379683600334427609 1253161784762700250820707)
                ·
                  refine ⟨1879742677144050376231061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253161784762700250820707 1879742677144050376231061)
                  ·
                    refine ⟨88112937991127361385831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1879742677144050376231061 88112937991127361385831)
                    ·
                      rfl

theorem cell23_514798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_514798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514798 prefixEnd_514798 := by exact prefixLift 514798
  have htrace : WordTrace (prefixWord ++ tailWord_514798) baseStart_514798 baseEnd_514798 := by
    simpa [prefixWord, tailWord_514798, baseEnd_514798] using wordTrace_append hprefix tailTrace_514798
  have hstable : (prefixWord ++ tailWord_514798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514798).length < 2 ^ (prefixWord ++ tailWord_514798).sum := by decide
  have hdescent : baseEnd_514798 < baseStart_514798 := by decide
  rcases family_descends (prefixWord ++ tailWord_514798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514802 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_514802 : Nat := 118140960795 + 514802 * 2 ^ 59
def prefixEnd_514802 : Nat := 4983230072969 + 3 ^ 40 * 514802 * 2
def baseEnd_514802 : Nat := 88113622632000022835825

theorem tailTrace_514802 : CollatzResearch.WordTrace tailWord_514802 prefixEnd_514802 88113622632000022835825 := by
  unfold tailWord_514802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694092870241937506736665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12517580987311833351297773 4694092870241937506736665)
  ·
    refine ⟨3520569652681453130052499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4694092870241937506736665 3520569652681453130052499)
    ·
      refine ⟨5280854479022179695078749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520569652681453130052499 5280854479022179695078749)
      ·
        refine ⟨1980320429633317385654531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5280854479022179695078749 1980320429633317385654531)
        ·
          refine ⟨2970480644449976078481797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980320429633317385654531 2970480644449976078481797)
          ·
            refine ⟨556965120834370514715337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2970480644449976078481797 556965120834370514715337)
            ·
              refine ⟨417723840625777886036503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556965120834370514715337 417723840625777886036503)
              ·
                refine ⟨626585760938666829054755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417723840625777886036503 626585760938666829054755)
                ·
                  refine ⟨939878641408000243582133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626585760938666829054755 939878641408000243582133)
                  ·
                    refine ⟨88113622632000022835825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 939878641408000243582133 88113622632000022835825)
                    ·
                      rfl

theorem cell23_514802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_514802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514802 prefixEnd_514802 := by exact prefixLift 514802
  have htrace : WordTrace (prefixWord ++ tailWord_514802) baseStart_514802 baseEnd_514802 := by
    simpa [prefixWord, tailWord_514802, baseEnd_514802] using wordTrace_append hprefix tailTrace_514802
  have hstable : (prefixWord ++ tailWord_514802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514802).length < 2 ^ (prefixWord ++ tailWord_514802).sum := by decide
  have hdescent : baseEnd_514802 < baseStart_514802 := by decide
  rcases family_descends (prefixWord ++ tailWord_514802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514845 : List Nat := [1, 4, 2, 4, 1, 1, 1, 9]
def baseStart_514845 : Nat := 118140960795 + 514845 * 2 ^ 59
def prefixEnd_514845 : Nat := 4983230072969 + 3 ^ 40 * 514845 * 2
def baseEnd_514845 : Nat := 9791220280153459269251

theorem tailTrace_514845 : CollatzResearch.WordTrace tailWord_514845 prefixEnd_514845 9791220280153459269251 := by
  unfold tailWord_514845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18777939819811968370761989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12518626546541312247174659 18777939819811968370761989)
  ·
    refine ⟨3520863716214744069517873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18777939819811968370761989 3520863716214744069517873)
    ·
      refine ⟨2640647787161058052138405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3520863716214744069517873 2640647787161058052138405)
      ·
        refine ⟨495121460092698384775951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2640647787161058052138405 495121460092698384775951)
        ·
          refine ⟨742682190139047577163927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495121460092698384775951 742682190139047577163927)
          ·
            refine ⟨1114023285208571365745891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742682190139047577163927 1114023285208571365745891)
            ·
              refine ⟨1671034927812857048618837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114023285208571365745891 1671034927812857048618837)
              ·
                refine ⟨9791220280153459269251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1671034927812857048618837 9791220280153459269251)
                ·
                  rfl

theorem cell23_514845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 9].length) (baseStart_514845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514845 prefixEnd_514845 := by exact prefixLift 514845
  have htrace : WordTrace (prefixWord ++ tailWord_514845) baseStart_514845 baseEnd_514845 := by
    simpa [prefixWord, tailWord_514845, baseEnd_514845] using wordTrace_append hprefix tailTrace_514845
  have hstable : (prefixWord ++ tailWord_514845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514845).length < 2 ^ (prefixWord ++ tailWord_514845).sum := by decide
  have hdescent : baseEnd_514845 < baseStart_514845 := by decide
  rcases family_descends (prefixWord ++ tailWord_514845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514889 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 2, 1, 3]
def baseStart_514889 : Nat := 118140960795 + 514889 * 2 ^ 59
def prefixEnd_514889 : Nat := 4983230072969 + 3 ^ 40 * 514889 * 2
def baseEnd_514889 : Nat := 264385540712941228119575

theorem tailTrace_514889 : CollatzResearch.WordTrace tailWord_514889 prefixEnd_514889 264385540712941228119575 := by
  unfold tailWord_514889
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779544631652563885363721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12519696421101709256909147 18779544631652563885363721)
  ·
    refine ⟨14084658473739422914022791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18779544631652563885363721 14084658473739422914022791)
    ·
      refine ⟨21126987710609134371034187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14084658473739422914022791 21126987710609134371034187)
      ·
        refine ⟨31690481565913701556551281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21126987710609134371034187 31690481565913701556551281)
        ·
          refine ⟨23767861174435276167413461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31690481565913701556551281 23767861174435276167413461)
          ·
            refine ⟨557059246275826785173753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23767861174435276167413461 557059246275826785173753)
            ·
              refine ⟨417794434706870088880315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557059246275826785173753 417794434706870088880315)
              ·
                refine ⟨626691652060305133320473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417794434706870088880315 626691652060305133320473)
                ·
                  refine ⟨470018739045228849990355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626691652060305133320473 470018739045228849990355)
                  ·
                    refine ⟨705028108567843274985533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470018739045228849990355 705028108567843274985533)
                    ·
                      refine ⟨264385540712941228119575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 705028108567843274985533 264385540712941228119575)
                      ·
                        rfl

theorem cell23_514889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 1, 3].length) (baseStart_514889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514889 prefixEnd_514889 := by exact prefixLift 514889
  have htrace : WordTrace (prefixWord ++ tailWord_514889) baseStart_514889 baseEnd_514889 := by
    simpa [prefixWord, tailWord_514889, baseEnd_514889] using wordTrace_append hprefix tailTrace_514889
  have hstable : (prefixWord ++ tailWord_514889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514889).length < 2 ^ (prefixWord ++ tailWord_514889).sum := by decide
  have hdescent : baseEnd_514889 < baseStart_514889 := by decide
  rcases family_descends (prefixWord ++ tailWord_514889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514891 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6]
def baseStart_514891 : Nat := 118140960795 + 514891 * 2 ^ 59
def prefixEnd_514891 : Nat := 4983230072969 + 3 ^ 40 * 514891 * 2
def baseEnd_514891 : Nat := 264386567674250220294565

theorem tailTrace_514891 : CollatzResearch.WordTrace tailWord_514891 prefixEnd_514891 264386567674250220294565 := by
  unfold tailWord_514891
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779617577645318226936527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12519745051763545484624351 18779617577645318226936527)
  ·
    refine ⟨28169426366467977340404791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18779617577645318226936527 28169426366467977340404791)
    ·
      refine ⟨42254139549701966010607187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28169426366467977340404791 42254139549701966010607187)
      ·
        refine ⟨63381209324552949015910781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42254139549701966010607187 63381209324552949015910781)
        ·
          refine ⟨23767953496707355880966543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63381209324552949015910781 23767953496707355880966543)
          ·
            refine ⟨35651930245061033821449815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23767953496707355880966543 35651930245061033821449815)
            ·
              refine ⟨53477895367591550732174723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35651930245061033821449815 53477895367591550732174723)
              ·
                refine ⟨80216843051387326098262085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53477895367591550732174723 80216843051387326098262085)
                ·
                  refine ⟨15040658072135123643424141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80216843051387326098262085 15040658072135123643424141)
                  ·
                    refine ⟨5640246777050671366284053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15040658072135123643424141 5640246777050671366284053)
                    ·
                      refine ⟨264386567674250220294565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5640246777050671366284053 264386567674250220294565)
                      ·
                        rfl

theorem cell23_514891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_514891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514891 prefixEnd_514891 := by exact prefixLift 514891
  have htrace : WordTrace (prefixWord ++ tailWord_514891) baseStart_514891 baseEnd_514891 := by
    simpa [prefixWord, tailWord_514891, baseEnd_514891] using wordTrace_append hprefix tailTrace_514891
  have hstable : (prefixWord ++ tailWord_514891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514891).length < 2 ^ (prefixWord ++ tailWord_514891).sum := by decide
  have hdescent : baseEnd_514891 < baseStart_514891 := by decide
  rcases family_descends (prefixWord ++ tailWord_514891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514898 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_514898 : Nat := 118140960795 + 514898 * 2 ^ 59
def prefixEnd_514898 : Nat := 4983230072969 + 3 ^ 40 * 514898 * 2
def baseEnd_514898 : Nat := 264390162038831692907033

theorem tailTrace_514898 : CollatzResearch.WordTrace tailWord_514898 prefixEnd_514898 264390162038831692907033 := by
  unfold tailWord_514898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694968222154989605610337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12519915259079972281627565 4694968222154989605610337)
  ·
    refine ⟨3521226166616242204207753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4694968222154989605610337 3521226166616242204207753)
    ·
      refine ⟨2640919624962181653155815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3521226166616242204207753 2640919624962181653155815)
      ·
        refine ⟨3961379437443272479733723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640919624962181653155815 3961379437443272479733723)
        ·
          refine ⟨5942069156164908719600585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961379437443272479733723 5942069156164908719600585)
          ·
            refine ⟨4456551867123681539700439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5942069156164908719600585 4456551867123681539700439)
            ·
              refine ⟨6684827800685522309550659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456551867123681539700439 6684827800685522309550659)
              ·
                refine ⟨10027241701028283464325989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6684827800685522309550659 10027241701028283464325989)
                ·
                  refine ⟨1880107818942803149561123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10027241701028283464325989 1880107818942803149561123)
                  ·
                    refine ⟨2820161728414204724341685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1880107818942803149561123 2820161728414204724341685)
                    ·
                      refine ⟨264390162038831692907033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2820161728414204724341685 264390162038831692907033)
                      ·
                        rfl

theorem cell23_514898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_514898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514898 prefixEnd_514898 := by exact prefixLift 514898
  have htrace : WordTrace (prefixWord ++ tailWord_514898) baseStart_514898 baseEnd_514898 := by
    simpa [prefixWord, tailWord_514898, baseEnd_514898] using wordTrace_append hprefix tailTrace_514898
  have hstable : (prefixWord ++ tailWord_514898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514898).length < 2 ^ (prefixWord ++ tailWord_514898).sum := by decide
  have hdescent : baseEnd_514898 < baseStart_514898 := by decide
  rcases family_descends (prefixWord ++ tailWord_514898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514929 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 2, 2, 2]
def baseStart_514929 : Nat := 118140960795 + 514929 * 2 ^ 59
def prefixEnd_514929 : Nat := 4983230072969 + 3 ^ 40 * 514929 * 2
def baseEnd_514929 : Nat := 264406079939121071619391

theorem tailTrace_514929 : CollatzResearch.WordTrace tailWord_514929 prefixEnd_514929 264406079939121071619391 := by
  unfold tailWord_514929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18781003551507650716819841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12520669034338433811213227 18781003551507650716819841)
  ·
    refine ⟨14085752663630738037614881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18781003551507650716819841 14085752663630738037614881)
    ·
      refine ⟨10564314497723053528211161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14085752663630738037614881 10564314497723053528211161)
      ·
        refine ⟨7923235873292290146158371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10564314497723053528211161 7923235873292290146158371)
        ·
          refine ⟨11884853809938435219237557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7923235873292290146158371 11884853809938435219237557)
          ·
            refine ⟨1114205044681728301803521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11884853809938435219237557 1114205044681728301803521)
            ·
              refine ⟨835653783511296226352641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114205044681728301803521 835653783511296226352641)
              ·
                refine ⟨626740337633472169764481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835653783511296226352641 626740337633472169764481)
                ·
                  refine ⟨470055253225104127323361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626740337633472169764481 470055253225104127323361)
                  ·
                    refine ⟨352541439918828095492521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470055253225104127323361 352541439918828095492521)
                    ·
                      refine ⟨264406079939121071619391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352541439918828095492521 264406079939121071619391)
                      ·
                        rfl

theorem cell23_514929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_514929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514929 prefixEnd_514929 := by exact prefixLift 514929
  have htrace : WordTrace (prefixWord ++ tailWord_514929) baseStart_514929 baseEnd_514929 := by
    simpa [prefixWord, tailWord_514929, baseEnd_514929] using wordTrace_append hprefix tailTrace_514929
  have hstable : (prefixWord ++ tailWord_514929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514929).length < 2 ^ (prefixWord ++ tailWord_514929).sum := by decide
  have hdescent : baseEnd_514929 < baseStart_514929 := by decide
  rcases family_descends (prefixWord ++ tailWord_514929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514948 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_514948 : Nat := 118140960795 + 514948 * 2 ^ 59
def prefixEnd_514948 : Nat := 4983230072969 + 3 ^ 40 * 514948 * 2
def baseEnd_514948 : Nat := 88138612023852165760601

theorem tailTrace_514948 : CollatzResearch.WordTrace tailWord_514948 prefixEnd_514948 88138612023852165760601 := by
  unfold tailWord_514948
  simp only [CollatzResearch.WordTrace]
  refine ⟨9390848269219408480880749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12521131025625877974507665 9390848269219408480880749)
  ·
    refine ⟨3521568100957278180330281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9390848269219408480880749 3521568100957278180330281)
    ·
      refine ⟨2641176075717958635247711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3521568100957278180330281 2641176075717958635247711)
      ·
        refine ⟨3961764113576937952871567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641176075717958635247711 3961764113576937952871567)
        ·
          refine ⟨5942646170365406929307351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961764113576937952871567 5942646170365406929307351)
          ·
            refine ⟨8913969255548110393961027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5942646170365406929307351 8913969255548110393961027)
            ·
              refine ⟨13370953883322165590941541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8913969255548110393961027 13370953883322165590941541)
              ·
                refine ⟨2507053853122906048301539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13370953883322165590941541 2507053853122906048301539)
                ·
                  refine ⟨3760580779684359072452309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507053853122906048301539 3760580779684359072452309)
                  ·
                    refine ⟨88138612023852165760601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3760580779684359072452309 88138612023852165760601)
                    ·
                      rfl

theorem cell23_514948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_514948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514948 prefixEnd_514948 := by exact prefixLift 514948
  have htrace : WordTrace (prefixWord ++ tailWord_514948) baseStart_514948 baseEnd_514948 := by
    simpa [prefixWord, tailWord_514948, baseEnd_514948] using wordTrace_append hprefix tailTrace_514948
  have hstable : (prefixWord ++ tailWord_514948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514948).length < 2 ^ (prefixWord ++ tailWord_514948).sum := by decide
  have hdescent : baseEnd_514948 < baseStart_514948 := by decide
  rcases family_descends (prefixWord ++ tailWord_514948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514965 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_514965 : Nat := 118140960795 + 514965 * 2 ^ 59
def prefixEnd_514965 : Nat := 4983230072969 + 3 ^ 40 * 514965 * 2
def baseEnd_514965 : Nat := 88141521747560976923075

theorem tailTrace_514965 : CollatzResearch.WordTrace tailWord_514965 prefixEnd_514965 88141521747560976923075 := by
  unfold tailWord_514965
  simp only [CollatzResearch.WordTrace]
  refine ⟨18782316579377228865130349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12521544386251485910086899 18782316579377228865130349)
  ·
    refine ⟨7043368717266460824423881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18782316579377228865130349 7043368717266460824423881)
    ·
      refine ⟨5282526537949845618317911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7043368717266460824423881 5282526537949845618317911)
      ·
        refine ⟨7923789806924768427476867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5282526537949845618317911 7923789806924768427476867)
        ·
          refine ⟨11885684710387152641215301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7923789806924768427476867 11885684710387152641215301)
          ·
            refine ⟨2228565883197591120227869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11885684710387152641215301 2228565883197591120227869)
            ·
              refine ⟨835712206199096670085451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2228565883197591120227869 835712206199096670085451)
              ·
                refine ⟨1253568309298645005128177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835712206199096670085451 1253568309298645005128177)
                ·
                  refine ⟨940176231973983753846133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1253568309298645005128177 940176231973983753846133)
                  ·
                    refine ⟨88141521747560976923075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 940176231973983753846133 88141521747560976923075)
                    ·
                      rfl

theorem cell23_514965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_514965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514965 prefixEnd_514965 := by exact prefixLift 514965
  have htrace : WordTrace (prefixWord ++ tailWord_514965) baseStart_514965 baseEnd_514965 := by
    simpa [prefixWord, tailWord_514965, baseEnd_514965] using wordTrace_append hprefix tailTrace_514965
  have hstable : (prefixWord ++ tailWord_514965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514965).length < 2 ^ (prefixWord ++ tailWord_514965).sum := by decide
  have hdescent : baseEnd_514965 < baseStart_514965 := by decide
  rcases family_descends (prefixWord ++ tailWord_514965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514985 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 4, 4, 2]
def baseStart_514985 : Nat := 118140960795 + 514985 * 2 ^ 59
def prefixEnd_514985 : Nat := 4983230072969 + 3 ^ 40 * 514985 * 2
def baseEnd_514985 : Nat := 264434834855772852519133

theorem tailTrace_514985 : CollatzResearch.WordTrace tailWord_514985 prefixEnd_514985 264434834855772852519133 := by
  unfold tailWord_514985
  simp only [CollatzResearch.WordTrace]
  refine ⟨18783046039304772280858409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12522030692869848187238939 18783046039304772280858409)
  ·
    refine ⟨14087284529478579210643807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18783046039304772280858409 14087284529478579210643807)
    ·
      refine ⟨21130926794217868815965711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14087284529478579210643807 21130926794217868815965711)
      ·
        refine ⟨31696390191326803223948567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21130926794217868815965711 31696390191326803223948567)
        ·
          refine ⟨47544585286990204835922851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31696390191326803223948567 47544585286990204835922851)
          ·
            refine ⟨71316877930485307253884277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47544585286990204835922851 71316877930485307253884277)
            ·
              refine ⟨6685957305982997555051651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71316877930485307253884277 6685957305982997555051651)
              ·
                refine ⟨10028935958974496332577477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6685957305982997555051651 10028935958974496332577477)
                ·
                  refine ⟨1880425492307718062358277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10028935958974496332577477 1880425492307718062358277)
                  ·
                    refine ⟨352579779807697136692177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1880425492307718062358277 352579779807697136692177)
                    ·
                      refine ⟨264434834855772852519133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352579779807697136692177 264434834855772852519133)
                      ·
                        rfl

theorem cell23_514985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 4, 2].length) (baseStart_514985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_514985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_514985 prefixEnd_514985 := by exact prefixLift 514985
  have htrace : WordTrace (prefixWord ++ tailWord_514985) baseStart_514985 baseEnd_514985 := by
    simpa [prefixWord, tailWord_514985, baseEnd_514985] using wordTrace_append hprefix tailTrace_514985
  have hstable : (prefixWord ++ tailWord_514985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514985).length < 2 ^ (prefixWord ++ tailWord_514985).sum := by decide
  have hdescent : baseEnd_514985 < baseStart_514985 := by decide
  rcases family_descends (prefixWord ++ tailWord_514985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515042 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 8]
def baseStart_515042 : Nat := 118140960795 + 515042 * 2 ^ 59
def prefixEnd_515042 : Nat := 4983230072969 + 3 ^ 40 * 515042 * 2
def baseEnd_515042 : Nat := 29384900361453236611819

theorem tailTrace_515042 : CollatzResearch.WordTrace tailWord_515042 prefixEnd_515042 29384900361453236611819 := by
  unfold tailWord_515042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696281250024567753920845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12523416666732180677122253 4696281250024567753920845)
  ·
    refine ⟨1761105468759212907720317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4696281250024567753920845 1761105468759212907720317)
    ·
      refine ⟨660414550784704840395119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1761105468759212907720317 660414550784704840395119)
      ·
        refine ⟨990621826177057260592679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660414550784704840395119 990621826177057260592679)
        ·
          refine ⟨1485932739265585890889019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990621826177057260592679 1485932739265585890889019)
          ·
            refine ⟨2228899108898378836333529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485932739265585890889019 2228899108898378836333529)
            ·
              refine ⟨1671674331673784127250147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228899108898378836333529 1671674331673784127250147)
              ·
                refine ⟨2507511497510676190875221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671674331673784127250147 2507511497510676190875221)
                ·
                  refine ⟨29384900361453236611819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2507511497510676190875221 29384900361453236611819)
                  ·
                    rfl

theorem cell23_515042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_515042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515042 prefixEnd_515042 := by exact prefixLift 515042
  have htrace : WordTrace (prefixWord ++ tailWord_515042) baseStart_515042 baseEnd_515042 := by
    simpa [prefixWord, tailWord_515042, baseEnd_515042] using wordTrace_append hprefix tailTrace_515042
  have hstable : (prefixWord ++ tailWord_515042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515042).length < 2 ^ (prefixWord ++ tailWord_515042).sum := by decide
  have hdescent : baseEnd_515042 < baseStart_515042 := by decide
  rcases family_descends (prefixWord ++ tailWord_515042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515079 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_515079 : Nat := 118140960795 + 515079 * 2 ^ 59
def prefixEnd_515079 : Nat := 4983230072969 + 3 ^ 40 * 515079 * 2
def baseEnd_515079 : Nat := 264483102037295484743701

theorem tailTrace_515079 : CollatzResearch.WordTrace tailWord_515079 prefixEnd_515079 264483102037295484743701 := by
  unfold tailWord_515079
  simp only [CollatzResearch.WordTrace]
  refine ⟨18786474500964226334780291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12524316333976150889853527 18786474500964226334780291)
  ·
    refine ⟨28179711751446339502170437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18786474500964226334780291 28179711751446339502170437)
    ·
      refine ⟨5283695953396188656656957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28179711751446339502170437 5283695953396188656656957)
      ·
        refine ⟨1981385982523570746246359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5283695953396188656656957 1981385982523570746246359)
        ·
          refine ⟨2972078973785356119369539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981385982523570746246359 2972078973785356119369539)
          ·
            refine ⟨4458118460678034179054309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972078973785356119369539 4458118460678034179054309)
            ·
              refine ⟨835897211377131408572683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4458118460678034179054309 835897211377131408572683)
              ·
                refine ⟨1253845817065697112859025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835897211377131408572683 1253845817065697112859025)
                ·
                  refine ⟨940384362799272834644269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1253845817065697112859025 940384362799272834644269)
                  ·
                    refine ⟨352644136049727312991601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 940384362799272834644269 352644136049727312991601)
                    ·
                      refine ⟨264483102037295484743701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352644136049727312991601 264483102037295484743701)
                      ·
                        rfl

theorem cell23_515079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_515079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515079 prefixEnd_515079 := by exact prefixLift 515079
  have htrace : WordTrace (prefixWord ++ tailWord_515079) baseStart_515079 baseEnd_515079 := by
    simpa [prefixWord, tailWord_515079, baseEnd_515079] using wordTrace_append hprefix tailTrace_515079
  have hstable : (prefixWord ++ tailWord_515079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515079).length < 2 ^ (prefixWord ++ tailWord_515079).sum := by decide
  have hdescent : baseEnd_515079 < baseStart_515079 := by decide
  rcases family_descends (prefixWord ++ tailWord_515079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515103 : List Nat := [1, 1, 2, 4, 1, 5, 2, 2, 1, 1, 3]
def baseStart_515103 : Nat := 118140960795 + 515103 * 2 ^ 59
def prefixEnd_515103 : Nat := 4983230072969 + 3 ^ 40 * 515103 * 2
def baseEnd_515103 : Nat := 264495425573003390843591

theorem tailTrace_515103 : CollatzResearch.WordTrace tailWord_515103 prefixEnd_515103 264495425573003390843591 := by
  unfold tailWord_515103
  simp only [CollatzResearch.WordTrace]
  refine ⟨18787349852877278433653963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12524899901918185622435975 18787349852877278433653963)
  ·
    refine ⟨28181024779315917650480945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18787349852877278433653963 28181024779315917650480945)
    ·
      refine ⟨21135768584486938237860709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28181024779315917650480945 21135768584486938237860709)
      ·
        refine ⟨3962956609591300919598883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21135768584486938237860709 3962956609591300919598883)
        ·
          refine ⟨5944434914386951379398325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962956609591300919598883 5944434914386951379398325)
          ·
            refine ⟨557290773223776691818593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5944434914386951379398325 557290773223776691818593)
            ·
              refine ⟨417968079917832518863945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557290773223776691818593 417968079917832518863945)
              ·
                refine ⟨313476059938374389147959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417968079917832518863945 313476059938374389147959)
                ·
                  refine ⟨470214089907561583721939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313476059938374389147959 470214089907561583721939)
                  ·
                    refine ⟨705321134861342375582909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470214089907561583721939 705321134861342375582909)
                    ·
                      refine ⟨264495425573003390843591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 705321134861342375582909 264495425573003390843591)
                      ·
                        rfl

theorem cell23_515103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_515103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515103 prefixEnd_515103 := by exact prefixLift 515103
  have htrace : WordTrace (prefixWord ++ tailWord_515103) baseStart_515103 baseEnd_515103 := by
    simpa [prefixWord, tailWord_515103, baseEnd_515103] using wordTrace_append hprefix tailTrace_515103
  have hstable : (prefixWord ++ tailWord_515103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515103).length < 2 ^ (prefixWord ++ tailWord_515103).sum := by decide
  have hdescent : baseEnd_515103 < baseStart_515103 := by decide
  rcases family_descends (prefixWord ++ tailWord_515103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515109 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 3, 2, 2]
def baseStart_515109 : Nat := 118140960795 + 515109 * 2 ^ 59
def prefixEnd_515109 : Nat := 4983230072969 + 3 ^ 40 * 515109 * 2
def baseEnd_515109 : Nat := 264498506456930367368563

theorem tailTrace_515109 : CollatzResearch.WordTrace tailWord_515109 prefixEnd_515109 264498506456930367368563 := by
  unfold tailWord_515109
  simp only [CollatzResearch.WordTrace]
  refine ⟨18787568690855541458372381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12525045793903694305581587 18787568690855541458372381)
  ·
    refine ⟨7045338259070828046889643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18787568690855541458372381 7045338259070828046889643)
    ·
      refine ⟨10568007388606242070334465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7045338259070828046889643 10568007388606242070334465)
      ·
        refine ⟨7926005541454681552750849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10568007388606242070334465 7926005541454681552750849)
        ·
          refine ⟨5944504156091011164563137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7926005541454681552750849 5944504156091011164563137)
          ·
            refine ⟨4458378117068258373422353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944504156091011164563137 4458378117068258373422353)
            ·
              refine ⟨3343783587801193780066765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458378117068258373422353 3343783587801193780066765)
              ·
                refine ⟨1253918845425447667525037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3343783587801193780066765 1253918845425447667525037)
                ·
                  refine ⟨470219567034542875321889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253918845425447667525037 470219567034542875321889)
                  ·
                    refine ⟨352664675275907156491417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470219567034542875321889 352664675275907156491417)
                    ·
                      refine ⟨264498506456930367368563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352664675275907156491417 264498506456930367368563)
                      ·
                        rfl

theorem cell23_515109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_515109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515109 prefixEnd_515109 := by exact prefixLift 515109
  have htrace : WordTrace (prefixWord ++ tailWord_515109) baseStart_515109 baseEnd_515109 := by
    simpa [prefixWord, tailWord_515109, baseEnd_515109] using wordTrace_append hprefix tailTrace_515109
  have hstable : (prefixWord ++ tailWord_515109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515109).length < 2 ^ (prefixWord ++ tailWord_515109).sum := by decide
  have hdescent : baseEnd_515109 < baseStart_515109 := by decide
  rcases family_descends (prefixWord ++ tailWord_515109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515122 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_515122 : Nat := 118140960795 + 515122 * 2 ^ 59
def prefixEnd_515122 : Nat := 4983230072969 + 3 ^ 40 * 515122 * 2
def baseEnd_515122 : Nat := 264505181705438816506003

theorem tailTrace_515122 : CollatzResearch.WordTrace tailWord_515122 prefixEnd_515122 264505181705438816506003 := by
  unfold tailWord_515122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697010709952111169648905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12525361893205629785730413 4697010709952111169648905)
  ·
    refine ⟨3522758032464083377236679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4697010709952111169648905 3522758032464083377236679)
    ·
      refine ⟨5284137048696125065855019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522758032464083377236679 5284137048696125065855019)
      ·
        refine ⟨7926205573044187598782529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284137048696125065855019 7926205573044187598782529)
        ·
          refine ⟨5944654179783140699086897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7926205573044187598782529 5944654179783140699086897)
          ·
            refine ⟨4458490634837355524315173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944654179783140699086897 4458490634837355524315173)
            ·
              refine ⟨835966994032004160809095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4458490634837355524315173 835966994032004160809095)
              ·
                refine ⟨1253950491048006241213643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835966994032004160809095 1253950491048006241213643)
                ·
                  refine ⟨1880925736572009361820465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253950491048006241213643 1880925736572009361820465)
                  ·
                    refine ⟨1410694302429007021365349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1880925736572009361820465 1410694302429007021365349)
                    ·
                      refine ⟨264505181705438816506003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1410694302429007021365349 264505181705438816506003)
                      ·
                        rfl

theorem cell23_515122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_515122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515122 prefixEnd_515122 := by exact prefixLift 515122
  have htrace : WordTrace (prefixWord ++ tailWord_515122) baseStart_515122 baseEnd_515122 := by
    simpa [prefixWord, tailWord_515122, baseEnd_515122] using wordTrace_append hprefix tailTrace_515122
  have hstable : (prefixWord ++ tailWord_515122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515122).length < 2 ^ (prefixWord ++ tailWord_515122).sum := by decide
  have hdescent : baseEnd_515122 < baseStart_515122 := by decide
  rcases family_descends (prefixWord ++ tailWord_515122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515126 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_515126 : Nat := 118140960795 + 515126 * 2 ^ 59
def prefixEnd_515126 : Nat := 4983230072969 + 3 ^ 40 * 515126 * 2
def baseEnd_515126 : Nat := 264507235628056800855985

theorem tailTrace_515126 : CollatzResearch.WordTrace tailWord_515126 prefixEnd_515126 264507235628056800855985 := by
  unfold tailWord_515126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174261795737122085108827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12525459154529302241160821 1174261795737122085108827)
  ·
    refine ⟨1761392693605683127663241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1174261795737122085108827 1761392693605683127663241)
    ·
      refine ⟨1321044520204262345747431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1761392693605683127663241 1321044520204262345747431)
      ·
        refine ⟨1981566780306393518621147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321044520204262345747431 1981566780306393518621147)
        ·
          refine ⟨2972350170459590277931721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981566780306393518621147 2972350170459590277931721)
          ·
            refine ⟨2229262627844692708448791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2972350170459590277931721 2229262627844692708448791)
            ·
              refine ⟨3343893941767039062673187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229262627844692708448791 3343893941767039062673187)
              ·
                refine ⟨5015840912650558594009781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343893941767039062673187 5015840912650558594009781)
                ·
                  refine ⟨470235085560989868188417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5015840912650558594009781 470235085560989868188417)
                  ·
                    refine ⟨352676314170742401141313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470235085560989868188417 352676314170742401141313)
                    ·
                      refine ⟨264507235628056800855985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352676314170742401141313 264507235628056800855985)
                      ·
                        rfl

theorem cell23_515126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_515126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515126 prefixEnd_515126 := by exact prefixLift 515126
  have htrace : WordTrace (prefixWord ++ tailWord_515126) baseStart_515126 baseEnd_515126 := by
    simpa [prefixWord, tailWord_515126, baseEnd_515126] using wordTrace_append hprefix tailTrace_515126
  have hstable : (prefixWord ++ tailWord_515126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515126).length < 2 ^ (prefixWord ++ tailWord_515126).sum := by decide
  have hdescent : baseEnd_515126 < baseStart_515126 := by decide
  rcases family_descends (prefixWord ++ tailWord_515126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515132 : List Nat := [2, 2, 2, 2, 2, 3, 3, 7]
def baseStart_515132 : Nat := 118140960795 + 515132 * 2 ^ 59
def prefixEnd_515132 : Nat := 4983230072969 + 3 ^ 40 * 515132 * 2
def baseEnd_515132 : Nat := 9796678389332732495591

theorem tailTrace_515132 : CollatzResearch.WordTrace tailWord_515132 prefixEnd_515132 9796678389332732495591 := by
  unfold tailWord_515132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394203784886108193229825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12525605046514810924306433 9394203784886108193229825)
  ·
    refine ⟨7045652838664581144922369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9394203784886108193229825 7045652838664581144922369)
    ·
      refine ⟨5284239628998435858691777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7045652838664581144922369 5284239628998435858691777)
      ·
        refine ⟨3963179721748826894018833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5284239628998435858691777 3963179721748826894018833)
        ·
          refine ⟨2972384791311620170514125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3963179721748826894018833 2972384791311620170514125)
          ·
            refine ⟨1114644296741857563942797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2972384791311620170514125 1114644296741857563942797)
            ·
              refine ⟨417991611278196586478549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1114644296741857563942797 417991611278196586478549)
              ·
                refine ⟨9796678389332732495591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 417991611278196586478549 9796678389332732495591)
                ·
                  rfl

theorem cell23_515132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 7].length) (baseStart_515132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515132 prefixEnd_515132 := by exact prefixLift 515132
  have htrace : WordTrace (prefixWord ++ tailWord_515132) baseStart_515132 baseEnd_515132 := by
    simpa [prefixWord, tailWord_515132, baseEnd_515132] using wordTrace_append hprefix tailTrace_515132
  have hstable : (prefixWord ++ tailWord_515132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515132).length < 2 ^ (prefixWord ++ tailWord_515132).sum := by decide
  have hdescent : baseEnd_515132 < baseStart_515132 := by decide
  rcases family_descends (prefixWord ++ tailWord_515132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515143 : List Nat := [1, 1, 4, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_515143 : Nat := 118140960795 + 515143 * 2 ^ 59
def prefixEnd_515143 : Nat := 4983230072969 + 3 ^ 40 * 515143 * 2
def baseEnd_515143 : Nat := 264515964799183234343407

theorem tailTrace_515143 : CollatzResearch.WordTrace tailWord_515143 prefixEnd_515143 264515964799183234343407 := by
  unfold tailWord_515143
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788808772732365265110083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12525872515154910176740055 18788808772732365265110083)
  ·
    refine ⟨28183213159098547897665125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18788808772732365265110083 28183213159098547897665125)
    ·
      refine ⟨5284352467330977730812211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28183213159098547897665125 5284352467330977730812211)
      ·
        refine ⟨7926528700996466596218317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284352467330977730812211 7926528700996466596218317)
        ·
          refine ⟨2972448262873674973581869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7926528700996466596218317 2972448262873674973581869)
          ·
            refine ⟨1114668098577628115093201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2972448262873674973581869 1114668098577628115093201)
            ·
              refine ⟨836001073933221086319901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114668098577628115093201 836001073933221086319901)
              ·
                refine ⟨313500402724957907369963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836001073933221086319901 313500402724957907369963)
                ·
                  refine ⟨470250604087436861054945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313500402724957907369963 470250604087436861054945)
                  ·
                    refine ⟨352687953065577645791209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470250604087436861054945 352687953065577645791209)
                    ·
                      refine ⟨264515964799183234343407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352687953065577645791209 264515964799183234343407)
                      ·
                        rfl

theorem cell23_515143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_515143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515143 prefixEnd_515143 := by exact prefixLift 515143
  have htrace : WordTrace (prefixWord ++ tailWord_515143) baseStart_515143 baseEnd_515143 := by
    simpa [prefixWord, tailWord_515143, baseEnd_515143] using wordTrace_append hprefix tailTrace_515143
  have hstable : (prefixWord ++ tailWord_515143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515143).length < 2 ^ (prefixWord ++ tailWord_515143).sum := by decide
  have hdescent : baseEnd_515143 < baseStart_515143 := by decide
  rcases family_descends (prefixWord ++ tailWord_515143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515186 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_515186 : Nat := 118140960795 + 515186 * 2 ^ 59
def prefixEnd_515186 : Nat := 4983230072969 + 3 ^ 40 * 515186 * 2
def baseEnd_515186 : Nat := 264538044467326566105709

theorem tailTrace_515186 : CollatzResearch.WordTrace tailWord_515186 prefixEnd_515186 264538044467326566105709 := by
  unfold tailWord_515186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697594277894145902231353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12526918074384389072616941 4697594277894145902231353)
  ·
    refine ⟨3523195708420609426673515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4697594277894145902231353 3523195708420609426673515)
    ·
      refine ⟨5284793562630914140010273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523195708420609426673515 5284793562630914140010273)
      ·
        refine ⟨3963595171973185605007705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5284793562630914140010273 3963595171973185605007705)
        ·
          refine ⟨2972696378979889203755779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3963595171973185605007705 2972696378979889203755779)
          ·
            refine ⟨4459044568469833805633669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972696378979889203755779 4459044568469833805633669)
            ·
              refine ⟨836070856588093838556313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4459044568469833805633669 836070856588093838556313)
              ·
                refine ⟨627053142441070378917235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836070856588093838556313 627053142441070378917235)
                ·
                  refine ⟨940579713661605568375853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627053142441070378917235 940579713661605568375853)
                  ·
                    refine ⟨352717392623102088140945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 940579713661605568375853 352717392623102088140945)
                    ·
                      refine ⟨264538044467326566105709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352717392623102088140945 264538044467326566105709)
                      ·
                        rfl

theorem cell23_515186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_515186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515186 prefixEnd_515186 := by exact prefixLift 515186
  have htrace : WordTrace (prefixWord ++ tailWord_515186) baseStart_515186 baseEnd_515186 := by
    simpa [prefixWord, tailWord_515186, baseEnd_515186] using wordTrace_append hprefix tailTrace_515186
  have hstable : (prefixWord ++ tailWord_515186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515186).length < 2 ^ (prefixWord ++ tailWord_515186).sum := by decide
  have hdescent : baseEnd_515186 < baseStart_515186 := by decide
  rcases family_descends (prefixWord ++ tailWord_515186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515195 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4]
def baseStart_515195 : Nat := 118140960795 + 515195 * 2 ^ 59
def prefixEnd_515195 : Nat := 4983230072969 + 3 ^ 40 * 515195 * 2
def baseEnd_515195 : Nat := 264542665793217030893167

theorem tailTrace_515195 : CollatzResearch.WordTrace tailWord_515195 prefixEnd_515195 264542665793217030893167 := by
  unfold tailWord_515195
  simp only [CollatzResearch.WordTrace]
  refine ⟨18790705368543978146003039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12527136912362652097335359 18790705368543978146003039)
  ·
    refine ⟨28186058052815967219004559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18790705368543978146003039 28186058052815967219004559)
    ·
      refine ⟨42279087079223950828506839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28186058052815967219004559 42279087079223950828506839)
      ·
        refine ⟨63418630618835926242760259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42279087079223950828506839 63418630618835926242760259)
        ·
          refine ⟨95127945928253889364140389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63418630618835926242760259 95127945928253889364140389)
          ·
            refine ⟨17836489861547604255776323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95127945928253889364140389 17836489861547604255776323)
            ·
              refine ⟨26754734792321406383664485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17836489861547604255776323 26754734792321406383664485)
              ·
                refine ⟨5016512773560263696937091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26754734792321406383664485 5016512773560263696937091)
                ·
                  refine ⟨7524769160340395545405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016512773560263696937091 7524769160340395545405637)
                  ·
                    refine ⟨1410894217563824164763557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7524769160340395545405637 1410894217563824164763557)
                    ·
                      refine ⟨264542665793217030893167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1410894217563824164763557 264542665793217030893167)
                      ·
                        rfl

theorem cell23_515195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_515195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515195 prefixEnd_515195 := by exact prefixLift 515195
  have htrace : WordTrace (prefixWord ++ tailWord_515195) baseStart_515195 baseEnd_515195 := by
    simpa [prefixWord, tailWord_515195, baseEnd_515195] using wordTrace_append hprefix tailTrace_515195
  have hstable : (prefixWord ++ tailWord_515195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515195).length < 2 ^ (prefixWord ++ tailWord_515195).sum := by decide
  have hdescent : baseEnd_515195 < baseStart_515195 := by decide
  rcases family_descends (prefixWord ++ tailWord_515195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515232 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3]
def baseStart_515232 : Nat := 118140960795 + 515232 * 2 ^ 59
def prefixEnd_515232 : Nat := 4983230072969 + 3 ^ 40 * 515232 * 2
def baseEnd_515232 : Nat := 264561664577433386130497

theorem tailTrace_515232 : CollatzResearch.WordTrace tailWord_515232 prefixEnd_515232 264561664577433386130497 := by
  unfold tailWord_515232
  simp only [CollatzResearch.WordTrace]
  refine ⟨9396027434704966732549975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12528036579606622310066633 9396027434704966732549975)
  ·
    refine ⟨14094041152057450098824963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9396027434704966732549975 14094041152057450098824963)
    ·
      refine ⟨21141061728086175148237445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14094041152057450098824963 21141061728086175148237445)
      ·
        refine ⟨3963949074016157840294521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21141061728086175148237445 3963949074016157840294521)
        ·
          refine ⟨2972961805512118380220891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3963949074016157840294521 2972961805512118380220891)
          ·
            refine ⟨4459442708268177570331337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972961805512118380220891 4459442708268177570331337)
            ·
              refine ⟨3344582031201133177748503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459442708268177570331337 3344582031201133177748503)
              ·
                refine ⟨5016873046801699766622755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344582031201133177748503 5016873046801699766622755)
                ·
                  refine ⟨7525309570202549649934133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5016873046801699766622755 7525309570202549649934133)
                  ·
                    refine ⟨705497772206489029681325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7525309570202549649934133 705497772206489029681325)
                    ·
                      refine ⟨264561664577433386130497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 705497772206489029681325 264561664577433386130497)
                      ·
                        rfl

theorem cell23_515232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_515232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515232 prefixEnd_515232 := by exact prefixLift 515232
  have htrace : WordTrace (prefixWord ++ tailWord_515232) baseStart_515232 baseEnd_515232 := by
    simpa [prefixWord, tailWord_515232, baseEnd_515232] using wordTrace_append hprefix tailTrace_515232
  have hstable : (prefixWord ++ tailWord_515232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515232).length < 2 ^ (prefixWord ++ tailWord_515232).sum := by decide
  have hdescent : baseEnd_515232 < baseStart_515232 := by decide
  rcases family_descends (prefixWord ++ tailWord_515232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515235 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 3, 7]
def baseStart_515235 : Nat := 118140960795 + 515235 * 2 ^ 59
def prefixEnd_515235 : Nat := 4983230072969 + 3 ^ 40 * 515235 * 2
def baseEnd_515235 : Nat := 88187735006465624797661

theorem tailTrace_515235 : CollatzResearch.WordTrace tailWord_515235 prefixEnd_515235 88187735006465624797661 := by
  unfold tailWord_515235
  simp only [CollatzResearch.WordTrace]
  refine ⟨18792164288399064977459159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12528109525599376651639439 18792164288399064977459159)
  ·
    refine ⟨28188246432598597466188739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18792164288399064977459159 28188246432598597466188739)
    ·
      refine ⟨42282369648897896199283109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28188246432598597466188739 42282369648897896199283109)
      ·
        refine ⟨7927944309168355537365583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42282369648897896199283109 7927944309168355537365583)
        ·
          refine ⟨11891916463752533306048375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927944309168355537365583 11891916463752533306048375)
          ·
            refine ⟨17837874695628799959072563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11891916463752533306048375 17837874695628799959072563)
            ·
              refine ⟨26756812043443199938608845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17837874695628799959072563 26756812043443199938608845)
              ·
                refine ⟨10033804516291199976978317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26756812043443199938608845 10033804516291199976978317)
                ·
                  refine ⟨3762676693609199991366869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10033804516291199976978317 3762676693609199991366869)
                  ·
                    refine ⟨88187735006465624797661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3762676693609199991366869 88187735006465624797661)
                    ·
                      rfl

theorem cell23_515235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 7].length) (baseStart_515235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515235 prefixEnd_515235 := by exact prefixLift 515235
  have htrace : WordTrace (prefixWord ++ tailWord_515235) baseStart_515235 baseEnd_515235 := by
    simpa [prefixWord, tailWord_515235, baseEnd_515235] using wordTrace_append hprefix tailTrace_515235
  have hstable : (prefixWord ++ tailWord_515235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515235).length < 2 ^ (prefixWord ++ tailWord_515235).sum := by decide
  have hdescent : baseEnd_515235 < baseStart_515235 := by decide
  rcases family_descends (prefixWord ++ tailWord_515235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515303 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 2, 5]
def baseStart_515303 : Nat := 118140960795 + 515303 * 2 ^ 59
def prefixEnd_515303 : Nat := 4983230072969 + 3 ^ 40 * 515303 * 2
def baseEnd_515303 : Nat := 88199373901300869447557

theorem tailTrace_515303 : CollatzResearch.WordTrace tailWord_515303 prefixEnd_515303 88199373901300869447557 := by
  unfold tailWord_515303
  simp only [CollatzResearch.WordTrace]
  refine ⟨18794644452152712590934563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12529762968101808393956375 18794644452152712590934563)
  ·
    refine ⟨28191966678229068886401845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18794644452152712590934563 28191966678229068886401845)
    ·
      refine ⟨2642996876083975208100173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28191966678229068886401845 2642996876083975208100173)
      ·
        refine ⟨991123828531490703037565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2642996876083975208100173 991123828531490703037565)
        ·
          refine ⟨371671435699309013639087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 991123828531490703037565 371671435699309013639087)
          ·
            refine ⟨557507153548963520458631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371671435699309013639087 557507153548963520458631)
            ·
              refine ⟨836260730323445280687947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557507153548963520458631 836260730323445280687947)
              ·
                refine ⟨1254391095485167921031921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836260730323445280687947 1254391095485167921031921)
                ·
                  refine ⟨940793321613875940773941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1254391095485167921031921 940793321613875940773941)
                  ·
                    refine ⟨88199373901300869447557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 940793321613875940773941 88199373901300869447557)
                    ·
                      rfl

theorem cell23_515303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_515303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515303 prefixEnd_515303 := by exact prefixLift 515303
  have htrace : WordTrace (prefixWord ++ tailWord_515303) baseStart_515303 baseEnd_515303 := by
    simpa [prefixWord, tailWord_515303, baseEnd_515303] using wordTrace_append hprefix tailTrace_515303
  have hstable : (prefixWord ++ tailWord_515303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515303).length < 2 ^ (prefixWord ++ tailWord_515303).sum := by decide
  have hdescent : baseEnd_515303 < baseStart_515303 := by decide
  rcases family_descends (prefixWord ++ tailWord_515303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515306 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_515306 : Nat := 118140960795 + 515306 * 2 ^ 59
def prefixEnd_515306 : Nat := 4983230072969 + 3 ^ 40 * 515306 * 2
def baseEnd_515306 : Nat := 264599662145866096605157

theorem tailTrace_515306 : CollatzResearch.WordTrace tailWord_515306 prefixEnd_515306 264599662145866096605157 := by
  unfold tailWord_515306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698688467785461025823443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12529835914094562735529181 4698688467785461025823443)
  ·
    refine ⟨7048032701678191538735165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4698688467785461025823443 7048032701678191538735165)
    ·
      refine ⟨2643012263129321827025687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7048032701678191538735165 2643012263129321827025687)
      ·
        refine ⟨3964518394693982740538531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643012263129321827025687 3964518394693982740538531)
        ·
          refine ⟨5946777592040974110807797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964518394693982740538531 5946777592040974110807797)
          ·
            refine ⟨557510399253841322888231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5946777592040974110807797 557510399253841322888231)
            ·
              refine ⟨836265598880761984332347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557510399253841322888231 836265598880761984332347)
              ·
                refine ⟨1254398398321142976498521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836265598880761984332347 1254398398321142976498521)
                ·
                  refine ⟨940798798740857232373891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1254398398321142976498521 940798798740857232373891)
                  ·
                    refine ⟨1411198198111285848560837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 940798798740857232373891 1411198198111285848560837)
                    ·
                      refine ⟨264599662145866096605157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1411198198111285848560837 264599662145866096605157)
                      ·
                        rfl

theorem cell23_515306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_515306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515306 prefixEnd_515306 := by exact prefixLift 515306
  have htrace : WordTrace (prefixWord ++ tailWord_515306) baseStart_515306 baseEnd_515306 := by
    simpa [prefixWord, tailWord_515306, baseEnd_515306] using wordTrace_append hprefix tailTrace_515306
  have hstable : (prefixWord ++ tailWord_515306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515306).length < 2 ^ (prefixWord ++ tailWord_515306).sum := by decide
  have hdescent : baseEnd_515306 < baseStart_515306 := by decide
  rcases family_descends (prefixWord ++ tailWord_515306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515329 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 6]
def baseStart_515329 : Nat := 118140960795 + 515329 * 2 ^ 59
def prefixEnd_515329 : Nat := 4983230072969 + 3 ^ 40 * 515329 * 2
def baseEnd_515329 : Nat := 29401274688991056290839

theorem tailTrace_515329 : CollatzResearch.WordTrace tailWord_515329 prefixEnd_515329 29401274688991056290839 := by
  unfold tailWord_515329
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795592750058519031381041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12530395166705679354254027 18795592750058519031381041)
  ·
    refine ⟨14096694562543889273535781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18795592750058519031381041 14096694562543889273535781)
    ·
      refine ⟨2643130230476979238787959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14096694562543889273535781 2643130230476979238787959)
      ·
        refine ⟨3964695345715468858181939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643130230476979238787959 3964695345715468858181939)
        ·
          refine ⟨5947043018573203287272909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964695345715468858181939 5947043018573203287272909)
          ·
            refine ⟨2230141131964951232727341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5947043018573203287272909 2230141131964951232727341)
            ·
              refine ⟨836302924486856712272753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2230141131964951232727341 836302924486856712272753)
              ·
                refine ⟨627227193365142534204565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836302924486856712272753 627227193365142534204565)
                ·
                  refine ⟨29401274688991056290839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 627227193365142534204565 29401274688991056290839)
                  ·
                    rfl

theorem cell23_515329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 6].length) (baseStart_515329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515329 prefixEnd_515329 := by exact prefixLift 515329
  have htrace : WordTrace (prefixWord ++ tailWord_515329) baseStart_515329 baseEnd_515329 := by
    simpa [prefixWord, tailWord_515329, baseEnd_515329] using wordTrace_append hprefix tailTrace_515329
  have hstable : (prefixWord ++ tailWord_515329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515329).length < 2 ^ (prefixWord ++ tailWord_515329).sum := by decide
  have hdescent : baseEnd_515329 < baseStart_515329 := by decide
  rcases family_descends (prefixWord ++ tailWord_515329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515356 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_515356 : Nat := 118140960795 + 515356 * 2 ^ 59
def prefixEnd_515356 : Nat := 4983230072969 + 3 ^ 40 * 515356 * 2
def baseEnd_515356 : Nat := 264625336178590900979927

theorem tailTrace_515356 : CollatzResearch.WordTrace tailWord_515356 prefixEnd_515356 264625336178590900979927 := by
  unfold tailWord_515356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398288760480351321306961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12531051680640468428409281 9398288760480351321306961)
  ·
    refine ⟨7048716570360263490980221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9398288760480351321306961 7048716570360263490980221)
    ·
      refine ⟨2643268713885098809117583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7048716570360263490980221 2643268713885098809117583)
      ·
        refine ⟨3964903070827648213676375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643268713885098809117583 3964903070827648213676375)
        ·
          refine ⟨5947354606241472320514563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964903070827648213676375 5947354606241472320514563)
          ·
            refine ⟨8921031909362208480771845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947354606241472320514563 8921031909362208480771845)
            ·
              refine ⟨1672693483005414090144721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8921031909362208480771845 1672693483005414090144721)
              ·
                refine ⟨1254520112254060567608541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672693483005414090144721 1254520112254060567608541)
                ·
                  refine ⟨470445042095272712853203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254520112254060567608541 470445042095272712853203)
                  ·
                    refine ⟨705667563142909069279805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470445042095272712853203 705667563142909069279805)
                    ·
                      refine ⟨264625336178590900979927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 705667563142909069279805 264625336178590900979927)
                      ·
                        rfl

theorem cell23_515356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_515356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515356 prefixEnd_515356 := by exact prefixLift 515356
  have htrace : WordTrace (prefixWord ++ tailWord_515356) baseStart_515356 baseEnd_515356 := by
    simpa [prefixWord, tailWord_515356, baseEnd_515356] using wordTrace_append hprefix tailTrace_515356
  have hstable : (prefixWord ++ tailWord_515356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515356).length < 2 ^ (prefixWord ++ tailWord_515356).sum := by decide
  have hdescent : baseEnd_515356 < baseStart_515356 := by decide
  rcases family_descends (prefixWord ++ tailWord_515356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515372 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_515372 : Nat := 118140960795 + 515372 * 2 ^ 59
def prefixEnd_515372 : Nat := 4983230072969 + 3 ^ 40 * 515372 * 2
def baseEnd_515372 : Nat := 88211183956354279459951

theorem tailTrace_515372 : CollatzResearch.WordTrace tailWord_515372 prefixEnd_515372 88211183956354279459951 := by
  unfold tailWord_515372
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398580544451368687598185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12531440725935158250130913 9398580544451368687598185)
  ·
    refine ⟨7048935408338526515698639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9398580544451368687598185 7048935408338526515698639)
    ·
      refine ⟨10573403112507789773547959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048935408338526515698639 10573403112507789773547959)
      ·
        refine ⟨15860104668761684660321939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10573403112507789773547959 15860104668761684660321939)
        ·
          refine ⟨23790157003142526990482909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15860104668761684660321939 23790157003142526990482909)
          ·
            refine ⟨8921308876178447621431091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23790157003142526990482909 8921308876178447621431091)
            ·
              refine ⟨13381963314267671432146637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921308876178447621431091 13381963314267671432146637)
              ·
                refine ⟨5018236242850376787054989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13381963314267671432146637 5018236242850376787054989)
                ·
                  refine ⟨1881838591068891295145621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5018236242850376787054989 1881838591068891295145621)
                  ·
                    refine ⟨88211183956354279459951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1881838591068891295145621 88211183956354279459951)
                    ·
                      rfl

theorem cell23_515372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_515372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515372 prefixEnd_515372 := by exact prefixLift 515372
  have htrace : WordTrace (prefixWord ++ tailWord_515372) baseStart_515372 baseEnd_515372 := by
    simpa [prefixWord, tailWord_515372, baseEnd_515372] using wordTrace_append hprefix tailTrace_515372
  have hstable : (prefixWord ++ tailWord_515372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515372).length < 2 ^ (prefixWord ++ tailWord_515372).sum := by decide
  have hdescent : baseEnd_515372 < baseStart_515372 := by decide
  rcases family_descends (prefixWord ++ tailWord_515372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515392 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_515392 : Nat := 118140960795 + 515392 * 2 ^ 59
def prefixEnd_515392 : Nat := 4983230072969 + 3 ^ 40 * 515392 * 2
def baseEnd_515392 : Nat := 264643821482152760129761

theorem tailTrace_515392 : CollatzResearch.WordTrace tailWord_515392 prefixEnd_515392 264643821482152760129761 := by
  unfold tailWord_515392
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398945274415140395462215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12531927032553520527282953 9398945274415140395462215)
  ·
    refine ⟨14098417911622710593193323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9398945274415140395462215 14098417911622710593193323)
    ·
      refine ⟨21147626867434065889789985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14098417911622710593193323 21147626867434065889789985)
      ·
        refine ⟨15860720150575549417342489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21147626867434065889789985 15860720150575549417342489)
        ·
          refine ⟨11895540112931662063006867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15860720150575549417342489 11895540112931662063006867)
          ·
            refine ⟨17843310169397493094510301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895540112931662063006867 17843310169397493094510301)
            ·
              refine ⟨6691241313524059910441363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17843310169397493094510301 6691241313524059910441363)
              ·
                refine ⟨10036861970286089865662045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691241313524059910441363 10036861970286089865662045)
                ·
                  refine ⟨3763823238857283699623267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10036861970286089865662045 3763823238857283699623267)
                  ·
                    refine ⟨5645734858285925549434901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3763823238857283699623267 5645734858285925549434901)
                    ·
                      refine ⟨264643821482152760129761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5645734858285925549434901 264643821482152760129761)
                      ·
                        rfl

theorem cell23_515392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_515392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515392 prefixEnd_515392 := by exact prefixLift 515392
  have htrace : WordTrace (prefixWord ++ tailWord_515392) baseStart_515392 baseEnd_515392 := by
    simpa [prefixWord, tailWord_515392, baseEnd_515392] using wordTrace_append hprefix tailTrace_515392
  have hstable : (prefixWord ++ tailWord_515392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515392).length < 2 ^ (prefixWord ++ tailWord_515392).sum := by decide
  have hdescent : baseEnd_515392 < baseStart_515392 := by decide
  rcases family_descends (prefixWord ++ tailWord_515392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515399 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_515399 : Nat := 118140960795 + 515399 * 2 ^ 59
def prefixEnd_515399 : Nat := 4983230072969 + 3 ^ 40 * 515399 * 2
def baseEnd_515399 : Nat := 264647415846734232742229

theorem tailTrace_515399 : CollatzResearch.WordTrace tailWord_515399 prefixEnd_515399 264647415846734232742229 := by
  unfold tailWord_515399
  simp only [CollatzResearch.WordTrace]
  refine ⟨18798145859804920986429251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12532097239869947324286167 18798145859804920986429251)
  ·
    refine ⟨28197218789707381479643877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18798145859804920986429251 28197218789707381479643877)
    ·
      refine ⟨5286978523070134027433227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28197218789707381479643877 5286978523070134027433227)
      ·
        refine ⟨7930467784605201041149841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5286978523070134027433227 7930467784605201041149841)
        ·
          refine ⟨5947850838453900780862381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7930467784605201041149841 5947850838453900780862381)
          ·
            refine ⟨2230444064420212792823393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5947850838453900780862381 2230444064420212792823393)
            ·
              refine ⟨1672833048315159594617545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230444064420212792823393 1672833048315159594617545)
              ·
                refine ⟨1254624786236369695963159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672833048315159594617545 1254624786236369695963159)
                ·
                  refine ⟨1881937179354554543944739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254624786236369695963159 1881937179354554543944739)
                  ·
                    refine ⟨2822905769031831815917109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1881937179354554543944739 2822905769031831815917109)
                    ·
                      refine ⟨264647415846734232742229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2822905769031831815917109 264647415846734232742229)
                      ·
                        rfl

theorem cell23_515399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_515399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515399 prefixEnd_515399 := by exact prefixLift 515399
  have htrace : WordTrace (prefixWord ++ tailWord_515399) baseStart_515399 baseEnd_515399 := by
    simpa [prefixWord, tailWord_515399, baseEnd_515399] using wordTrace_append hprefix tailTrace_515399
  have hstable : (prefixWord ++ tailWord_515399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515399).length < 2 ^ (prefixWord ++ tailWord_515399).sum := by decide
  have hdescent : baseEnd_515399 < baseStart_515399 := by decide
  rcases family_descends (prefixWord ++ tailWord_515399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515406 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_515406 : Nat := 118140960795 + 515406 * 2 ^ 59
def prefixEnd_515406 : Nat := 4983230072969 + 3 ^ 40 * 515406 * 2
def baseEnd_515406 : Nat := 88217003403771901784899

theorem tailTrace_515406 : CollatzResearch.WordTrace tailWord_515406 prefixEnd_515406 88217003403771901784899 := by
  unfold tailWord_515406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349800146347445147741759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12532267447186374121289381 2349800146347445147741759)
  ·
    refine ⟨3524700219521167721612639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2349800146347445147741759 3524700219521167721612639)
    ·
      refine ⟨5287050329281751582418959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3524700219521167721612639 5287050329281751582418959)
      ·
        refine ⟨7930575493922627373628439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287050329281751582418959 7930575493922627373628439)
        ·
          refine ⟨11895863240883941060442659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930575493922627373628439 11895863240883941060442659)
          ·
            refine ⟨17843794861325911590663989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895863240883941060442659 17843794861325911590663989)
            ·
              refine ⟨1672855768249304211624749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17843794861325911590663989 1672855768249304211624749)
              ·
                refine ⟨627320913093489079359281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1672855768249304211624749 627320913093489079359281)
                ·
                  refine ⟨470490684820116809519461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627320913093489079359281 470490684820116809519461)
                  ·
                    refine ⟨88217003403771901784899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 470490684820116809519461 88217003403771901784899)
                    ·
                      rfl

theorem cell23_515406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_515406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515406 prefixEnd_515406 := by exact prefixLift 515406
  have htrace : WordTrace (prefixWord ++ tailWord_515406) baseStart_515406 baseEnd_515406 := by
    simpa [prefixWord, tailWord_515406, baseEnd_515406] using wordTrace_append hprefix tailTrace_515406
  have hstable : (prefixWord ++ tailWord_515406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515406).length < 2 ^ (prefixWord ++ tailWord_515406).sum := by decide
  have hdescent : baseEnd_515406 < baseStart_515406 := by decide
  rcases family_descends (prefixWord ++ tailWord_515406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515409 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_515409 : Nat := 118140960795 + 515409 * 2 ^ 59
def prefixEnd_515409 : Nat := 4983230072969 + 3 ^ 40 * 515409 * 2
def baseEnd_515409 : Nat := 264652550653279193617183

theorem tailTrace_515409 : CollatzResearch.WordTrace tailWord_515409 prefixEnd_515409 264652550653279193617183 := by
  unfold tailWord_515409
  simp only [CollatzResearch.WordTrace]
  refine ⟨18798510589768692694293281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12532340393179128462862187 18798510589768692694293281)
  ·
    refine ⟨14098882942326519520719961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18798510589768692694293281 14098882942326519520719961)
    ·
      refine ⟨10574162206744889640539971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14098882942326519520719961 10574162206744889640539971)
      ·
        refine ⟨15861243310117334460809957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10574162206744889640539971 15861243310117334460809957)
        ·
          refine ⟨2973983120647000211401867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15861243310117334460809957 2973983120647000211401867)
          ·
            refine ⟨4460974680970500317102801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973983120647000211401867 4460974680970500317102801)
            ·
              refine ⟨3345731010727875237827101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460974680970500317102801 3345731010727875237827101)
              ·
                refine ⟨1254649129022953214185163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3345731010727875237827101 1254649129022953214185163)
                ·
                  refine ⟨1881973693534429821277745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254649129022953214185163 1881973693534429821277745)
                  ·
                    refine ⟨1411480270150822365958309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1881973693534429821277745 1411480270150822365958309)
                    ·
                      refine ⟨264652550653279193617183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1411480270150822365958309 264652550653279193617183)
                      ·
                        rfl

theorem cell23_515409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_515409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515409 prefixEnd_515409 := by exact prefixLift 515409
  have htrace : WordTrace (prefixWord ++ tailWord_515409) baseStart_515409 baseEnd_515409 := by
    simpa [prefixWord, tailWord_515409, baseEnd_515409] using wordTrace_append hprefix tailTrace_515409
  have hstable : (prefixWord ++ tailWord_515409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515409).length < 2 ^ (prefixWord ++ tailWord_515409).sum := by decide
  have hdescent : baseEnd_515409 < baseStart_515409 := by decide
  rcases family_descends (prefixWord ++ tailWord_515409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515413 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_515413 : Nat := 118140960795 + 515413 * 2 ^ 59
def prefixEnd_515413 : Nat := 4983230072969 + 3 ^ 40 * 515413 * 2
def baseEnd_515413 : Nat := 264654604575897177967165

theorem tailTrace_515413 : CollatzResearch.WordTrace tailWord_515413 prefixEnd_515413 264654604575897177967165 := by
  unfold tailWord_515413
  simp only [CollatzResearch.WordTrace]
  refine ⟨18798656481754201377438893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12532437654502800918292595 18798656481754201377438893)
  ·
    refine ⟨7049496180657825516539585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18798656481754201377438893 7049496180657825516539585)
    ·
      refine ⟨5287122135493369137404689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7049496180657825516539585 5287122135493369137404689)
      ·
        refine ⟨3965341601620026853053517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5287122135493369137404689 3965341601620026853053517)
        ·
          refine ⟨1487003100607510069895069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3965341601620026853053517 1487003100607510069895069)
          ·
            refine ⟨557626162727816276210651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1487003100607510069895069 557626162727816276210651)
            ·
              refine ⟨836439244091724414315977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557626162727816276210651 836439244091724414315977)
              ·
                refine ⟨627329433068793310736983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836439244091724414315977 627329433068793310736983)
                ·
                  refine ⟨940994149603189966105475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627329433068793310736983 940994149603189966105475)
                  ·
                    refine ⟨1411491224404784949158213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 940994149603189966105475 1411491224404784949158213)
                    ·
                      refine ⟨264654604575897177967165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1411491224404784949158213 264654604575897177967165)
                      ·
                        rfl

theorem cell23_515413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_515413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515413 prefixEnd_515413 := by exact prefixLift 515413
  have htrace : WordTrace (prefixWord ++ tailWord_515413) baseStart_515413 baseEnd_515413 := by
    simpa [prefixWord, tailWord_515413, baseEnd_515413] using wordTrace_append hprefix tailTrace_515413
  have hstable : (prefixWord ++ tailWord_515413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515413).length < 2 ^ (prefixWord ++ tailWord_515413).sum := by decide
  have hdescent : baseEnd_515413 < baseStart_515413 := by decide
  rcases family_descends (prefixWord ++ tailWord_515413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515426 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_515426 : Nat := 118140960795 + 515426 * 2 ^ 59
def prefixEnd_515426 : Nat := 4983230072969 + 3 ^ 40 * 515426 * 2
def baseEnd_515426 : Nat := 264661279824405627104605

theorem tailTrace_515426 : CollatzResearch.WordTrace tailWord_515426 prefixEnd_515426 264661279824405627104605 := by
  unfold tailWord_515426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699782657676776149415533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12532753753804736398441421 4699782657676776149415533)
  ·
    refine ⟨1762418496628791056030825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4699782657676776149415533 1762418496628791056030825)
    ·
      refine ⟨1321813872471593292023119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1762418496628791056030825 1321813872471593292023119)
      ·
        refine ⟨1982720808707389938034679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321813872471593292023119 1982720808707389938034679)
        ·
          refine ⟨2974081213061084907052019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982720808707389938034679 2974081213061084907052019)
          ·
            refine ⟨4461121819591627360578029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974081213061084907052019 4461121819591627360578029)
            ·
              refine ⟨1672920682346860260216761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4461121819591627360578029 1672920682346860260216761)
              ·
                refine ⟨1254690511760145195162571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672920682346860260216761 1254690511760145195162571)
                ·
                  refine ⟨1882035767640217792743857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254690511760145195162571 1882035767640217792743857)
                  ·
                    refine ⟨1411526825730163344557893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1882035767640217792743857 1411526825730163344557893)
                    ·
                      refine ⟨264661279824405627104605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1411526825730163344557893 264661279824405627104605)
                      ·
                        rfl

theorem cell23_515426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_515426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515426 prefixEnd_515426 := by exact prefixLift 515426
  have htrace : WordTrace (prefixWord ++ tailWord_515426) baseStart_515426 baseEnd_515426 := by
    simpa [prefixWord, tailWord_515426, baseEnd_515426] using wordTrace_append hprefix tailTrace_515426
  have hstable : (prefixWord ++ tailWord_515426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515426).length < 2 ^ (prefixWord ++ tailWord_515426).sum := by decide
  have hdescent : baseEnd_515426 < baseStart_515426 := by decide
  rcases family_descends (prefixWord ++ tailWord_515426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515463 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_515463 : Nat := 118140960795 + 515463 * 2 ^ 59
def prefixEnd_515463 : Nat := 4983230072969 + 3 ^ 40 * 515463 * 2
def baseEnd_515463 : Nat := 264680278608621982341935

theorem tailTrace_515463 : CollatzResearch.WordTrace tailWord_515463 prefixEnd_515463 264680278608621982341935 := by
  unfold tailWord_515463
  simp only [CollatzResearch.WordTrace]
  refine ⟨18800480131573059916759043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12533653421048706611172695 18800480131573059916759043)
  ·
    refine ⟨28200720197359589875138565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18800480131573059916759043 28200720197359589875138565)
    ·
      refine ⟨5287635037004923101588481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28200720197359589875138565 5287635037004923101588481)
      ·
        refine ⟨3965726277753692326191361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5287635037004923101588481 3965726277753692326191361)
        ·
          refine ⟨2974294708315269244643521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3965726277753692326191361 2974294708315269244643521)
          ·
            refine ⟨2230721031236451933482641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974294708315269244643521 2230721031236451933482641)
            ·
              refine ⟨1673040773427338950111981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230721031236451933482641 1673040773427338950111981)
              ·
                refine ⟨627390290035252106291993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673040773427338950111981 627390290035252106291993)
                ·
                  refine ⟨470542717526439079718995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627390290035252106291993 470542717526439079718995)
                  ·
                    refine ⟨705814076289658619578493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470542717526439079718995 705814076289658619578493)
                    ·
                      refine ⟨264680278608621982341935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 705814076289658619578493 264680278608621982341935)
                      ·
                        rfl

theorem cell23_515463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_515463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515463 prefixEnd_515463 := by exact prefixLift 515463
  have htrace : WordTrace (prefixWord ++ tailWord_515463) baseStart_515463 baseEnd_515463 := by
    simpa [prefixWord, tailWord_515463, baseEnd_515463] using wordTrace_append hprefix tailTrace_515463
  have hstable : (prefixWord ++ tailWord_515463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515463).length < 2 ^ (prefixWord ++ tailWord_515463).sum := by decide
  have hdescent : baseEnd_515463 < baseStart_515463 := by decide
  rcases family_descends (prefixWord ++ tailWord_515463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515484 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_515484 : Nat := 118140960795 + 515484 * 2 ^ 59
def prefixEnd_515484 : Nat := 4983230072969 + 3 ^ 40 * 515484 * 2
def baseEnd_515484 : Nat := 264691061702366400179339

theorem tailTrace_515484 : CollatzResearch.WordTrace tailWord_515484 prefixEnd_515484 264691061702366400179339 := by
  unfold tailWord_515484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400623032248490251636753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12534164042997987002182337 9400623032248490251636753)
  ·
    refine ⟨7050467274186367688727565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9400623032248490251636753 7050467274186367688727565)
    ·
      refine ⟨2643925227819887883272837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7050467274186367688727565 2643925227819887883272837)
      ·
        refine ⟨495735980216228978113657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2643925227819887883272837 495735980216228978113657)
        ·
          refine ⟨371801985162171733585243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495735980216228978113657 371801985162171733585243)
          ·
            refine ⟨557702977743257600377865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371801985162171733585243 557702977743257600377865)
            ·
              refine ⟨418277233307443200283399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557702977743257600377865 418277233307443200283399)
              ·
                refine ⟨627415849961164800425099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418277233307443200283399 627415849961164800425099)
                ·
                  refine ⟨941123774941747200637649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627415849961164800425099 941123774941747200637649)
                  ·
                    refine ⟨705842831206310400478237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 941123774941747200637649 705842831206310400478237)
                    ·
                      refine ⟨264691061702366400179339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 705842831206310400478237 264691061702366400179339)
                      ·
                        rfl

theorem cell23_515484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_515484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515484 prefixEnd_515484 := by exact prefixLift 515484
  have htrace : WordTrace (prefixWord ++ tailWord_515484) baseStart_515484 baseEnd_515484 := by
    simpa [prefixWord, tailWord_515484, baseEnd_515484] using wordTrace_append hprefix tailTrace_515484
  have hstable : (prefixWord ++ tailWord_515484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515484).length < 2 ^ (prefixWord ++ tailWord_515484).sum := by decide
  have hdescent : baseEnd_515484 < baseStart_515484 := by decide
  rcases family_descends (prefixWord ++ tailWord_515484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515490 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_515490 : Nat := 118140960795 + 515490 * 2 ^ 59
def prefixEnd_515490 : Nat := 4983230072969 + 3 ^ 40 * 515490 * 2
def baseEnd_515490 : Nat := 264694142586293376704311

theorem tailTrace_515490 : CollatzResearch.WordTrace tailWord_515490 prefixEnd_515490 264694142586293376704311 := by
  unfold tailWord_515490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700366225618810881997981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12534309934983495685327949 4700366225618810881997981)
  ·
    refine ⟨1762637334607054080749243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4700366225618810881997981 1762637334607054080749243)
    ·
      refine ⟨2643956001910581121123865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762637334607054080749243 2643956001910581121123865)
      ·
        refine ⟨1982967001432935840842899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2643956001910581121123865 1982967001432935840842899)
        ·
          refine ⟨2974450502149403761264349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982967001432935840842899 2974450502149403761264349)
          ·
            refine ⟨1115418938306026410474131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2974450502149403761264349 1115418938306026410474131)
            ·
              refine ⟨1673128407459039615711197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115418938306026410474131 1673128407459039615711197)
              ·
                refine ⟨627423152797139855891699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673128407459039615711197 627423152797139855891699)
                ·
                  refine ⟨941134729195709783837549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627423152797139855891699 941134729195709783837549)
                  ·
                    refine ⟨352925523448391168939081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 941134729195709783837549 352925523448391168939081)
                    ·
                      refine ⟨264694142586293376704311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 352925523448391168939081 264694142586293376704311)
                      ·
                        rfl

theorem cell23_515490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_515490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515490 prefixEnd_515490 := by exact prefixLift 515490
  have htrace : WordTrace (prefixWord ++ tailWord_515490) baseStart_515490 baseEnd_515490 := by
    simpa [prefixWord, tailWord_515490, baseEnd_515490] using wordTrace_append hprefix tailTrace_515490
  have hstable : (prefixWord ++ tailWord_515490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515490).length < 2 ^ (prefixWord ++ tailWord_515490).sum := by decide
  have hdescent : baseEnd_515490 < baseStart_515490 := by decide
  rcases family_descends (prefixWord ++ tailWord_515490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515566 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_515566 : Nat := 118140960795 + 515566 * 2 ^ 59
def prefixEnd_515566 : Nat := 4983230072969 + 3 ^ 40 * 515566 * 2
def baseEnd_515566 : Nat := 264733167116035079353961

theorem tailTrace_515566 : CollatzResearch.WordTrace tailWord_515566 prefixEnd_515566 264733167116035079353961 := by
  unfold tailWord_515566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2350529606274988563469819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12536157900133272338505701 2350529606274988563469819)
  ·
    refine ⟨3525794409412482845204729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2350529606274988563469819 3525794409412482845204729)
    ·
      refine ⟨2644345807059362133903547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3525794409412482845204729 2644345807059362133903547)
      ·
        refine ⟨3966518710589043200855321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644345807059362133903547 3966518710589043200855321)
        ·
          refine ⟨2974889032941782400641491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966518710589043200855321 2974889032941782400641491)
          ·
            refine ⟨4462333549412673600962237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974889032941782400641491 4462333549412673600962237)
            ·
              refine ⟨1673375081029752600360839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4462333549412673600962237 1673375081029752600360839)
              ·
                refine ⟨2510062621544628900541259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673375081029752600360839 2510062621544628900541259)
                ·
                  refine ⟨3765093932316943350811889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510062621544628900541259 3765093932316943350811889)
                  ·
                    refine ⟨2823820449237707513108917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3765093932316943350811889 2823820449237707513108917)
                    ·
                      refine ⟨264733167116035079353961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2823820449237707513108917 264733167116035079353961)
                      ·
                        rfl

theorem cell23_515566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_515566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515566 prefixEnd_515566 := by exact prefixLift 515566
  have htrace : WordTrace (prefixWord ++ tailWord_515566) baseStart_515566 baseEnd_515566 := by
    simpa [prefixWord, tailWord_515566, baseEnd_515566] using wordTrace_append hprefix tailTrace_515566
  have hstable : (prefixWord ++ tailWord_515566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515566).length < 2 ^ (prefixWord ++ tailWord_515566).sum := by decide
  have hdescent : baseEnd_515566 < baseStart_515566 := by decide
  rcases family_descends (prefixWord ++ tailWord_515566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515589 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_515589 : Nat := 118140960795 + 515589 * 2 ^ 59
def prefixEnd_515589 : Nat := 4983230072969 + 3 ^ 40 * 515589 * 2
def baseEnd_515589 : Nat := 264744977171088489366355

theorem tailTrace_515589 : CollatzResearch.WordTrace tailWord_515589 prefixEnd_515589 264744977171088489366355 := by
  unfold tailWord_515589
  simp only [CollatzResearch.WordTrace]
  refine ⟨18805075729116583435845821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12536717152744388957230547 18805075729116583435845821)
  ·
    refine ⟨7051903398418718788442183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18805075729116583435845821 7051903398418718788442183)
    ·
      refine ⟨10577855097628078182663275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7051903398418718788442183 10577855097628078182663275)
      ·
        refine ⟨15866782646442117273994913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10577855097628078182663275 15866782646442117273994913)
        ·
          refine ⟨11900086984831587955496185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15866782646442117273994913 11900086984831587955496185)
          ·
            refine ⟨8925065238623690966622139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11900086984831587955496185 8925065238623690966622139)
            ·
              refine ⟨13387597857935536449933209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925065238623690966622139 13387597857935536449933209)
              ·
                refine ⟨10040698393451652337449907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13387597857935536449933209 10040698393451652337449907)
                ·
                  refine ⟨15061047590177478506174861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10040698393451652337449907 15061047590177478506174861)
                  ·
                    refine ⟨5647892846316554439815573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15061047590177478506174861 5647892846316554439815573)
                    ·
                      refine ⟨264744977171088489366355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5647892846316554439815573 264744977171088489366355)
                      ·
                        rfl

theorem cell23_515589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_515589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515589 prefixEnd_515589 := by exact prefixLift 515589
  have htrace : WordTrace (prefixWord ++ tailWord_515589) baseStart_515589 baseEnd_515589 := by
    simpa [prefixWord, tailWord_515589, baseEnd_515589] using wordTrace_append hprefix tailTrace_515589
  have hstable : (prefixWord ++ tailWord_515589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515589).length < 2 ^ (prefixWord ++ tailWord_515589).sum := by decide
  have hdescent : baseEnd_515589 < baseStart_515589 := by decide
  rcases family_descends (prefixWord ++ tailWord_515589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515613 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_515613 : Nat := 118140960795 + 515613 * 2 ^ 59
def prefixEnd_515613 : Nat := 4983230072969 + 3 ^ 40 * 515613 * 2
def baseEnd_515613 : Nat := 264757300706796395466245

theorem tailTrace_515613 : CollatzResearch.WordTrace tailWord_515613 prefixEnd_515613 264757300706796395466245 := by
  unfold tailWord_515613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18805951081029635534719493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12537300720686423689812995 18805951081029635534719493)
  ·
    refine ⟨3526115827693056662759905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18805951081029635534719493 3526115827693056662759905)
    ·
      refine ⟨2644586870769792497069929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3526115827693056662759905 2644586870769792497069929)
      ·
        refine ⟨1983440153077344372802447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2644586870769792497069929 1983440153077344372802447)
        ·
          refine ⟨2975160229616016559203671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983440153077344372802447 2975160229616016559203671)
          ·
            refine ⟨4462740344424024838805507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975160229616016559203671 4462740344424024838805507)
            ·
              refine ⟨6694110516636037258208261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462740344424024838805507 6694110516636037258208261)
              ·
                refine ⟨1255145721869256985914049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6694110516636037258208261 1255145721869256985914049)
                ·
                  refine ⟨941359291401942739435537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255145721869256985914049 941359291401942739435537)
                  ·
                    refine ⟨706019468551457054576653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 941359291401942739435537 706019468551457054576653)
                    ·
                      refine ⟨264757300706796395466245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 706019468551457054576653 264757300706796395466245)
                      ·
                        rfl

theorem cell23_515613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_515613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515613 prefixEnd_515613 := by exact prefixLift 515613
  have htrace : WordTrace (prefixWord ++ tailWord_515613) baseStart_515613 baseEnd_515613 := by
    simpa [prefixWord, tailWord_515613, baseEnd_515613] using wordTrace_append hprefix tailTrace_515613
  have hstable : (prefixWord ++ tailWord_515613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515613).length < 2 ^ (prefixWord ++ tailWord_515613).sum := by decide
  have hdescent : baseEnd_515613 < baseStart_515613 := by decide
  rcases family_descends (prefixWord ++ tailWord_515613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515653 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 1, 5, 2]
def baseStart_515653 : Nat := 118140960795 + 515653 * 2 ^ 59
def prefixEnd_515653 : Nat := 4983230072969 + 3 ^ 40 * 515653 * 2
def baseEnd_515653 : Nat := 264777839932976238966061

theorem tailTrace_515653 : CollatzResearch.WordTrace tailWord_515653 prefixEnd_515653 264777839932976238966061 := by
  unfold tailWord_515653
  simp only [CollatzResearch.WordTrace]
  refine ⟨18807410000884722366175613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12538273333923148244117075 18807410000884722366175613)
  ·
    refine ⟨7052778750331770887315855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18807410000884722366175613 7052778750331770887315855)
    ·
      refine ⟨10579168125497656330973783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7052778750331770887315855 10579168125497656330973783)
      ·
        refine ⟨15868752188246484496460675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10579168125497656330973783 15868752188246484496460675)
        ·
          refine ⟨23803128282369726744691013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15868752188246484496460675 23803128282369726744691013)
          ·
            refine ⟨4463086552944323764629565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23803128282369726744691013 4463086552944323764629565)
            ·
              refine ⟨1673657457354121411736087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4463086552944323764629565 1673657457354121411736087)
              ·
                refine ⟨2510486186031182117604131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673657457354121411736087 2510486186031182117604131)
                ·
                  refine ⟨3765729279046773176406197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510486186031182117604131 3765729279046773176406197)
                  ·
                    refine ⟨353037119910634985288081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3765729279046773176406197 353037119910634985288081)
                    ·
                      refine ⟨264777839932976238966061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353037119910634985288081 264777839932976238966061)
                      ·
                        rfl

theorem cell23_515653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_515653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515653 prefixEnd_515653 := by exact prefixLift 515653
  have htrace : WordTrace (prefixWord ++ tailWord_515653) baseStart_515653 baseEnd_515653 := by
    simpa [prefixWord, tailWord_515653, baseEnd_515653] using wordTrace_append hprefix tailTrace_515653
  have hstable : (prefixWord ++ tailWord_515653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515653).length < 2 ^ (prefixWord ++ tailWord_515653).sum := by decide
  have hdescent : baseEnd_515653 < baseStart_515653 := by decide
  rcases family_descends (prefixWord ++ tailWord_515653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515790 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_515790 : Nat := 118140960795 + 515790 * 2 ^ 59
def prefixEnd_515790 : Nat := 4983230072969 + 3 ^ 40 * 515790 * 2
def baseEnd_515790 : Nat := 264848186782642202952931

theorem tailTrace_515790 : CollatzResearch.WordTrace tailWord_515790 prefixEnd_515790 264848186782642202952931 := by
  unfold tailWord_515790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351550850173549345489103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12541604534258929842608549 2351550850173549345489103)
  ·
    refine ⟨3527326275260324018233655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2351550850173549345489103 3527326275260324018233655)
    ·
      refine ⟨5290989412890486027350483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527326275260324018233655 5290989412890486027350483)
      ·
        refine ⟨7936484119335729041025725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290989412890486027350483 7936484119335729041025725)
        ·
          refine ⟨2976181544750898390384647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7936484119335729041025725 2976181544750898390384647)
          ·
            refine ⟨4464272317126347585576971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976181544750898390384647 4464272317126347585576971)
            ·
              refine ⟨6696408475689521378365457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464272317126347585576971 6696408475689521378365457)
              ·
                refine ⟨5022306356767141033774093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6696408475689521378365457 5022306356767141033774093)
                ·
                  refine ⟨1883364883787677887665285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5022306356767141033774093 1883364883787677887665285)
                  ·
                    refine ⟨353130915710189603937241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883364883787677887665285 353130915710189603937241)
                    ·
                      refine ⟨264848186782642202952931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353130915710189603937241 264848186782642202952931)
                      ·
                        rfl

theorem cell23_515790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_515790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515790 prefixEnd_515790 := by exact prefixLift 515790
  have htrace : WordTrace (prefixWord ++ tailWord_515790) baseStart_515790 baseEnd_515790 := by
    simpa [prefixWord, tailWord_515790, baseEnd_515790] using wordTrace_append hprefix tailTrace_515790
  have hstable : (prefixWord ++ tailWord_515790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515790).length < 2 ^ (prefixWord ++ tailWord_515790).sum := by decide
  have hdescent : baseEnd_515790 < baseStart_515790 := by decide
  rcases family_descends (prefixWord ++ tailWord_515790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515793 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_515793 : Nat := 118140960795 + 515793 * 2 ^ 59
def prefixEnd_515793 : Nat := 4983230072969 + 3 ^ 40 * 515793 * 2
def baseEnd_515793 : Nat := 264849727224605691215417

theorem tailTrace_515793 : CollatzResearch.WordTrace tailWord_515793 prefixEnd_515793 264849727224605691215417 := by
  unfold tailWord_515793
  simp only [CollatzResearch.WordTrace]
  refine ⟨18812516220377526276272033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12541677480251684184181355 18812516220377526276272033)
  ·
    refine ⟨14109387165283144707204025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18812516220377526276272033 14109387165283144707204025)
    ·
      refine ⟨10582040373962358530403019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14109387165283144707204025 10582040373962358530403019)
      ·
        refine ⟨15873060560943537795604529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10582040373962358530403019 15873060560943537795604529)
        ·
          refine ⟨11904795420707653346703397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15873060560943537795604529 11904795420707653346703397)
          ·
            refine ⟨2232149141382685002506887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11904795420707653346703397 2232149141382685002506887)
            ·
              refine ⟨3348223712074027503760331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232149141382685002506887 3348223712074027503760331)
              ·
                refine ⟨5022335568111041255640497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348223712074027503760331 5022335568111041255640497)
                ·
                  refine ⟨3766751676083280941730373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5022335568111041255640497 3766751676083280941730373)
                  ·
                    refine ⟨706265939265615176574445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3766751676083280941730373 706265939265615176574445)
                    ·
                      refine ⟨264849727224605691215417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 706265939265615176574445 264849727224605691215417)
                      ·
                        rfl

theorem cell23_515793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_515793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515793 prefixEnd_515793 := by exact prefixLift 515793
  have htrace : WordTrace (prefixWord ++ tailWord_515793) baseStart_515793 baseEnd_515793 := by
    simpa [prefixWord, tailWord_515793, baseEnd_515793] using wordTrace_append hprefix tailTrace_515793
  have hstable : (prefixWord ++ tailWord_515793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515793).length < 2 ^ (prefixWord ++ tailWord_515793).sum := by decide
  have hdescent : baseEnd_515793 < baseStart_515793 := by decide
  rcases family_descends (prefixWord ++ tailWord_515793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515807 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 2, 2, 2]
def baseStart_515807 : Nat := 118140960795 + 515807 * 2 ^ 59
def prefixEnd_515807 : Nat := 4983230072969 + 3 ^ 40 * 515807 * 2
def baseEnd_515807 : Nat := 264856915953768636440353

theorem tailTrace_515807 : CollatzResearch.WordTrace tailWord_515807 prefixEnd_515807 264856915953768636440353 := by
  unfold tailWord_515807
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813026842326806667281675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12542017894884537778187783 18813026842326806667281675)
  ·
    refine ⟨28219540263490210000922513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18813026842326806667281675 28219540263490210000922513)
    ·
      refine ⟨21164655197617657500691885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28219540263490210000922513 21164655197617657500691885)
      ·
        refine ⟨7936745699106621562759457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21164655197617657500691885 7936745699106621562759457)
        ·
          refine ⟨5952559274329966172069593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7936745699106621562759457 5952559274329966172069593)
          ·
            refine ⟨4464419455747474629052195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5952559274329966172069593 4464419455747474629052195)
            ·
              refine ⟨6696629183621211943578293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464419455747474629052195 6696629183621211943578293)
              ·
                refine ⟨627808985964488619710465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6696629183621211943578293 627808985964488619710465)
                ·
                  refine ⟨470856739473366464782849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627808985964488619710465 470856739473366464782849)
                  ·
                    refine ⟨353142554605024848587137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470856739473366464782849 353142554605024848587137)
                    ·
                      refine ⟨264856915953768636440353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353142554605024848587137 264856915953768636440353)
                      ·
                        rfl

theorem cell23_515807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_515807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515807 prefixEnd_515807 := by exact prefixLift 515807
  have htrace : WordTrace (prefixWord ++ tailWord_515807) baseStart_515807 baseEnd_515807 := by
    simpa [prefixWord, tailWord_515807, baseEnd_515807] using wordTrace_append hprefix tailTrace_515807
  have hstable : (prefixWord ++ tailWord_515807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515807).length < 2 ^ (prefixWord ++ tailWord_515807).sum := by decide
  have hdescent : baseEnd_515807 < baseStart_515807 := by decide
  rcases family_descends (prefixWord ++ tailWord_515807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515813 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 7]
def baseStart_515813 : Nat := 118140960795 + 515813 * 2 ^ 59
def prefixEnd_515813 : Nat := 4983230072969 + 3 ^ 40 * 515813 * 2
def baseEnd_515813 : Nat := 29428888537521734773925

theorem tailTrace_515813 : CollatzResearch.WordTrace tailWord_515813 prefixEnd_515813 29428888537521734773925 := by
  unfold tailWord_515813
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813245680305069692000093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12542163786870046461333395 18813245680305069692000093)
  ·
    refine ⟨7054967130114401134500035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18813245680305069692000093 7054967130114401134500035)
    ·
      refine ⟨10582450695171601701750053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054967130114401134500035 10582450695171601701750053)
      ·
        refine ⟨1984209505344675319078135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10582450695171601701750053 1984209505344675319078135)
        ·
          refine ⟨2976314258017012978617203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984209505344675319078135 2976314258017012978617203)
          ·
            refine ⟨4464471387025519467925805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976314258017012978617203 4464471387025519467925805)
            ·
              refine ⟨1674176770134569800472177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4464471387025519467925805 1674176770134569800472177)
              ·
                refine ⟨1255632577600927350354133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674176770134569800472177 1255632577600927350354133)
                ·
                  refine ⟨29428888537521734773925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1255632577600927350354133 29428888537521734773925)
                  ·
                    rfl

theorem cell23_515813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_515813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515813 prefixEnd_515813 := by exact prefixLift 515813
  have htrace : WordTrace (prefixWord ++ tailWord_515813) baseStart_515813 baseEnd_515813 := by
    simpa [prefixWord, tailWord_515813, baseEnd_515813] using wordTrace_append hprefix tailTrace_515813
  have hstable : (prefixWord ++ tailWord_515813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515813).length < 2 ^ (prefixWord ++ tailWord_515813).sum := by decide
  have hdescent : baseEnd_515813 < baseStart_515813 := by decide
  rcases family_descends (prefixWord ++ tailWord_515813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515823 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 3]
def baseStart_515823 : Nat := 118140960795 + 515823 * 2 ^ 59
def prefixEnd_515823 : Nat := 4983230072969 + 3 ^ 40 * 515823 * 2
def baseEnd_515823 : Nat := 264865131644240573840279

theorem tailTrace_515823 : CollatzResearch.WordTrace tailWord_515823 prefixEnd_515823 264865131644240573840279 := by
  unfold tailWord_515823
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813610410268841399864123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12542406940179227599909415 18813610410268841399864123)
  ·
    refine ⟨28220415615403262099796185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18813610410268841399864123 28220415615403262099796185)
    ·
      refine ⟨21165311711552446574847139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28220415615403262099796185 21165311711552446574847139)
      ·
        refine ⟨31747967567328669862270709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21165311711552446574847139 31747967567328669862270709)
        ·
          refine ⟨2976371959437062799587879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31747967567328669862270709 2976371959437062799587879)
          ·
            refine ⟨4464557939155594199381819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976371959437062799587879 4464557939155594199381819)
            ·
              refine ⟨6696836908733391299072729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464557939155594199381819 6696836908733391299072729)
              ·
                refine ⟨5022627681550043474304547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6696836908733391299072729 5022627681550043474304547)
                ·
                  refine ⟨7533941522325065211456821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5022627681550043474304547 7533941522325065211456821)
                  ·
                    refine ⟨706307017717974863574077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7533941522325065211456821 706307017717974863574077)
                    ·
                      refine ⟨264865131644240573840279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 706307017717974863574077 264865131644240573840279)
                      ·
                        rfl

theorem cell23_515823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_515823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515823 prefixEnd_515823 := by exact prefixLift 515823
  have htrace : WordTrace (prefixWord ++ tailWord_515823) baseStart_515823 baseEnd_515823 := by
    simpa [prefixWord, tailWord_515823, baseEnd_515823] using wordTrace_append hprefix tailTrace_515823
  have hstable : (prefixWord ++ tailWord_515823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515823).length < 2 ^ (prefixWord ++ tailWord_515823).sum := by decide
  have hdescent : baseEnd_515823 < baseStart_515823 := by decide
  rcases family_descends (prefixWord ++ tailWord_515823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515828 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_515828 : Nat := 118140960795 + 515828 * 2 ^ 59
def prefixEnd_515828 : Nat := 4983230072969 + 3 ^ 40 * 515828 * 2
def baseEnd_515828 : Nat := 264867699047513054277757

theorem tailTrace_515828 : CollatzResearch.WordTrace tailWord_515828 prefixEnd_515828 264867699047513054277757 := by
  unfold tailWord_515828
  simp only [CollatzResearch.WordTrace]
  refine ⟨9406896387625363626898069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12542528516833818169197425 9406896387625363626898069)
  ·
    refine ⟨440948268169938920010847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9406896387625363626898069 440948268169938920010847)
    ·
      refine ⟨661422402254908380016271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440948268169938920010847 661422402254908380016271)
      ·
        refine ⟨992133603382362570024407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661422402254908380016271 992133603382362570024407)
        ·
          refine ⟨1488200405073543855036611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992133603382362570024407 1488200405073543855036611)
          ·
            refine ⟨2232300607610315782554917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488200405073543855036611 2232300607610315782554917)
            ·
              refine ⟨418556363926934209229047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2232300607610315782554917 418556363926934209229047)
              ·
                refine ⟨627834545890401313843571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418556363926934209229047 627834545890401313843571)
                ·
                  refine ⟨941751818835601970765357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627834545890401313843571 941751818835601970765357)
                  ·
                    refine ⟨353156932063350739037009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 941751818835601970765357 353156932063350739037009)
                    ·
                      refine ⟨264867699047513054277757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353156932063350739037009 264867699047513054277757)
                      ·
                        rfl

theorem cell23_515828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_515828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515828 prefixEnd_515828 := by exact prefixLift 515828
  have htrace : WordTrace (prefixWord ++ tailWord_515828) baseStart_515828 baseEnd_515828 := by
    simpa [prefixWord, tailWord_515828, baseEnd_515828] using wordTrace_append hprefix tailTrace_515828
  have hstable : (prefixWord ++ tailWord_515828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515828).length < 2 ^ (prefixWord ++ tailWord_515828).sum := by decide
  have hdescent : baseEnd_515828 < baseStart_515828 := by decide
  rcases family_descends (prefixWord ++ tailWord_515828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515843 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 2, 5]
def baseStart_515843 : Nat := 118140960795 + 515843 * 2 ^ 59
def prefixEnd_515843 : Nat := 4983230072969 + 3 ^ 40 * 515843 * 2
def baseEnd_515843 : Nat := 88291800419110165196729

theorem tailTrace_515843 : CollatzResearch.WordTrace tailWord_515843 prefixEnd_515843 88291800419110165196729 := by
  unfold tailWord_515843
  simp only [CollatzResearch.WordTrace]
  refine ⟨18814339870196384815592183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12542893246797589877061455 18814339870196384815592183)
  ·
    refine ⟨28221509805294577223388275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18814339870196384815592183 28221509805294577223388275)
    ·
      refine ⟨42332264707941865835082413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28221509805294577223388275 42332264707941865835082413)
      ·
        refine ⟨15874599265478199688155905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42332264707941865835082413 15874599265478199688155905)
        ·
          refine ⟨11905949449108649766116929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15874599265478199688155905 11905949449108649766116929)
          ·
            refine ⟨8929462086831487324587697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11905949449108649766116929 8929462086831487324587697)
            ·
              refine ⟨6697096565123615493440773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8929462086831487324587697 6697096565123615493440773)
              ·
                refine ⟨1255705605960677905020145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6697096565123615493440773 1255705605960677905020145)
                ·
                  refine ⟨941779204470508428765109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255705605960677905020145 941779204470508428765109)
                  ·
                    refine ⟨88291800419110165196729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 941779204470508428765109 88291800419110165196729)
                    ·
                      rfl

theorem cell23_515843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 5].length) (baseStart_515843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515843 prefixEnd_515843 := by exact prefixLift 515843
  have htrace : WordTrace (prefixWord ++ tailWord_515843) baseStart_515843 baseEnd_515843 := by
    simpa [prefixWord, tailWord_515843, baseEnd_515843] using wordTrace_append hprefix tailTrace_515843
  have hstable : (prefixWord ++ tailWord_515843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515843).length < 2 ^ (prefixWord ++ tailWord_515843).sum := by decide
  have hdescent : baseEnd_515843 < baseStart_515843 := by decide
  rcases family_descends (prefixWord ++ tailWord_515843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515858 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_515858 : Nat := 118140960795 + 515858 * 2 ^ 59
def prefixEnd_515858 : Nat := 4983230072969 + 3 ^ 40 * 515858 * 2
def baseEnd_515858 : Nat := 264883103467147936902619

theorem tailTrace_515858 : CollatzResearch.WordTrace tailWord_515858 prefixEnd_515858 264883103467147936902619 := by
  unfold tailWord_515858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703721741285510594347057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12543257976761361584925485 4703721741285510594347057)
  ·
    refine ⟨3527791305964132945760293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4703721741285510594347057 3527791305964132945760293)
    ·
      refine ⟨661460869868274927330055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3527791305964132945760293 661460869868274927330055)
      ·
        refine ⟨992191304802412390995083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661460869868274927330055 992191304802412390995083)
        ·
          refine ⟨1488286957203618586492625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992191304802412390995083 1488286957203618586492625)
          ·
            refine ⟨1116215217902713939869469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488286957203618586492625 1116215217902713939869469)
            ·
              refine ⟨418580706713517727451051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116215217902713939869469 418580706713517727451051)
              ·
                refine ⟨627871060070276591176577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418580706713517727451051 627871060070276591176577)
                ·
                  refine ⟨470903295052707443382433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627871060070276591176577 470903295052707443382433)
                  ·
                    refine ⟨353177471289530582536825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470903295052707443382433 353177471289530582536825)
                    ·
                      refine ⟨264883103467147936902619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353177471289530582536825 264883103467147936902619)
                      ·
                        rfl

theorem cell23_515858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_515858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515858 prefixEnd_515858 := by exact prefixLift 515858
  have htrace : WordTrace (prefixWord ++ tailWord_515858) baseStart_515858 baseEnd_515858 := by
    simpa [prefixWord, tailWord_515858, baseEnd_515858] using wordTrace_append hprefix tailTrace_515858
  have hstable : (prefixWord ++ tailWord_515858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515858).length < 2 ^ (prefixWord ++ tailWord_515858).sum := by decide
  have hdescent : baseEnd_515858 < baseStart_515858 := by decide
  rcases family_descends (prefixWord ++ tailWord_515858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515880 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_515880 : Nat := 118140960795 + 515880 * 2 ^ 59
def prefixEnd_515880 : Nat := 4983230072969 + 3 ^ 40 * 515880 * 2
def baseEnd_515880 : Nat := 264894400041546850827517

theorem tailTrace_515880 : CollatzResearch.WordTrace tailWord_515880 prefixEnd_515880 264894400041546850827517 := by
  unfold tailWord_515880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407844685531170067344547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12543792914041560089792729 9407844685531170067344547)
  ·
    refine ⟨14111767028296755101016821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9407844685531170067344547 14111767028296755101016821)
    ·
      refine ⟨1322978158902820790720327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14111767028296755101016821 1322978158902820790720327)
      ·
        refine ⟨1984467238354231186080491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322978158902820790720327 1984467238354231186080491)
        ·
          refine ⟨2976700857531346779120737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984467238354231186080491 2976700857531346779120737)
          ·
            refine ⟨2232525643148510084340553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2976700857531346779120737 2232525643148510084340553)
            ·
              refine ⟨1674394232361382563255415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232525643148510084340553 1674394232361382563255415)
              ·
                refine ⟨2511591348542073844883123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674394232361382563255415 2511591348542073844883123)
                ·
                  refine ⟨3767387022813110767324685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511591348542073844883123 3767387022813110767324685)
                  ·
                    refine ⟨1412770133554916537746757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3767387022813110767324685 1412770133554916537746757)
                    ·
                      refine ⟨264894400041546850827517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1412770133554916537746757 264894400041546850827517)
                      ·
                        rfl

theorem cell23_515880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_515880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515880 prefixEnd_515880 := by exact prefixLift 515880
  have htrace : WordTrace (prefixWord ++ tailWord_515880) baseStart_515880 baseEnd_515880 := by
    simpa [prefixWord, tailWord_515880, baseEnd_515880] using wordTrace_append hprefix tailTrace_515880
  have hstable : (prefixWord ++ tailWord_515880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515880).length < 2 ^ (prefixWord ++ tailWord_515880).sum := by decide
  have hdescent : baseEnd_515880 < baseStart_515880 := by decide
  rcases family_descends (prefixWord ++ tailWord_515880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515883 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 3]
def baseStart_515883 : Nat := 118140960795 + 515883 * 2 ^ 59
def prefixEnd_515883 : Nat := 4983230072969 + 3 ^ 40 * 515883 * 2
def baseEnd_515883 : Nat := 264895940483510339090003

theorem tailTrace_515883 : CollatzResearch.WordTrace tailWord_515883 prefixEnd_515883 264895940483510339090003 := by
  unfold tailWord_515883
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815798790051471647048303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12543865860034314431365535 18815798790051471647048303)
  ·
    refine ⟨28223698185077207470572455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18815798790051471647048303 28223698185077207470572455)
    ·
      refine ⟨42335547277615811205858683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28223698185077207470572455 42335547277615811205858683)
      ·
        refine ⟨63503320916423716808788025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42335547277615811205858683 63503320916423716808788025)
        ·
          refine ⟨47627490687317787606591019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63503320916423716808788025 47627490687317787606591019)
          ·
            refine ⟨71441236030976681409886529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47627490687317787606591019 71441236030976681409886529)
            ·
              refine ⟨53580927023232511057414897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71441236030976681409886529 53580927023232511057414897)
              ·
                refine ⟨40185695267424383293061173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53580927023232511057414897 40185695267424383293061173)
                ·
                  refine ⟨3767408931321035933724485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40185695267424383293061173 3767408931321035933724485)
                  ·
                    refine ⟨706389174622694237573341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767408931321035933724485 706389174622694237573341)
                    ·
                      refine ⟨264895940483510339090003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 706389174622694237573341 264895940483510339090003)
                      ·
                        rfl

theorem cell23_515883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 3].length) (baseStart_515883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515883 prefixEnd_515883 := by exact prefixLift 515883
  have htrace : WordTrace (prefixWord ++ tailWord_515883) baseStart_515883 baseEnd_515883 := by
    simpa [prefixWord, tailWord_515883, baseEnd_515883] using wordTrace_append hprefix tailTrace_515883
  have hstable : (prefixWord ++ tailWord_515883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515883).length < 2 ^ (prefixWord ++ tailWord_515883).sum := by decide
  have hdescent : baseEnd_515883 < baseStart_515883 := by decide
  rcases family_descends (prefixWord ++ tailWord_515883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515900 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_515900 : Nat := 118140960795 + 515900 * 2 ^ 59
def prefixEnd_515900 : Nat := 4983230072969 + 3 ^ 40 * 515900 * 2
def baseEnd_515900 : Nat := 264904669654636772577425

theorem tailTrace_515900 : CollatzResearch.WordTrace tailWord_515900 prefixEnd_515900 264904669654636772577425 := by
  unfold tailWord_515900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408209415494941775208577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12544279220659922366944769 9408209415494941775208577)
  ·
    refine ⟨7056157061621206331406433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9408209415494941775208577 7056157061621206331406433)
    ·
      refine ⟨5292117796215904748554825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7056157061621206331406433 5292117796215904748554825)
      ·
        refine ⟨3969088347161928561416119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5292117796215904748554825 3969088347161928561416119)
        ·
          refine ⟨5953632520742892842124179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969088347161928561416119 5953632520742892842124179)
          ·
            refine ⟨8930448781114339263186269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953632520742892842124179 8930448781114339263186269)
            ·
              refine ⟨3348918292917877223694851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8930448781114339263186269 3348918292917877223694851)
              ·
                refine ⟨5023377439376815835542277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348918292917877223694851 5023377439376815835542277)
                ·
                  refine ⟨941883269883152969164177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5023377439376815835542277 941883269883152969164177)
                  ·
                    refine ⟨706412452412364726873133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 941883269883152969164177 706412452412364726873133)
                    ·
                      refine ⟨264904669654636772577425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 706412452412364726873133 264904669654636772577425)
                      ·
                        rfl

theorem cell23_515900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_515900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515900 prefixEnd_515900 := by exact prefixLift 515900
  have htrace : WordTrace (prefixWord ++ tailWord_515900) baseStart_515900 baseEnd_515900 := by
    simpa [prefixWord, tailWord_515900, baseEnd_515900] using wordTrace_append hprefix tailTrace_515900
  have hstable : (prefixWord ++ tailWord_515900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515900).length < 2 ^ (prefixWord ++ tailWord_515900).sum := by decide
  have hdescent : baseEnd_515900 < baseStart_515900 := by decide
  rcases family_descends (prefixWord ++ tailWord_515900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515907 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 3, 4]
def baseStart_515907 : Nat := 118140960795 + 515907 * 2 ^ 59
def prefixEnd_515907 : Nat := 4983230072969 + 3 ^ 40 * 515907 * 2
def baseEnd_515907 : Nat := 88302754673072748396631

theorem tailTrace_515907 : CollatzResearch.WordTrace tailWord_515907 prefixEnd_515907 88302754673072748396631 := by
  unfold tailWord_515907
  simp only [CollatzResearch.WordTrace]
  refine ⟨18816674141964523745921975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12544449427976349163947983 18816674141964523745921975)
  ·
    refine ⟨28225011212946785618882963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18816674141964523745921975 28225011212946785618882963)
    ·
      refine ⟨42337516819420178428324445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28225011212946785618882963 42337516819420178428324445)
      ·
        refine ⟨15876568807282566910621667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42337516819420178428324445 15876568807282566910621667)
        ·
          refine ⟨23814853210923850365932501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15876568807282566910621667 23814853210923850365932501)
          ·
            refine ⟨558160622131027742951543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23814853210923850365932501 558160622131027742951543)
            ·
              refine ⟨837240933196541614427315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558160622131027742951543 837240933196541614427315)
              ·
                refine ⟨1255861399794812421640973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837240933196541614427315 1255861399794812421640973)
                ·
                  refine ⟨470948024923054658115365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255861399794812421640973 470948024923054658115365)
                  ·
                    refine ⟨88302754673072748396631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 470948024923054658115365 88302754673072748396631)
                    ·
                      rfl

theorem cell23_515907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 4].length) (baseStart_515907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515907 prefixEnd_515907 := by exact prefixLift 515907
  have htrace : WordTrace (prefixWord ++ tailWord_515907) baseStart_515907 baseEnd_515907 := by
    simpa [prefixWord, tailWord_515907, baseEnd_515907] using wordTrace_append hprefix tailTrace_515907
  have hstable : (prefixWord ++ tailWord_515907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515907).length < 2 ^ (prefixWord ++ tailWord_515907).sum := by decide
  have hdescent : baseEnd_515907 < baseStart_515907 := by decide
  rcases family_descends (prefixWord ++ tailWord_515907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515963 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 5, 6]
def baseStart_515963 : Nat := 118140960795 + 515963 * 2 ^ 59
def prefixEnd_515963 : Nat := 4983230072969 + 3 ^ 40 * 515963 * 2
def baseEnd_515963 : Nat := 88312339645290008696545

theorem tailTrace_515963 : CollatzResearch.WordTrace tailWord_515963 prefixEnd_515963 88312339645290008696545 := by
  unfold tailWord_515963
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818716629761645309960543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12545811086507763539973695 18818716629761645309960543)
  ·
    refine ⟨28228074944642467964940815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18818716629761645309960543 28228074944642467964940815)
    ·
      refine ⟨42342112416963701947411223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28228074944642467964940815 42342112416963701947411223)
      ·
        refine ⟨63513168625445552921116835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42342112416963701947411223 63513168625445552921116835)
        ·
          refine ⟨95269752938168329381675253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63513168625445552921116835 95269752938168329381675253)
          ·
            refine ⟨8931539337953280879532055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95269752938168329381675253 8931539337953280879532055)
            ·
              refine ⟨13397309006929921319298083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931539337953280879532055 13397309006929921319298083)
              ·
                refine ⟨20095963510394881978947125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397309006929921319298083 20095963510394881978947125)
                ·
                  refine ⟨1883996579099520185526293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20095963510394881978947125 1883996579099520185526293)
                  ·
                    refine ⟨88312339645290008696545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1883996579099520185526293 88312339645290008696545)
                    ·
                      rfl

theorem cell23_515963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 6].length) (baseStart_515963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515963 prefixEnd_515963 := by exact prefixLift 515963
  have htrace : WordTrace (prefixWord ++ tailWord_515963) baseStart_515963 baseEnd_515963 := by
    simpa [prefixWord, tailWord_515963, baseEnd_515963] using wordTrace_append hprefix tailTrace_515963
  have hstable : (prefixWord ++ tailWord_515963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515963).length < 2 ^ (prefixWord ++ tailWord_515963).sum := by decide
  have hdescent : baseEnd_515963 < baseStart_515963 := by decide
  rcases family_descends (prefixWord ++ tailWord_515963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515980 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_515980 : Nat := 118140960795 + 515980 * 2 ^ 59
def prefixEnd_515980 : Nat := 4983230072969 + 3 ^ 40 * 515980 * 2
def baseEnd_515980 : Nat := 88315249368998819859019

theorem tailTrace_515980 : CollatzResearch.WordTrace tailWord_515980 prefixEnd_515980 88315249368998819859019 := by
  unfold tailWord_515980
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409668335350028606664697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12546224447133371475552929 9409668335350028606664697)
  ·
    refine ⟨7057251251512521454998523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9409668335350028606664697 7057251251512521454998523)
    ·
      refine ⟨10585876877268782182497785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7057251251512521454998523 10585876877268782182497785)
      ·
        refine ⟨7939407657951586636873339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10585876877268782182497785 7939407657951586636873339)
        ·
          refine ⟨11909111486927379955310009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7939407657951586636873339 11909111486927379955310009)
          ·
            refine ⟨8931833615195534966482507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11909111486927379955310009 8931833615195534966482507)
            ·
              refine ⟨13397750422793302449723761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931833615195534966482507 13397750422793302449723761)
              ·
                refine ⟨10048312817094976837292821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13397750422793302449723761 10048312817094976837292821)
                ·
                  refine ⟨471014663301327039248101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10048312817094976837292821 471014663301327039248101)
                  ·
                    refine ⟨88315249368998819859019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471014663301327039248101 88315249368998819859019)
                    ·
                      rfl

theorem cell23_515980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_515980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515980 prefixEnd_515980 := by exact prefixLift 515980
  have htrace : WordTrace (prefixWord ++ tailWord_515980) baseStart_515980 baseEnd_515980 := by
    simpa [prefixWord, tailWord_515980, baseEnd_515980] using wordTrace_append hprefix tailTrace_515980
  have hstable : (prefixWord ++ tailWord_515980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515980).length < 2 ^ (prefixWord ++ tailWord_515980).sum := by decide
  have hdescent : baseEnd_515980 < baseStart_515980 := by decide
  rcases family_descends (prefixWord ++ tailWord_515980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515983 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_515983 : Nat := 118140960795 + 515983 * 2 ^ 59
def prefixEnd_515983 : Nat := 4983230072969 + 3 ^ 40 * 515983 * 2
def baseEnd_515983 : Nat := 264947288548959947839543

theorem tailTrace_515983 : CollatzResearch.WordTrace tailWord_515983 prefixEnd_515983 264947288548959947839543 := by
  unfold tailWord_515983
  simp only [CollatzResearch.WordTrace]
  refine ⟨18819446089689188725688603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12546297393126125817125735 18819446089689188725688603)
  ·
    refine ⟨28229169134533783088532905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18819446089689188725688603 28229169134533783088532905)
    ·
      refine ⟨21171876850900337316399679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28229169134533783088532905 21171876850900337316399679)
      ·
        refine ⟨31757815276350505974599519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21171876850900337316399679 31757815276350505974599519)
        ·
          refine ⟨47636722914525758961899279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31757815276350505974599519 47636722914525758961899279)
          ·
            refine ⟨71455084371788638442848919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47636722914525758961899279 71455084371788638442848919)
            ·
              refine ⟨107182626557682957664273379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71455084371788638442848919 107182626557682957664273379)
              ·
                refine ⟨160773939836524436496410069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107182626557682957664273379 160773939836524436496410069)
                ·
                  refine ⟨3768139214918541480384611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160773939836524436496410069 3768139214918541480384611)
                  ·
                    refine ⟨5652208822377812220576917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3768139214918541480384611 5652208822377812220576917)
                    ·
                      refine ⟨264947288548959947839543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5652208822377812220576917 264947288548959947839543)
                      ·
                        rfl

theorem cell23_515983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_515983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515983 prefixEnd_515983 := by exact prefixLift 515983
  have htrace : WordTrace (prefixWord ++ tailWord_515983) baseStart_515983 baseEnd_515983 := by
    simpa [prefixWord, tailWord_515983, baseEnd_515983] using wordTrace_append hprefix tailTrace_515983
  have hstable : (prefixWord ++ tailWord_515983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515983).length < 2 ^ (prefixWord ++ tailWord_515983).sum := by decide
  have hdescent : baseEnd_515983 < baseStart_515983 := by decide
  rcases family_descends (prefixWord ++ tailWord_515983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515993 : List Nat := [1, 2, 1, 2, 1, 3, 2, 11]
def baseStart_515993 : Nat := 118140960795 + 515993 * 2 ^ 59
def prefixEnd_515993 : Nat := 4983230072969 + 3 ^ 40 * 515993 * 2
def baseEnd_515993 : Nat := 9813052716870552174611

theorem tailTrace_515993 : CollatzResearch.WordTrace tailWord_515993 prefixEnd_515993 9813052716870552174611 := by
  unfold tailWord_515993
  simp only [CollatzResearch.WordTrace]
  refine ⟨18819810819652960433552633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12546540546435306955701755 18819810819652960433552633)
  ·
    refine ⟨14114858114739720325164475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18819810819652960433552633 14114858114739720325164475)
    ·
      refine ⟨21172287172109580487746713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14114858114739720325164475 21172287172109580487746713)
      ·
        refine ⟨15879215379082185365810035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21172287172109580487746713 15879215379082185365810035)
        ·
          refine ⟨23818823068623278048715053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15879215379082185365810035 23818823068623278048715053)
          ·
            refine ⟨8932058650733729268268145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23818823068623278048715053 8932058650733729268268145)
            ·
              refine ⟨6699043988050296951201109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8932058650733729268268145 6699043988050296951201109)
              ·
                refine ⟨9813052716870552174611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 6699043988050296951201109 9813052716870552174611)
                ·
                  rfl

theorem cell23_515993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 11].length) (baseStart_515993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_515993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_515993 prefixEnd_515993 := by exact prefixLift 515993
  have htrace : WordTrace (prefixWord ++ tailWord_515993) baseStart_515993 baseEnd_515993 := by
    simpa [prefixWord, tailWord_515993, baseEnd_515993] using wordTrace_append hprefix tailTrace_515993
  have hstable : (prefixWord ++ tailWord_515993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515993).length < 2 ^ (prefixWord ++ tailWord_515993).sum := by decide
  have hdescent : baseEnd_515993 < baseStart_515993 := by decide
  rcases family_descends (prefixWord ++ tailWord_515993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516001 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 1, 5]
def baseStart_516001 : Nat := 118140960795 + 516001 * 2 ^ 59
def prefixEnd_516001 : Nat := 4983230072969 + 3 ^ 40 * 516001 * 2
def baseEnd_516001 : Nat := 88318843733580292471487

theorem tailTrace_516001 : CollatzResearch.WordTrace tailWord_516001 prefixEnd_516001 88318843733580292471487 := by
  unfold tailWord_516001
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820102603623977799843857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12546735069082651866562571 18820102603623977799843857)
  ·
    refine ⟨14115076952717983349882893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18820102603623977799843857 14115076952717983349882893)
    ·
      refine ⟨5293153857269243756206085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14115076952717983349882893 5293153857269243756206085)
      ·
        refine ⟨992466348237983204288641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5293153857269243756206085 992466348237983204288641)
        ·
          refine ⟨744349761178487403216481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992466348237983204288641 744349761178487403216481)
          ·
            refine ⟨558262320883865552412361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744349761178487403216481 558262320883865552412361)
            ·
              refine ⟨418696740662899164309271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558262320883865552412361 418696740662899164309271)
              ·
                refine ⟨628045110994348746463907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418696740662899164309271 628045110994348746463907)
                ·
                  refine ⟨942067666491523119695861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628045110994348746463907 942067666491523119695861)
                  ·
                    refine ⟨88318843733580292471487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 942067666491523119695861 88318843733580292471487)
                    ·
                      rfl

theorem cell23_516001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_516001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516001 prefixEnd_516001 := by exact prefixLift 516001
  have htrace : WordTrace (prefixWord ++ tailWord_516001) baseStart_516001 baseEnd_516001 := by
    simpa [prefixWord, tailWord_516001, baseEnd_516001] using wordTrace_append hprefix tailTrace_516001
  have hstable : (prefixWord ++ tailWord_516001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516001).length < 2 ^ (prefixWord ++ tailWord_516001).sum := by decide
  have hdescent : baseEnd_516001 < baseStart_516001 := by decide
  rcases family_descends (prefixWord ++ tailWord_516001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516004 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_516004 : Nat := 118140960795 + 516004 * 2 ^ 59
def prefixEnd_516004 : Nat := 4983230072969 + 3 ^ 40 * 516004 * 2
def baseEnd_516004 : Nat := 264958071642704365676947

theorem tailTrace_516004 : CollatzResearch.WordTrace tailWord_516004 prefixEnd_516004 264958071642704365676947 := by
  unfold tailWord_516004
  simp only [CollatzResearch.WordTrace]
  refine ⟨9410106011306554656101533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12546808015075406208135377 9410106011306554656101533)
  ·
    refine ⟨3528789754239957996038075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9410106011306554656101533 3528789754239957996038075)
    ·
      refine ⟨5293184631359936994057113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3528789754239957996038075 5293184631359936994057113)
      ·
        refine ⟨3969888473519952745542835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5293184631359936994057113 3969888473519952745542835)
        ·
          refine ⟨5954832710279929118314253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969888473519952745542835 5954832710279929118314253)
          ·
            refine ⟨2233062266354973419367845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5954832710279929118314253 2233062266354973419367845)
            ·
              refine ⟨418699174941557516131471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2233062266354973419367845 418699174941557516131471)
              ·
                refine ⟨628048762412336274197207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418699174941557516131471 628048762412336274197207)
                ·
                  refine ⟨942073143618504411295811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628048762412336274197207 942073143618504411295811)
                  ·
                    refine ⟨1413109715427756616943717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 942073143618504411295811 1413109715427756616943717)
                    ·
                      refine ⟨264958071642704365676947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1413109715427756616943717 264958071642704365676947)
                      ·
                        rfl

theorem cell23_516004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_516004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516004 prefixEnd_516004 := by exact prefixLift 516004
  have htrace : WordTrace (prefixWord ++ tailWord_516004) baseStart_516004 baseEnd_516004 := by
    simpa [prefixWord, tailWord_516004, baseEnd_516004] using wordTrace_append hprefix tailTrace_516004
  have hstable : (prefixWord ++ tailWord_516004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516004).length < 2 ^ (prefixWord ++ tailWord_516004).sum := by decide
  have hdescent : baseEnd_516004 < baseStart_516004 := by decide
  rcases family_descends (prefixWord ++ tailWord_516004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516021 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_516021 : Nat := 118140960795 + 516021 * 2 ^ 59
def prefixEnd_516021 : Nat := 4983230072969 + 3 ^ 40 * 516021 * 2
def baseEnd_516021 : Nat := 264966800813830799164369

theorem tailTrace_516021 : CollatzResearch.WordTrace tailWord_516021 prefixEnd_516021 264966800813830799164369 := by
  unfold tailWord_516021
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820832063551521215571917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12547221375701014143714611 18820832063551521215571917)
  ·
    refine ⟨7057812023831820455839469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18820832063551521215571917 7057812023831820455839469)
    ·
      refine ⟨2646679508936932670939801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7057812023831820455839469 2646679508936932670939801)
      ·
        refine ⟨1985009631702699503204851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2646679508936932670939801 1985009631702699503204851)
        ·
          refine ⟨2977514447554049254807277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985009631702699503204851 2977514447554049254807277)
          ·
            refine ⟨1116567917832768470552729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2977514447554049254807277 1116567917832768470552729)
            ·
              refine ⟨837425938374576352914547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1116567917832768470552729 837425938374576352914547)
              ·
                refine ⟨1256138907561864529371821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837425938374576352914547 1256138907561864529371821)
                ·
                  refine ⟨471052090335699198514433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256138907561864529371821 471052090335699198514433)
                  ·
                    refine ⟨353289067751774398885825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 471052090335699198514433 353289067751774398885825)
                    ·
                      refine ⟨264966800813830799164369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353289067751774398885825 264966800813830799164369)
                      ·
                        rfl

theorem cell23_516021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_516021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516021 prefixEnd_516021 := by exact prefixLift 516021
  have htrace : WordTrace (prefixWord ++ tailWord_516021) baseStart_516021 baseEnd_516021 := by
    simpa [prefixWord, tailWord_516021, baseEnd_516021] using wordTrace_append hprefix tailTrace_516021
  have hstable : (prefixWord ++ tailWord_516021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516021).length < 2 ^ (prefixWord ++ tailWord_516021).sum := by decide
  have hdescent : baseEnd_516021 < baseStart_516021 := by decide
  rcases family_descends (prefixWord ++ tailWord_516021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516127 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 3]
def baseStart_516127 : Nat := 118140960795 + 516127 * 2 ^ 59
def prefixEnd_516127 : Nat := 4983230072969 + 3 ^ 40 * 516127 * 2
def baseEnd_516127 : Nat := 265021229763207384438881

theorem tailTrace_516127 : CollatzResearch.WordTrace tailWord_516127 prefixEnd_516127 265021229763207384438881 := by
  unfold tailWord_516127
  simp only [CollatzResearch.WordTrace]
  refine ⟨18824698201167501318930635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12549798800778334212620423 18824698201167501318930635)
  ·
    refine ⟨28237047301751251978395953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18824698201167501318930635 28237047301751251978395953)
    ·
      refine ⟨21177785476313438983796965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28237047301751251978395953 21177785476313438983796965)
      ·
        refine ⟨3970834776808769809461931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21177785476313438983796965 3970834776808769809461931)
        ·
          refine ⟨5956252165213154714192897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970834776808769809461931 5956252165213154714192897)
          ·
            refine ⟨4467189123909866035644673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5956252165213154714192897 4467189123909866035644673)
            ·
              refine ⟨3350391842932399526733505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467189123909866035644673 3350391842932399526733505)
              ·
                refine ⟨2512793882199299645050129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350391842932399526733505 2512793882199299645050129)
                ·
                  refine ⟨1884595411649474733787597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2512793882199299645050129 1884595411649474733787597)
                  ·
                    refine ⟨706723279368553025170349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884595411649474733787597 706723279368553025170349)
                    ·
                      refine ⟨265021229763207384438881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 706723279368553025170349 265021229763207384438881)
                      ·
                        rfl

theorem cell23_516127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_516127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516127 prefixEnd_516127 := by exact prefixLift 516127
  have htrace : WordTrace (prefixWord ++ tailWord_516127) baseStart_516127 baseEnd_516127 := by
    simpa [prefixWord, tailWord_516127, baseEnd_516127] using wordTrace_append hprefix tailTrace_516127
  have hstable : (prefixWord ++ tailWord_516127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516127).length < 2 ^ (prefixWord ++ tailWord_516127).sum := by decide
  have hdescent : baseEnd_516127 < baseStart_516127 := by decide
  rcases family_descends (prefixWord ++ tailWord_516127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516140 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_516140 : Nat := 118140960795 + 516140 * 2 ^ 59
def prefixEnd_516140 : Nat := 4983230072969 + 3 ^ 40 * 516140 * 2
def baseEnd_516140 : Nat := 265027905011715833576321

theorem tailTrace_516140 : CollatzResearch.WordTrace tailWord_516140 prefixEnd_516140 265027905011715833576321 := by
  unfold tailWord_516140
  simp only [CollatzResearch.WordTrace]
  refine ⟨9412586175060202269576937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12550114900080269692769249 9412586175060202269576937)
  ·
    refine ⟨7059439631295151702182703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9412586175060202269576937 7059439631295151702182703)
    ·
      refine ⟨10589159446942727553274055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7059439631295151702182703 10589159446942727553274055)
      ·
        refine ⟨15883739170414091329911083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10589159446942727553274055 15883739170414091329911083)
        ·
          refine ⟨23825608755621136994866625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15883739170414091329911083 23825608755621136994866625)
          ·
            refine ⟨17869206566715852746149969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23825608755621136994866625 17869206566715852746149969)
            ·
              refine ⟨13401904925036889559612477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17869206566715852746149969 13401904925036889559612477)
              ·
                refine ⟨5025714346888833584854679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13401904925036889559612477 5025714346888833584854679)
                ·
                  refine ⟨7538571520333250377282019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025714346888833584854679 7538571520333250377282019)
                  ·
                    refine ⟨11307857280499875565923029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7538571520333250377282019 11307857280499875565923029)
                    ·
                      refine ⟨265027905011715833576321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11307857280499875565923029 265027905011715833576321)
                      ·
                        rfl

theorem cell23_516140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_516140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516140 prefixEnd_516140 := by exact prefixLift 516140
  have htrace : WordTrace (prefixWord ++ tailWord_516140) baseStart_516140 baseEnd_516140 := by
    simpa [prefixWord, tailWord_516140, baseEnd_516140] using wordTrace_append hprefix tailTrace_516140
  have hstable : (prefixWord ++ tailWord_516140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516140).length < 2 ^ (prefixWord ++ tailWord_516140).sum := by decide
  have hdescent : baseEnd_516140 < baseStart_516140 := by decide
  rcases family_descends (prefixWord ++ tailWord_516140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516167 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_516167 : Nat := 118140960795 + 516167 * 2 ^ 59
def prefixEnd_516167 : Nat := 4983230072969 + 3 ^ 40 * 516167 * 2
def baseEnd_516167 : Nat := 265041768989387227938697

theorem tailTrace_516167 : CollatzResearch.WordTrace tailWord_516167 prefixEnd_516167 265041768989387227938697 := by
  unfold tailWord_516167
  simp only [CollatzResearch.WordTrace]
  refine ⟨18826157121022588150386755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12550771414015058766924503 18826157121022588150386755)
  ·
    refine ⟨28239235681533882225580133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18826157121022588150386755 28239235681533882225580133)
    ·
      refine ⟨5294856690287602917296275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28239235681533882225580133 5294856690287602917296275)
      ·
        refine ⟨7942285035431404375944413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5294856690287602917296275 7942285035431404375944413)
        ·
          refine ⟨2978356888286776640979155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7942285035431404375944413 2978356888286776640979155)
          ·
            refine ⟨4467535332430164961468733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978356888286776640979155 4467535332430164961468733)
            ·
              refine ⟨1675325749661311860550775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4467535332430164961468733 1675325749661311860550775)
              ·
                refine ⟨2512988624491967790826163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675325749661311860550775 2512988624491967790826163)
                ·
                  refine ⟨3769482936737951686239245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512988624491967790826163 3769482936737951686239245)
                  ·
                    refine ⟨1413556101276731882339717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769482936737951686239245 1413556101276731882339717)
                    ·
                      refine ⟨265041768989387227938697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1413556101276731882339717 265041768989387227938697)
                      ·
                        rfl

theorem cell23_516167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_516167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516167 prefixEnd_516167 := by exact prefixLift 516167
  have htrace : WordTrace (prefixWord ++ tailWord_516167) baseStart_516167 baseEnd_516167 := by
    simpa [prefixWord, tailWord_516167, baseEnd_516167] using wordTrace_append hprefix tailTrace_516167
  have hstable : (prefixWord ++ tailWord_516167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516167).length < 2 ^ (prefixWord ++ tailWord_516167).sum := by decide
  have hdescent : baseEnd_516167 < baseStart_516167 := by decide
  rcases family_descends (prefixWord ++ tailWord_516167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516177 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 7, 4]
def baseStart_516177 : Nat := 118140960795 + 516177 * 2 ^ 59
def prefixEnd_516177 : Nat := 4983230072969 + 3 ^ 40 * 516177 * 2
def baseEnd_516177 : Nat := 88348967931977396271217

theorem tailTrace_516177 : CollatzResearch.WordTrace tailWord_516177 prefixEnd_516177 88348967931977396271217 := by
  unfold tailWord_516177
  simp only [CollatzResearch.WordTrace]
  refine ⟨18826521850986359858250785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12551014567324239905500523 18826521850986359858250785)
  ·
    refine ⟨14119891388239769893688089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18826521850986359858250785 14119891388239769893688089)
    ·
      refine ⟨10589918541179827420266067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14119891388239769893688089 10589918541179827420266067)
      ·
        refine ⟨15884877811769741130399101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10589918541179827420266067 15884877811769741130399101)
        ·
          refine ⟨5956829179413652923899663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15884877811769741130399101 5956829179413652923899663)
          ·
            refine ⟨8935243769120479385849495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956829179413652923899663 8935243769120479385849495)
            ·
              refine ⟨13402865653680719078774243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935243769120479385849495 13402865653680719078774243)
              ·
                refine ⟨20104298480521078618161365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13402865653680719078774243 20104298480521078618161365)
                ·
                  refine ⟨471194495637212780113157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20104298480521078618161365 471194495637212780113157)
                  ·
                    refine ⟨88348967931977396271217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471194495637212780113157 88348967931977396271217)
                    ·
                      rfl

theorem cell23_516177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_516177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516177 prefixEnd_516177 := by exact prefixLift 516177
  have htrace : WordTrace (prefixWord ++ tailWord_516177) baseStart_516177 baseEnd_516177 := by
    simpa [prefixWord, tailWord_516177, baseEnd_516177] using wordTrace_append hprefix tailTrace_516177
  have hstable : (prefixWord ++ tailWord_516177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516177).length < 2 ^ (prefixWord ++ tailWord_516177).sum := by decide
  have hdescent : baseEnd_516177 < baseStart_516177 := by decide
  rcases family_descends (prefixWord ++ tailWord_516177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516184 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 2, 4, 2]
def baseStart_516184 : Nat := 118140960795 + 516184 * 2 ^ 59
def prefixEnd_516184 : Nat := 4983230072969 + 3 ^ 40 * 516184 * 2
def baseEnd_516184 : Nat := 265050498160513661426119

theorem tailTrace_516184 : CollatzResearch.WordTrace tailWord_516184 prefixEnd_516184 265050498160513661426119 := by
  unfold tailWord_516184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413388580980500026877803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12551184774640666702503737 9413388580980500026877803)
  ·
    refine ⟨14120082871470750040316705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9413388580980500026877803 14120082871470750040316705)
    ·
      refine ⟨10590062153603062530237529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14120082871470750040316705 10590062153603062530237529)
      ·
        refine ⟨7942546615202296897678147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10590062153603062530237529 7942546615202296897678147)
        ·
          refine ⟨11913819922803445346517221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7942546615202296897678147 11913819922803445346517221)
          ·
            refine ⟨2233841235525646002471979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11913819922803445346517221 2233841235525646002471979)
            ·
              refine ⟨3350761853288469003707969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233841235525646002471979 3350761853288469003707969)
              ·
                refine ⟨2513071389966351752780977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350761853288469003707969 2513071389966351752780977)
                ·
                  refine ⟨1884803542474763814585733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2513071389966351752780977 1884803542474763814585733)
                  ·
                    refine ⟨353400664214018215234825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1884803542474763814585733 353400664214018215234825)
                    ·
                      refine ⟨265050498160513661426119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353400664214018215234825 265050498160513661426119)
                      ·
                        rfl

theorem cell23_516184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_516184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516184 prefixEnd_516184 := by exact prefixLift 516184
  have htrace : WordTrace (prefixWord ++ tailWord_516184) baseStart_516184 baseEnd_516184 := by
    simpa [prefixWord, tailWord_516184, baseEnd_516184] using wordTrace_append hprefix tailTrace_516184
  have hstable : (prefixWord ++ tailWord_516184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516184).length < 2 ^ (prefixWord ++ tailWord_516184).sum := by decide
  have hdescent : baseEnd_516184 < baseStart_516184 := by decide
  rcases family_descends (prefixWord ++ tailWord_516184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516258 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 6]
def baseStart_516258 : Nat := 118140960795 + 516258 * 2 ^ 59
def prefixEnd_516258 : Nat := 4983230072969 + 3 ^ 40 * 516258 * 2
def baseEnd_516258 : Nat := 29454277303216263544531

theorem tailTrace_516258 : CollatzResearch.WordTrace tailWord_516258 prefixEnd_516258 29454277303216263544531 := by
  unfold tailWord_516258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4707369040923227672987357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12552984109128607127966285 4707369040923227672987357)
  ·
    refine ⟨1765263390346210377370259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4707369040923227672987357 1765263390346210377370259)
    ·
      refine ⟨2647895085519315566055389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1765263390346210377370259 2647895085519315566055389)
      ·
        refine ⟨992960657069743337270771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2647895085519315566055389 992960657069743337270771)
        ·
          refine ⟨1489440985604615005906157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992960657069743337270771 1489440985604615005906157)
          ·
            refine ⟨558540369601730627214809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1489440985604615005906157 558540369601730627214809)
            ·
              refine ⟨418905277201297970411107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558540369601730627214809 418905277201297970411107)
              ·
                refine ⟨628357915801946955616661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418905277201297970411107 628357915801946955616661)
                ·
                  refine ⟨29454277303216263544531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 628357915801946955616661 29454277303216263544531)
                  ·
                    rfl

theorem cell23_516258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_516258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516258 prefixEnd_516258 := by exact prefixLift 516258
  have htrace : WordTrace (prefixWord ++ tailWord_516258) baseStart_516258 baseEnd_516258 := by
    simpa [prefixWord, tailWord_516258, baseEnd_516258] using wordTrace_append hprefix tailTrace_516258
  have hstable : (prefixWord ++ tailWord_516258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516258).length < 2 ^ (prefixWord ++ tailWord_516258).sum := by decide
  have hdescent : baseEnd_516258 < baseStart_516258 := by decide
  rcases family_descends (prefixWord ++ tailWord_516258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516274 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_516274 : Nat := 118140960795 + 516274 * 2 ^ 59
def prefixEnd_516274 : Nat := 4983230072969 + 3 ^ 40 * 516274 * 2
def baseEnd_516274 : Nat := 265096711419418309300705

theorem tailTrace_516274 : CollatzResearch.WordTrace tailWord_516274 prefixEnd_516274 265096711419418309300705 := by
  unfold tailWord_516274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4707514932908736356132969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12553373154423296949687917 4707514932908736356132969)
  ·
    refine ⟨3530636199681552267099727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4707514932908736356132969 3530636199681552267099727)
    ·
      refine ⟨5295954299522328400649591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3530636199681552267099727 5295954299522328400649591)
      ·
        refine ⟨7943931449283492600974387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295954299522328400649591 7943931449283492600974387)
        ·
          refine ⟨11915897173925238901461581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943931449283492600974387 11915897173925238901461581)
          ·
            refine ⟨4468461440221964588048093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11915897173925238901461581 4468461440221964588048093)
            ·
              refine ⟨1675673040083236720518035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4468461440221964588048093 1675673040083236720518035)
              ·
                refine ⟨2513509560124855080777053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675673040083236720518035 2513509560124855080777053)
                ·
                  refine ⟨942566085046820655291395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2513509560124855080777053 942566085046820655291395)
                  ·
                    refine ⟨1413849127570230982937093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 942566085046820655291395 1413849127570230982937093)
                    ·
                      refine ⟨265096711419418309300705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1413849127570230982937093 265096711419418309300705)
                      ·
                        rfl

theorem cell23_516274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_516274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516274 prefixEnd_516274 := by exact prefixLift 516274
  have htrace : WordTrace (prefixWord ++ tailWord_516274) baseStart_516274 baseEnd_516274 := by
    simpa [prefixWord, tailWord_516274, baseEnd_516274] using wordTrace_append hprefix tailTrace_516274
  have hstable : (prefixWord ++ tailWord_516274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516274).length < 2 ^ (prefixWord ++ tailWord_516274).sum := by decide
  have hdescent : baseEnd_516274 < baseStart_516274 := by decide
  rcases family_descends (prefixWord ++ tailWord_516274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516302 : List Nat := [4, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_516302 : Nat := 118140960795 + 516302 * 2 ^ 59
def prefixEnd_516302 : Nat := 4983230072969 + 3 ^ 40 * 516302 * 2
def baseEnd_516302 : Nat := 265111088877744199750577

theorem tailTrace_516302 : CollatzResearch.WordTrace tailWord_516302 prefixEnd_516302 265111088877744199750577 := by
  unfold tailWord_516302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353885121941688275818895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12554053983689004137700773 2353885121941688275818895)
  ·
    refine ⟨3530827682912532413728343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2353885121941688275818895 3530827682912532413728343)
    ·
      refine ⟨5296241524368798620592515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3530827682912532413728343 5296241524368798620592515)
      ·
        refine ⟨7944362286553197930888773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296241524368798620592515 7944362286553197930888773)
        ·
          refine ⟨1489567928728724612041645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7944362286553197930888773 1489567928728724612041645)
          ·
            refine ⟨558587973273271729515617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1489567928728724612041645 558587973273271729515617)
            ·
              refine ⟨418940979954953797136713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558587973273271729515617 418940979954953797136713)
              ·
                refine ⟨314205734966215347852535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418940979954953797136713 314205734966215347852535)
                ·
                  refine ⟨471308602449323021778803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314205734966215347852535 471308602449323021778803)
                  ·
                    refine ⟨706962903673984532668205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 471308602449323021778803 706962903673984532668205)
                    ·
                      refine ⟨265111088877744199750577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 706962903673984532668205 265111088877744199750577)
                      ·
                        rfl

theorem cell23_516302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_516302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516302 prefixEnd_516302 := by exact prefixLift 516302
  have htrace : WordTrace (prefixWord ++ tailWord_516302) baseStart_516302 baseEnd_516302 := by
    simpa [prefixWord, tailWord_516302, baseEnd_516302] using wordTrace_append hprefix tailTrace_516302
  have hstable : (prefixWord ++ tailWord_516302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516302).length < 2 ^ (prefixWord ++ tailWord_516302).sum := by decide
  have hdescent : baseEnd_516302 < baseStart_516302 := by decide
  rcases family_descends (prefixWord ++ tailWord_516302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516375 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 2, 1, 3]
def baseStart_516375 : Nat := 118140960795 + 516375 * 2 ^ 59
def prefixEnd_516375 : Nat := 4983230072969 + 3 ^ 40 * 516375 * 2
def baseEnd_516375 : Nat := 265148572965522414137741

theorem tailTrace_516375 : CollatzResearch.WordTrace tailWord_516375 prefixEnd_516375 265148572965522414137741 := by
  unfold tailWord_516375
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833743504269039673958579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12555829002846026449305719 18833743504269039673958579)
  ·
    refine ⟨28250615256403559510937869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18833743504269039673958579 28250615256403559510937869)
    ·
      refine ⟨10593980721151334816601701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28250615256403559510937869 10593980721151334816601701)
      ·
        refine ⟨1986371385215875278112819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10593980721151334816601701 1986371385215875278112819)
        ·
          refine ⟨2979557077823812917169229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986371385215875278112819 2979557077823812917169229)
          ·
            refine ⟨1117333904183929843938461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2979557077823812917169229 1117333904183929843938461)
            ·
              refine ⟨419000214068973691476923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1117333904183929843938461 419000214068973691476923)
              ·
                refine ⟨628500321103460537215385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419000214068973691476923 628500321103460537215385)
                ·
                  refine ⟨471375240827595402911539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628500321103460537215385 471375240827595402911539)
                  ·
                    refine ⟨707062861241393104367309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 471375240827595402911539 707062861241393104367309)
                    ·
                      refine ⟨265148572965522414137741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 707062861241393104367309 265148572965522414137741)
                      ·
                        rfl

theorem cell23_516375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_516375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516375 prefixEnd_516375 := by exact prefixLift 516375
  have htrace : WordTrace (prefixWord ++ tailWord_516375) baseStart_516375 baseEnd_516375 := by
    simpa [prefixWord, tailWord_516375, baseEnd_516375] using wordTrace_append hprefix tailTrace_516375
  have hstable : (prefixWord ++ tailWord_516375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516375).length < 2 ^ (prefixWord ++ tailWord_516375).sum := by decide
  have hdescent : baseEnd_516375 < baseStart_516375 := by decide
  rcases family_descends (prefixWord ++ tailWord_516375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516377 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_516377 : Nat := 118140960795 + 516377 * 2 ^ 59
def prefixEnd_516377 : Nat := 4983230072969 + 3 ^ 40 * 516377 * 2
def baseEnd_516377 : Nat := 265149599926831406312731

theorem tailTrace_516377 : CollatzResearch.WordTrace tailWord_516377 prefixEnd_516377 265149599926831406312731 := by
  unfold tailWord_516377
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833816450261794015531385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12555877633507862677020923 18833816450261794015531385)
  ·
    refine ⟨14125362337696345511648539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18833816450261794015531385 14125362337696345511648539)
    ·
      refine ⟨21188043506544518267472809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14125362337696345511648539 21188043506544518267472809)
      ·
        refine ⟨15891032629908388700604607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21188043506544518267472809 15891032629908388700604607)
        ·
          refine ⟨23836548944862583050906911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15891032629908388700604607 23836548944862583050906911)
          ·
            refine ⟨35754823417293874576360367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23836548944862583050906911 35754823417293874576360367)
            ·
              refine ⟨53632235125940811864540551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35754823417293874576360367 53632235125940811864540551)
              ·
                refine ⟨80448352688911217796810827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53632235125940811864540551 80448352688911217796810827)
                ·
                  refine ⟨120672529033366826695216241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80448352688911217796810827 120672529033366826695216241)
                  ·
                    refine ⟨90504396775025120021412181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120672529033366826695216241 90504396775025120021412181)
                    ·
                      refine ⟨265149599926831406312731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 90504396775025120021412181 265149599926831406312731)
                      ·
                        rfl

theorem cell23_516377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_516377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516377 prefixEnd_516377 := by exact prefixLift 516377
  have htrace : WordTrace (prefixWord ++ tailWord_516377) baseStart_516377 baseEnd_516377 := by
    simpa [prefixWord, tailWord_516377, baseEnd_516377] using wordTrace_append hprefix tailTrace_516377
  have hstable : (prefixWord ++ tailWord_516377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516377).length < 2 ^ (prefixWord ++ tailWord_516377).sum := by decide
  have hdescent : baseEnd_516377 < baseStart_516377 := by decide
  rcases family_descends (prefixWord ++ tailWord_516377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516401 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_516401 : Nat := 118140960795 + 516401 * 2 ^ 59
def prefixEnd_516401 : Nat := 4983230072969 + 3 ^ 40 * 516401 * 2
def baseEnd_516401 : Nat := 265161923462539312412621

theorem tailTrace_516401 : CollatzResearch.WordTrace tailWord_516401 prefixEnd_516401 265161923462539312412621 := by
  unfold tailWord_516401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834691802174846114405057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12556461201449897409603371 18834691802174846114405057)
  ·
    refine ⟨14126018851631134585803793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18834691802174846114405057 14126018851631134585803793)
    ·
      refine ⟨10594514138723350939352845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14126018851631134585803793 10594514138723350939352845)
      ·
        refine ⟨3972942802021256602257317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10594514138723350939352845 3972942802021256602257317)
        ·
          refine ⟨744926775378985612923247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3972942802021256602257317 744926775378985612923247)
          ·
            refine ⟨1117390163068478419384871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744926775378985612923247 1117390163068478419384871)
            ·
              refine ⟨1676085244602717629077307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117390163068478419384871 1676085244602717629077307)
              ·
                refine ⟨2514127866904076443615961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676085244602717629077307 2514127866904076443615961)
                ·
                  refine ⟨1885595900178057332711971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514127866904076443615961 1885595900178057332711971)
                  ·
                    refine ⟨2828393850267085999067957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1885595900178057332711971 2828393850267085999067957)
                    ·
                      refine ⟨265161923462539312412621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2828393850267085999067957 265161923462539312412621)
                      ·
                        rfl

theorem cell23_516401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_516401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516401 prefixEnd_516401 := by exact prefixLift 516401
  have htrace : WordTrace (prefixWord ++ tailWord_516401) baseStart_516401 baseEnd_516401 := by
    simpa [prefixWord, tailWord_516401, baseEnd_516401] using wordTrace_append hprefix tailTrace_516401
  have hstable : (prefixWord ++ tailWord_516401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516401).length < 2 ^ (prefixWord ++ tailWord_516401).sum := by decide
  have hdescent : baseEnd_516401 < baseStart_516401 := by decide
  rcases family_descends (prefixWord ++ tailWord_516401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516432 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 2, 2, 2]
def baseStart_516432 : Nat := 118140960795 + 516432 * 2 ^ 59
def prefixEnd_516432 : Nat := 4983230072969 + 3 ^ 40 * 516432 * 2
def baseEnd_516432 : Nat := 265177841362828691124979

theorem tailTrace_516432 : CollatzResearch.WordTrace tailWord_516432 prefixEnd_516432 265177841362828691124979 := by
  unfold tailWord_516432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417911232531269204391775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12557214976708358939189033 9417911232531269204391775)
  ·
    refine ⟨14126866848796903806587663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9417911232531269204391775 14126866848796903806587663)
    ·
      refine ⟨21190300273195355709881495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14126866848796903806587663 21190300273195355709881495)
      ·
        refine ⟨31785450409793033564822243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21190300273195355709881495 31785450409793033564822243)
        ·
          refine ⟨47678175614689550347233365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31785450409793033564822243 47678175614689550347233365)
          ·
            refine ⟨558728620484643168131641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 47678175614689550347233365 558728620484643168131641)
            ·
              refine ⟨419046465363482376098731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558728620484643168131641 419046465363482376098731)
              ·
                refine ⟨628569698045223564148097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419046465363482376098731 628569698045223564148097)
                ·
                  refine ⟨471427273533917673111073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628569698045223564148097 471427273533917673111073)
                  ·
                    refine ⟨353570455150438254833305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 471427273533917673111073 353570455150438254833305)
                    ·
                      refine ⟨265177841362828691124979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353570455150438254833305 265177841362828691124979)
                      ·
                        rfl

theorem cell23_516432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 2, 2].length) (baseStart_516432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516432 prefixEnd_516432 := by exact prefixLift 516432
  have htrace : WordTrace (prefixWord ++ tailWord_516432) baseStart_516432 baseEnd_516432 := by
    simpa [prefixWord, tailWord_516432, baseEnd_516432] using wordTrace_append hprefix tailTrace_516432
  have hstable : (prefixWord ++ tailWord_516432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516432).length < 2 ^ (prefixWord ++ tailWord_516432).sum := by decide
  have hdescent : baseEnd_516432 < baseStart_516432 := by decide
  rcases family_descends (prefixWord ++ tailWord_516432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516434 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_516434 : Nat := 118140960795 + 516434 * 2 ^ 59
def prefixEnd_516434 : Nat := 4983230072969 + 3 ^ 40 * 516434 * 2
def baseEnd_516434 : Nat := 88392956108045894433323

theorem tailTrace_516434 : CollatzResearch.WordTrace tailWord_516434 prefixEnd_516434 88392956108045894433323 := by
  unfold tailWord_516434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708973852763823187589089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12557263607370195166904237 4708973852763823187589089)
  ·
    refine ⟨3531730389572867390691817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4708973852763823187589089 3531730389572867390691817)
    ·
      refine ⟨2648797792179650543018863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3531730389572867390691817 2648797792179650543018863)
      ·
        refine ⟨3973196688269475814528295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648797792179650543018863 3973196688269475814528295)
        ·
          refine ⟨5959795032404213721792443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973196688269475814528295 5959795032404213721792443)
          ·
            refine ⟨8939692548606320582688665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959795032404213721792443 8939692548606320582688665)
            ·
              refine ⟨6704769411454740437016499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8939692548606320582688665 6704769411454740437016499)
              ·
                refine ⟨10057154117182110655524749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704769411454740437016499 10057154117182110655524749)
                ·
                  refine ⟨3771432793943291495821781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10057154117182110655524749 3771432793943291495821781)
                  ·
                    refine ⟨88392956108045894433323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3771432793943291495821781 88392956108045894433323)
                    ·
                      rfl

theorem cell23_516434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_516434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516434 prefixEnd_516434 := by exact prefixLift 516434
  have htrace : WordTrace (prefixWord ++ tailWord_516434) baseStart_516434 baseEnd_516434 := by
    simpa [prefixWord, tailWord_516434, baseEnd_516434] using wordTrace_append hprefix tailTrace_516434
  have hstable : (prefixWord ++ tailWord_516434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516434).length < 2 ^ (prefixWord ++ tailWord_516434).sum := by decide
  have hdescent : baseEnd_516434 < baseStart_516434 := by decide
  rcases family_descends (prefixWord ++ tailWord_516434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516451 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 2, 5]
def baseStart_516451 : Nat := 118140960795 + 516451 * 2 ^ 59
def prefixEnd_516451 : Nat := 4983230072969 + 3 ^ 40 * 516451 * 2
def baseEnd_516451 : Nat := 88395865831754705595797

theorem tailTrace_516451 : CollatzResearch.WordTrace tailWord_516451 prefixEnd_516451 88395865831754705595797 := by
  unfold tailWord_516451
  simp only [CollatzResearch.WordTrace]
  refine ⟨18836515451993704653725207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12557676967995803102483471 18836515451993704653725207)
  ·
    refine ⟨28254773177990556980587811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18836515451993704653725207 28254773177990556980587811)
    ·
      refine ⟨42382159766985835470881717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28254773177990556980587811 42382159766985835470881717)
      ·
        refine ⟨3973327478154922075395161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42382159766985835470881717 3973327478154922075395161)
        ·
          refine ⟨2979995608616191556546371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3973327478154922075395161 2979995608616191556546371)
          ·
            refine ⟨4469993412924287334819557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979995608616191556546371 4469993412924287334819557)
            ·
              refine ⟨838123764923303875278667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4469993412924287334819557 838123764923303875278667)
              ·
                refine ⟨1257185647384955812918001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838123764923303875278667 1257185647384955812918001)
                ·
                  refine ⟨942889235538716859688501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1257185647384955812918001 942889235538716859688501)
                  ·
                    refine ⟨88395865831754705595797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 942889235538716859688501 88395865831754705595797)
                    ·
                      rfl

theorem cell23_516451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 5].length) (baseStart_516451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516451 prefixEnd_516451 := by exact prefixLift 516451
  have htrace : WordTrace (prefixWord ++ tailWord_516451) baseStart_516451 baseEnd_516451 := by
    simpa [prefixWord, tailWord_516451, baseEnd_516451] using wordTrace_append hprefix tailTrace_516451
  have hstable : (prefixWord ++ tailWord_516451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516451).length < 2 ^ (prefixWord ++ tailWord_516451).sum := by decide
  have hdescent : baseEnd_516451 < baseStart_516451 := by decide
  rcases family_descends (prefixWord ++ tailWord_516451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516488 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_516488 : Nat := 118140960795 + 516488 * 2 ^ 59
def prefixEnd_516488 : Nat := 4983230072969 + 3 ^ 40 * 516488 * 2
def baseEnd_516488 : Nat := 265206596279480472024721

theorem tailTrace_516488 : CollatzResearch.WordTrace tailWord_516488 prefixEnd_516488 265206596279480472024721 := by
  unfold tailWord_516488
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418932476429829986411059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12558576635239773315214745 9418932476429829986411059)
  ·
    refine ⟨14128398714644744979616589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9418932476429829986411059 14128398714644744979616589)
    ·
      refine ⟨5298149517991779367356221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14128398714644744979616589 5298149517991779367356221)
      ·
        refine ⟨1986806069246917262758583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5298149517991779367356221 1986806069246917262758583)
        ·
          refine ⟨2980209103870375894137875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986806069246917262758583 2980209103870375894137875)
          ·
            refine ⟨4470313655805563841206813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980209103870375894137875 4470313655805563841206813)
            ·
              refine ⟨1676367620927086440452555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4470313655805563841206813 1676367620927086440452555)
              ·
                refine ⟨2514551431390629660678833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676367620927086440452555 2514551431390629660678833)
                ·
                  refine ⟨1885913573542972245509125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514551431390629660678833 1885913573542972245509125)
                  ·
                    refine ⟨353608795039307296032961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1885913573542972245509125 353608795039307296032961)
                    ·
                      refine ⟨265206596279480472024721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353608795039307296032961 265206596279480472024721)
                      ·
                        rfl

theorem cell23_516488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_516488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516488 prefixEnd_516488 := by exact prefixLift 516488
  have htrace : WordTrace (prefixWord ++ tailWord_516488) baseStart_516488 baseEnd_516488 := by
    simpa [prefixWord, tailWord_516488, baseEnd_516488] using wordTrace_append hprefix tailTrace_516488
  have hstable : (prefixWord ++ tailWord_516488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516488).length < 2 ^ (prefixWord ++ tailWord_516488).sum := by decide
  have hdescent : baseEnd_516488 < baseStart_516488 := by decide
  rcases family_descends (prefixWord ++ tailWord_516488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516502 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_516502 : Nat := 118140960795 + 516502 * 2 ^ 59
def prefixEnd_516502 : Nat := 4983230072969 + 3 ^ 40 * 516502 * 2
def baseEnd_516502 : Nat := 88404595002881139083219

theorem tailTrace_516502 : CollatzResearch.WordTrace tailWord_516502 prefixEnd_516502 88404595002881139083219 := by
  unfold tailWord_516502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177398473425558772739485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12558917049872626909221173 1177398473425558772739485)
  ·
    refine ⟨441524427534584539777307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1177398473425558772739485 441524427534584539777307)
    ·
      refine ⟨662286641301876809665961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441524427534584539777307 662286641301876809665961)
      ·
        refine ⟨496714980976407607249471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662286641301876809665961 496714980976407607249471)
        ·
          refine ⟨745072471464611410874207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496714980976407607249471 745072471464611410874207)
          ·
            refine ⟨1117608707196917116311311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745072471464611410874207 1117608707196917116311311)
            ·
              refine ⟨1676413060795375674466967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117608707196917116311311 1676413060795375674466967)
              ·
                refine ⟨2514619591193063511700451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676413060795375674466967 2514619591193063511700451)
                ·
                  refine ⟨3771929386789595267550677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514619591193063511700451 3771929386789595267550677)
                  ·
                    refine ⟨88404595002881139083219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3771929386789595267550677 88404595002881139083219)
                    ·
                      rfl

theorem cell23_516502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_516502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516502 prefixEnd_516502 := by exact prefixLift 516502
  have htrace : WordTrace (prefixWord ++ tailWord_516502) baseStart_516502 baseEnd_516502 := by
    simpa [prefixWord, tailWord_516502, baseEnd_516502] using wordTrace_append hprefix tailTrace_516502
  have hstable : (prefixWord ++ tailWord_516502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516502).length < 2 ^ (prefixWord ++ tailWord_516502).sum := by decide
  have hdescent : baseEnd_516502 < baseStart_516502 := by decide
  rcases family_descends (prefixWord ++ tailWord_516502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516515 : List Nat := [1, 1, 1, 4, 1, 5, 2, 3, 1, 4]
def baseStart_516515 : Nat := 118140960795 + 516515 * 2 ^ 59
def prefixEnd_516515 : Nat := 4983230072969 + 3 ^ 40 * 516515 * 2
def baseEnd_516515 : Nat := 88406820085717288795699

theorem tailTrace_516515 : CollatzResearch.WordTrace tailWord_516515 prefixEnd_516515 88406820085717288795699 := by
  unfold tailWord_516515
  simp only [CollatzResearch.WordTrace]
  refine ⟨18838849723761843584054999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12559233149174562389369999 18838849723761843584054999)
  ·
    refine ⟨28258274585642765376082499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18838849723761843584054999 28258274585642765376082499)
    ·
      refine ⟨42387411878464148064123749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28258274585642765376082499 42387411878464148064123749)
      ·
        refine ⟨7947639727212027762023203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42387411878464148064123749 7947639727212027762023203)
        ·
          refine ⟨11921459590818041643034805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947639727212027762023203 11921459590818041643034805)
          ·
            refine ⟨1117636836639191404034513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11921459590818041643034805 1117636836639191404034513)
            ·
              refine ⟨838227627479393553025885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117636836639191404034513 838227627479393553025885)
              ·
                refine ⟨314335360304772582384707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838227627479393553025885 314335360304772582384707)
                ·
                  refine ⟨471503040457158873577061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314335360304772582384707 471503040457158873577061)
                  ·
                    refine ⟨88406820085717288795699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471503040457158873577061 88406820085717288795699)
                    ·
                      rfl

theorem cell23_516515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 4].length) (baseStart_516515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516515 prefixEnd_516515 := by exact prefixLift 516515
  have htrace : WordTrace (prefixWord ++ tailWord_516515) baseStart_516515 baseEnd_516515 := by
    simpa [prefixWord, tailWord_516515, baseEnd_516515] using wordTrace_append hprefix tailTrace_516515
  have hstable : (prefixWord ++ tailWord_516515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516515).length < 2 ^ (prefixWord ++ tailWord_516515).sum := by decide
  have hdescent : baseEnd_516515 < baseStart_516515 := by decide
  rcases family_descends (prefixWord ++ tailWord_516515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516561 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_516561 : Nat := 118140960795 + 516561 * 2 ^ 59
def prefixEnd_516561 : Nat := 4983230072969 + 3 ^ 40 * 516561 * 2
def baseEnd_516561 : Nat := 265244080367258686411885

theorem tailTrace_516561 : CollatzResearch.WordTrace tailWord_516561 prefixEnd_516561 265244080367258686411885 := by
  unfold tailWord_516561
  simp only [CollatzResearch.WordTrace]
  refine ⟨18840527481595193440229537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12560351654396795626819691 18840527481595193440229537)
  ·
    refine ⟨14130395611196395080172153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18840527481595193440229537 14130395611196395080172153)
    ·
      refine ⟨10597796708397296310129115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14130395611196395080172153 10597796708397296310129115)
      ·
        refine ⟨15896695062595944465193673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10597796708397296310129115 15896695062595944465193673)
        ·
          refine ⟨11922521296946958348895255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15896695062595944465193673 11922521296946958348895255)
          ·
            refine ⟨17883781945420437523342883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11922521296946958348895255 17883781945420437523342883)
            ·
              refine ⟨26825672918130656285014325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17883781945420437523342883 26825672918130656285014325)
              ·
                refine ⟨2514906836074749026720093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26825672918130656285014325 2514906836074749026720093)
                ·
                  refine ⟨943090063528030885020035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2514906836074749026720093 943090063528030885020035)
                  ·
                    refine ⟨1414635095292046327530053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 943090063528030885020035 1414635095292046327530053)
                    ·
                      refine ⟨265244080367258686411885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1414635095292046327530053 265244080367258686411885)
                      ·
                        rfl

theorem cell23_516561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_516561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516561 prefixEnd_516561 := by exact prefixLift 516561
  have htrace : WordTrace (prefixWord ++ tailWord_516561) baseStart_516561 baseEnd_516561 := by
    simpa [prefixWord, tailWord_516561, baseEnd_516561] using wordTrace_append hprefix tailTrace_516561
  have hstable : (prefixWord ++ tailWord_516561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516561).length < 2 ^ (prefixWord ++ tailWord_516561).sum := by decide
  have hdescent : baseEnd_516561 < baseStart_516561 := by decide
  rcases family_descends (prefixWord ++ tailWord_516561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516588 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_516588 : Nat := 118140960795 + 516588 * 2 ^ 59
def prefixEnd_516588 : Nat := 4983230072969 + 3 ^ 40 * 516588 * 2
def baseEnd_516588 : Nat := 88419314781643360258087

theorem tailTrace_516588 : CollatzResearch.WordTrace tailWord_516588 prefixEnd_516588 88419314781643360258087 := by
  unfold tailWord_516588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420756126248688525731209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12561008168331584700974945 9420756126248688525731209)
  ·
    refine ⟨7065567094686516394298407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9420756126248688525731209 7065567094686516394298407)
    ·
      refine ⟨10598350642029774591447611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7065567094686516394298407 10598350642029774591447611)
      ·
        refine ⟨15897525963044661887171417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10598350642029774591447611 15897525963044661887171417)
        ·
          refine ⟨11923144472283496415378563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15897525963044661887171417 11923144472283496415378563)
          ·
            refine ⟨17884716708425244623067845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11923144472283496415378563 17884716708425244623067845)
            ·
              refine ⟨3353384382829733366825221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17884716708425244623067845 3353384382829733366825221)
              ·
                refine ⟨628759571780575006279729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3353384382829733366825221 628759571780575006279729)
                ·
                  refine ⟨471569678835431254709797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628759571780575006279729 471569678835431254709797)
                  ·
                    refine ⟨88419314781643360258087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471569678835431254709797 88419314781643360258087)
                    ·
                      rfl

theorem cell23_516588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_516588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516588 prefixEnd_516588 := by exact prefixLift 516588
  have htrace : WordTrace (prefixWord ++ tailWord_516588) baseStart_516588 baseEnd_516588 := by
    simpa [prefixWord, tailWord_516588, baseEnd_516588] using wordTrace_append hprefix tailTrace_516588
  have hstable : (prefixWord ++ tailWord_516588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516588).length < 2 ^ (prefixWord ++ tailWord_516588).sum := by decide
  have hdescent : baseEnd_516588 < baseStart_516588 := by decide
  rcases family_descends (prefixWord ++ tailWord_516588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516598 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_516598 : Nat := 118140960795 + 516598 * 2 ^ 59
def prefixEnd_516598 : Nat := 4983230072969 + 3 ^ 40 * 516598 * 2
def baseEnd_516598 : Nat := 265263079151475041649215

theorem tailTrace_516598 : CollatzResearch.WordTrace tailWord_516598 prefixEnd_516598 265263079151475041649215 := by
  unfold tailWord_516598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177617311403821797457903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12561251321640765839550965 1177617311403821797457903)
  ·
    refine ⟨1766425967105732696186855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1177617311403821797457903 1766425967105732696186855)
    ·
      refine ⟨2649638950658599044280283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766425967105732696186855 2649638950658599044280283)
      ·
        refine ⟨3974458425987898566420425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649638950658599044280283 3974458425987898566420425)
        ·
          refine ⟨2980843819490923924815319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3974458425987898566420425 2980843819490923924815319)
          ·
            refine ⟨4471265729236385887222979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980843819490923924815319 4471265729236385887222979)
            ·
              refine ⟨6706898593854578830834469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471265729236385887222979 6706898593854578830834469)
              ·
                refine ⟨1257543486347733530781463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6706898593854578830834469 1257543486347733530781463)
                ·
                  refine ⟨1886315229521600296172195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257543486347733530781463 1886315229521600296172195)
                  ·
                    refine ⟨2829472844282400444258293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1886315229521600296172195 2829472844282400444258293)
                    ·
                      refine ⟨265263079151475041649215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2829472844282400444258293 265263079151475041649215)
                      ·
                        rfl

theorem cell23_516598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_516598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516598 prefixEnd_516598 := by exact prefixLift 516598
  have htrace : WordTrace (prefixWord ++ tailWord_516598) baseStart_516598 baseEnd_516598 := by
    simpa [prefixWord, tailWord_516598, baseEnd_516598] using wordTrace_append hprefix tailTrace_516598
  have hstable : (prefixWord ++ tailWord_516598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516598).length < 2 ^ (prefixWord ++ tailWord_516598).sum := by decide
  have hdescent : baseEnd_516598 < baseStart_516598 := by decide
  rcases family_descends (prefixWord ++ tailWord_516598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516612 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_516612 : Nat := 118140960795 + 516612 * 2 ^ 59
def prefixEnd_516612 : Nat := 4983230072969 + 3 ^ 40 * 516612 * 2
def baseEnd_516612 : Nat := 265270267880637986874151

theorem tailTrace_516612 : CollatzResearch.WordTrace tailWord_516612 prefixEnd_516612 265270267880637986874151 := by
  unfold tailWord_516612
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421193802205214575168045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12561591736273619433557393 9421193802205214575168045)
  ·
    refine ⟨3532947675826955465688017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9421193802205214575168045 3532947675826955465688017)
    ·
      refine ⟨2649710756870216599266013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3532947675826955465688017 2649710756870216599266013)
      ·
        refine ⟨993641533826331224724755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2649710756870216599266013 993641533826331224724755)
        ·
          refine ⟨1490462300739496837087133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993641533826331224724755 1490462300739496837087133)
          ·
            refine ⟨558923362777311313907675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1490462300739496837087133 558923362777311313907675)
            ·
              refine ⟨838385044165966970861513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558923362777311313907675 838385044165966970861513)
              ·
                refine ⟨628788783124475228146135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838385044165966970861513 628788783124475228146135)
                ·
                  refine ⟨943183174686712842219203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628788783124475228146135 943183174686712842219203)
                  ·
                    refine ⟨1414774762030069263328805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 943183174686712842219203 1414774762030069263328805)
                    ·
                      refine ⟨265270267880637986874151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1414774762030069263328805 265270267880637986874151)
                      ·
                        rfl

theorem cell23_516612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_516612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516612 prefixEnd_516612 := by exact prefixLift 516612
  have htrace : WordTrace (prefixWord ++ tailWord_516612) baseStart_516612 baseEnd_516612 := by
    simpa [prefixWord, tailWord_516612, baseEnd_516612] using wordTrace_append hprefix tailTrace_516612
  have hstable : (prefixWord ++ tailWord_516612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516612).length < 2 ^ (prefixWord ++ tailWord_516612).sum := by decide
  have hdescent : baseEnd_516612 < baseStart_516612 := by decide
  rcases family_descends (prefixWord ++ tailWord_516612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516615 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_516615 : Nat := 118140960795 + 516615 * 2 ^ 59
def prefixEnd_516615 : Nat := 4983230072969 + 3 ^ 40 * 516615 * 2
def baseEnd_516615 : Nat := 265271808322601475136637

theorem tailTrace_516615 : CollatzResearch.WordTrace tailWord_516615 prefixEnd_516615 265271808322601475136637 := by
  unfold tailWord_516615
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842497023399560662695299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12561664682266373775130199 18842497023399560662695299)
  ·
    refine ⟨28263745535099340994042949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18842497023399560662695299 28263745535099340994042949)
    ·
      refine ⟨5299452287831126436383053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28263745535099340994042949 5299452287831126436383053)
      ·
        refine ⟨1987294607936672413643645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5299452287831126436383053 1987294607936672413643645)
        ·
          refine ⟨745235477976252155116367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1987294607936672413643645 745235477976252155116367)
          ·
            refine ⟨1117853216964378232674551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745235477976252155116367 1117853216964378232674551)
            ·
              refine ⟨1676779825446567349011827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117853216964378232674551 1676779825446567349011827)
              ·
                refine ⟨2515169738169851023517741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676779825446567349011827 2515169738169851023517741)
                ·
                  refine ⟨943188651813694133819153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2515169738169851023517741 943188651813694133819153)
                  ·
                    refine ⟨707391488860270600364365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943188651813694133819153 707391488860270600364365)
                    ·
                      refine ⟨265271808322601475136637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 707391488860270600364365 265271808322601475136637)
                      ·
                        rfl

theorem cell23_516615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_516615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516615 prefixEnd_516615 := by exact prefixLift 516615
  have htrace : WordTrace (prefixWord ++ tailWord_516615) baseStart_516615 baseEnd_516615 := by
    simpa [prefixWord, tailWord_516615, baseEnd_516615] using wordTrace_append hprefix tailTrace_516615
  have hstable : (prefixWord ++ tailWord_516615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516615).length < 2 ^ (prefixWord ++ tailWord_516615).sum := by decide
  have hdescent : baseEnd_516615 < baseStart_516615 := by decide
  rcases family_descends (prefixWord ++ tailWord_516615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516632 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 1, 2, 3]
def baseStart_516632 : Nat := 118140960795 + 516632 * 2 ^ 59
def prefixEnd_516632 : Nat := 4983230072969 + 3 ^ 40 * 516632 * 2
def baseEnd_516632 : Nat := 265280537493727908624059

theorem tailTrace_516632 : CollatzResearch.WordTrace tailWord_516632 prefixEnd_516632 265280537493727908624059 := by
  unfold tailWord_516632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421558532168986283032075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12562078042891981710709433 9421558532168986283032075)
  ·
    refine ⟨14132337798253479424548113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9421558532168986283032075 14132337798253479424548113)
    ·
      refine ⟨10599253348690109568411085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14132337798253479424548113 10599253348690109568411085)
      ·
        refine ⟨3974720005758791088154157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10599253348690109568411085 3974720005758791088154157)
        ·
          refine ⟨1490520002159546658057809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3974720005758791088154157 1490520002159546658057809)
          ·
            refine ⟨1117890001619659993543357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1490520002159546658057809 1117890001619659993543357)
            ·
              refine ⟨419208750607372497578759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1117890001619659993543357 419208750607372497578759)
              ·
                refine ⟨628813125911058746368139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419208750607372497578759 628813125911058746368139)
                ·
                  refine ⟨943219688866588119552209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628813125911058746368139 943219688866588119552209)
                  ·
                    refine ⟨707414766649941089664157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943219688866588119552209 707414766649941089664157)
                    ·
                      refine ⟨265280537493727908624059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 707414766649941089664157 265280537493727908624059)
                      ·
                        rfl

theorem cell23_516632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_516632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516632 prefixEnd_516632 := by exact prefixLift 516632
  have htrace : WordTrace (prefixWord ++ tailWord_516632) baseStart_516632 baseEnd_516632 := by
    simpa [prefixWord, tailWord_516632, baseEnd_516632] using wordTrace_append hprefix tailTrace_516632
  have hstable : (prefixWord ++ tailWord_516632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516632).length < 2 ^ (prefixWord ++ tailWord_516632).sum := by decide
  have hdescent : baseEnd_516632 < baseStart_516632 := by decide
  rcases family_descends (prefixWord ++ tailWord_516632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516645 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_516645 : Nat := 118140960795 + 516645 * 2 ^ 59
def prefixEnd_516645 : Nat := 4983230072969 + 3 ^ 40 * 516645 * 2
def baseEnd_516645 : Nat := 265287212742236357761499

theorem tailTrace_516645 : CollatzResearch.WordTrace tailWord_516645 prefixEnd_516645 265287212742236357761499 := by
  unfold tailWord_516645
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843591213290875786287389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12562394142193917190858259 18843591213290875786287389)
  ·
    refine ⟨7066346704984078419857771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18843591213290875786287389 7066346704984078419857771)
    ·
      refine ⟨10599520057476117629786657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066346704984078419857771 10599520057476117629786657)
      ·
        refine ⟨7949640043107088222339993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10599520057476117629786657 7949640043107088222339993)
        ·
          refine ⟨5962230032330316166754995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949640043107088222339993 5962230032330316166754995)
          ·
            refine ⟨8943345048495474250132493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962230032330316166754995 8943345048495474250132493)
            ·
              refine ⟨3353754393185802843799685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8943345048495474250132493 3353754393185802843799685)
              ·
                refine ⟨628828948722338033212441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3353754393185802843799685 628828948722338033212441)
                ·
                  refine ⟨471621711541753524909331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628828948722338033212441 471621711541753524909331)
                  ·
                    refine ⟨707432567312630287363997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 471621711541753524909331 707432567312630287363997)
                    ·
                      refine ⟨265287212742236357761499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 707432567312630287363997 265287212742236357761499)
                      ·
                        rfl

theorem cell23_516645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_516645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516645 prefixEnd_516645 := by exact prefixLift 516645
  have htrace : WordTrace (prefixWord ++ tailWord_516645) baseStart_516645 baseEnd_516645 := by
    simpa [prefixWord, tailWord_516645, baseEnd_516645] using wordTrace_append hprefix tailTrace_516645
  have hstable : (prefixWord ++ tailWord_516645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516645).length < 2 ^ (prefixWord ++ tailWord_516645).sum := by decide
  have hdescent : baseEnd_516645 < baseStart_516645 := by decide
  rcases family_descends (prefixWord ++ tailWord_516645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516648 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 2, 7]
def baseStart_516648 : Nat := 118140960795 + 516648 * 2 ^ 59
def prefixEnd_516648 : Nat := 4983230072969 + 3 ^ 40 * 516648 * 2
def baseEnd_516648 : Nat := 88429584394733282007995

theorem tailTrace_516648 : CollatzResearch.WordTrace tailWord_516648 prefixEnd_516648 88429584394733282007995 := by
  unfold tailWord_516648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421850316140003649323299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12562467088186671532431065 9421850316140003649323299)
  ·
    refine ⟨14132775474210005473984949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9421850316140003649323299 14132775474210005473984949)
    ·
      refine ⟨1324947700707188013186089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14132775474210005473984949 1324947700707188013186089)
      ·
        refine ⟨993710775530391009889567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324947700707188013186089 993710775530391009889567)
        ·
          refine ⟨1490566163295586514834351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993710775530391009889567 1490566163295586514834351)
          ·
            refine ⟨2235849244943379772251527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490566163295586514834351 2235849244943379772251527)
            ·
              refine ⟨3353773867415069658377291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235849244943379772251527 3353773867415069658377291)
              ·
                refine ⟨5030660801122604487565937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353773867415069658377291 5030660801122604487565937)
                ·
                  refine ⟨3772995600841953365674453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030660801122604487565937 3772995600841953365674453)
                  ·
                    refine ⟨88429584394733282007995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3772995600841953365674453 88429584394733282007995)
                    ·
                      rfl

theorem cell23_516648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_516648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516648 prefixEnd_516648 := by exact prefixLift 516648
  have htrace : WordTrace (prefixWord ++ tailWord_516648) baseStart_516648 baseEnd_516648 := by
    simpa [prefixWord, tailWord_516648, baseEnd_516648] using wordTrace_append hprefix tailTrace_516648
  have hstable : (prefixWord ++ tailWord_516648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516648).length < 2 ^ (prefixWord ++ tailWord_516648).sum := by decide
  have hdescent : baseEnd_516648 < baseStart_516648 := by decide
  rcases family_descends (prefixWord ++ tailWord_516648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516662 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_516662 : Nat := 118140960795 + 516662 * 2 ^ 59
def prefixEnd_516662 : Nat := 4983230072969 + 3 ^ 40 * 516662 * 2
def baseEnd_516662 : Nat := 265295941913362791248921

theorem tailTrace_516662 : CollatzResearch.WordTrace tailWord_516662 prefixEnd_516662 265295941913362791248921 := by
  unfold tailWord_516662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177763203389330480603515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12562807502819525126437493 1177763203389330480603515)
  ·
    refine ⟨1766644805083995720905273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1177763203389330480603515 1766644805083995720905273)
    ·
      refine ⟨1324983603812996790678955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1766644805083995720905273 1324983603812996790678955)
      ·
        refine ⟨1987475405719495186018433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324983603812996790678955 1987475405719495186018433)
        ·
          refine ⟨1490606554289621389513825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1987475405719495186018433 1490606554289621389513825)
          ·
            refine ⟨1117954915717216042135369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1490606554289621389513825 1117954915717216042135369)
            ·
              refine ⟨838466186787912031601527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117954915717216042135369 838466186787912031601527)
              ·
                refine ⟨1257699280181868047402291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838466186787912031601527 1257699280181868047402291)
                ·
                  refine ⟨1886548920272802071103437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257699280181868047402291 1886548920272802071103437)
                  ·
                    refine ⟨707455845102300776663789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886548920272802071103437 707455845102300776663789)
                    ·
                      refine ⟨265295941913362791248921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 707455845102300776663789 265295941913362791248921)
                      ·
                        rfl

theorem cell23_516662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_516662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516662 prefixEnd_516662 := by exact prefixLift 516662
  have htrace : WordTrace (prefixWord ++ tailWord_516662) baseStart_516662 baseEnd_516662 := by
    simpa [prefixWord, tailWord_516662, baseEnd_516662] using wordTrace_append hprefix tailTrace_516662
  have hstable : (prefixWord ++ tailWord_516662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516662).length < 2 ^ (prefixWord ++ tailWord_516662).sum := by decide
  have hdescent : baseEnd_516662 < baseStart_516662 := by decide
  rcases family_descends (prefixWord ++ tailWord_516662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516689 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 1, 3, 2]
def baseStart_516689 : Nat := 118140960795 + 516689 * 2 ^ 59
def prefixEnd_516689 : Nat := 4983230072969 + 3 ^ 40 * 516689 * 2
def baseEnd_516689 : Nat := 265309805891034185611297

theorem tailTrace_516689 : CollatzResearch.WordTrace tailWord_516689 prefixEnd_516689 265309805891034185611297 := by
  unfold tailWord_516689
  simp only [CollatzResearch.WordTrace]
  refine ⟨18845196025131471300889121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12563464016754314200592747 18845196025131471300889121)
  ·
    refine ⟨14133897018848603475666841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18845196025131471300889121 14133897018848603475666841)
    ·
      refine ⟨10600422764136452606750131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14133897018848603475666841 10600422764136452606750131)
      ·
        refine ⟨15900634146204678910125197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600422764136452606750131 15900634146204678910125197)
        ·
          refine ⟨5962737804826754591296949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15900634146204678910125197 5962737804826754591296949)
          ·
            refine ⟨559006669202508242934089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5962737804826754591296949 559006669202508242934089)
            ·
              refine ⟨419255001901881182200567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559006669202508242934089 419255001901881182200567)
              ·
                refine ⟨628882502852821773300851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419255001901881182200567 628882502852821773300851)
                ·
                  refine ⟨943323754279232659951277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628882502852821773300851 943323754279232659951277)
                  ·
                    refine ⟨353746407854712247481729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943323754279232659951277 353746407854712247481729)
                    ·
                      refine ⟨265309805891034185611297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 353746407854712247481729 265309805891034185611297)
                      ·
                        rfl

theorem cell23_516689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_516689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516689 prefixEnd_516689 := by exact prefixLift 516689
  have htrace : WordTrace (prefixWord ++ tailWord_516689) baseStart_516689 baseEnd_516689 := by
    simpa [prefixWord, tailWord_516689, baseEnd_516689] using wordTrace_append hprefix tailTrace_516689
  have hstable : (prefixWord ++ tailWord_516689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516689).length < 2 ^ (prefixWord ++ tailWord_516689).sum := by decide
  have hdescent : baseEnd_516689 < baseStart_516689 := by decide
  rcases family_descends (prefixWord ++ tailWord_516689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516708 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 7]
def baseStart_516708 : Nat := 118140960795 + 516708 * 2 ^ 59
def prefixEnd_516708 : Nat := 4983230072969 + 3 ^ 40 * 516708 * 2
def baseEnd_516708 : Nat := 29479951335941067919301

theorem tailTrace_516708 : CollatzResearch.WordTrace tailWord_516708 prefixEnd_516708 29479951335941067919301 := by
  unfold tailWord_516708
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422944506031318772915389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12563926008041758363887185 9422944506031318772915389)
  ·
    refine ⟨3533604189761744539843271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9422944506031318772915389 3533604189761744539843271)
    ·
      refine ⟨5300406284642616809764907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533604189761744539843271 5300406284642616809764907)
      ·
        refine ⟨7950609426963925214647361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300406284642616809764907 7950609426963925214647361)
        ·
          refine ⟨5962957070222943910985521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7950609426963925214647361 5962957070222943910985521)
          ·
            refine ⟨4472217802667207933239141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962957070222943910985521 4472217802667207933239141)
            ·
              refine ⟨838540838000101487482339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4472217802667207933239141 838540838000101487482339)
              ·
                refine ⟨1257811257000152231223509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838540838000101487482339 1257811257000152231223509)
                ·
                  refine ⟨29479951335941067919301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1257811257000152231223509 29479951335941067919301)
                  ·
                    rfl

theorem cell23_516708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_516708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516708 prefixEnd_516708 := by exact prefixLift 516708
  have htrace : WordTrace (prefixWord ++ tailWord_516708) baseStart_516708 baseEnd_516708 := by
    simpa [prefixWord, tailWord_516708, baseEnd_516708] using wordTrace_append hprefix tailTrace_516708
  have hstable : (prefixWord ++ tailWord_516708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516708).length < 2 ^ (prefixWord ++ tailWord_516708).sum := by decide
  have hdescent : baseEnd_516708 < baseStart_516708 := by decide
  rcases family_descends (prefixWord ++ tailWord_516708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516731 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7]
def baseStart_516731 : Nat := 118140960795 + 516731 * 2 ^ 59
def prefixEnd_516731 : Nat := 4983230072969 + 3 ^ 40 * 516731 * 2
def baseEnd_516731 : Nat := 265331372078523021286103

theorem tailTrace_516731 : CollatzResearch.WordTrace tailWord_516731 prefixEnd_516731 265331372078523021286103 := by
  unfold tailWord_516731
  simp only [CollatzResearch.WordTrace]
  refine ⟨18846727890979312473918047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12564485260652874982612031 18846727890979312473918047)
  ·
    refine ⟨28270091836468968710877071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18846727890979312473918047 28270091836468968710877071)
    ·
      refine ⟨42405137754703453066315607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28270091836468968710877071 42405137754703453066315607)
      ·
        refine ⟨63607706632055179599473411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42405137754703453066315607 63607706632055179599473411)
        ·
          refine ⟨95411559948082769399210117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63607706632055179599473411 95411559948082769399210117)
          ·
            refine ⟨17889667490265519262351897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95411559948082769399210117 17889667490265519262351897)
            ·
              refine ⟨13417250617699139446763923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17889667490265519262351897 13417250617699139446763923)
              ·
                refine ⟨20125875926548709170145885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13417250617699139446763923 20125875926548709170145885)
                ·
                  refine ⟨7547203472455765938804707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20125875926548709170145885 7547203472455765938804707)
                  ·
                    refine ⟨11320805208683648908207061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547203472455765938804707 11320805208683648908207061)
                    ·
                      refine ⟨265331372078523021286103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11320805208683648908207061 265331372078523021286103)
                      ·
                        rfl

theorem cell23_516731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_516731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516731 prefixEnd_516731 := by exact prefixLift 516731
  have htrace : WordTrace (prefixWord ++ tailWord_516731) baseStart_516731 baseEnd_516731 := by
    simpa [prefixWord, tailWord_516731, baseEnd_516731] using wordTrace_append hprefix tailTrace_516731
  have hstable : (prefixWord ++ tailWord_516731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516731).length < 2 ^ (prefixWord ++ tailWord_516731).sum := by decide
  have hdescent : baseEnd_516731 < baseStart_516731 := by decide
  rcases family_descends (prefixWord ++ tailWord_516731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516751 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 10]
def baseStart_516751 : Nat := 118140960795 + 516751 * 2 ^ 59
def prefixEnd_516751 : Nat := 4983230072969 + 3 ^ 40 * 516751 * 2
def baseEnd_516751 : Nat := 88447213897204314345337

theorem tailTrace_516751 : CollatzResearch.WordTrace tailWord_516751 prefixEnd_516751 88447213897204314345337 := by
  unfold tailWord_516751
  simp only [CollatzResearch.WordTrace]
  refine ⟨18847457350906855889646107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12564971567271237259764071 18847457350906855889646107)
  ·
    refine ⟨28271186026360283834469161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18847457350906855889646107 28271186026360283834469161)
    ·
      refine ⟨21203389519770212875851871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28271186026360283834469161 21203389519770212875851871)
      ·
        refine ⟨31805084279655319313777807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21203389519770212875851871 31805084279655319313777807)
        ·
          refine ⟨47707626419482978970666711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31805084279655319313777807 47707626419482978970666711)
          ·
            refine ⟨71561439629224468456000067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47707626419482978970666711 71561439629224468456000067)
            ·
              refine ⟨107342159443836702684000101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71561439629224468456000067 107342159443836702684000101)
              ·
                refine ⟨20126654895719381753250019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107342159443836702684000101 20126654895719381753250019)
                ·
                  refine ⟨30189982343579072629875029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20126654895719381753250019 30189982343579072629875029)
                  ·
                    refine ⟨88447213897204314345337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 30189982343579072629875029 88447213897204314345337)
                    ·
                      rfl

theorem cell23_516751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_516751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516751 prefixEnd_516751 := by exact prefixLift 516751
  have htrace : WordTrace (prefixWord ++ tailWord_516751) baseStart_516751 baseEnd_516751 := by
    simpa [prefixWord, tailWord_516751, baseEnd_516751] using wordTrace_append hprefix tailTrace_516751
  have hstable : (prefixWord ++ tailWord_516751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516751).length < 2 ^ (prefixWord ++ tailWord_516751).sum := by decide
  have hdescent : baseEnd_516751 < baseStart_516751 := by decide
  rcases family_descends (prefixWord ++ tailWord_516751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516812 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_516812 : Nat := 118140960795 + 516812 * 2 ^ 59
def prefixEnd_516812 : Nat := 4983230072969 + 3 ^ 40 * 516812 * 2
def baseEnd_516812 : Nat := 265372964011537204373231

theorem tailTrace_516812 : CollatzResearch.WordTrace tailWord_516812 prefixEnd_516812 265372964011537204373231 := by
  unfold tailWord_516812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9424841101842931653808345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12566454802457242205077793 9424841101842931653808345)
  ·
    refine ⟨7068630826382198740356259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9424841101842931653808345 7068630826382198740356259)
    ·
      refine ⟨10602946239573298110534389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7068630826382198740356259 10602946239573298110534389)
      ·
        refine ⟨994026209959996697862599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10602946239573298110534389 994026209959996697862599)
        ·
          refine ⟨1491039314939995046793899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994026209959996697862599 1491039314939995046793899)
          ·
            refine ⟨2236558972409992570190849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491039314939995046793899 2236558972409992570190849)
            ·
              refine ⟨1677419229307494427643137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236558972409992570190849 1677419229307494427643137)
              ·
                refine ⟨1258064421980620820732353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677419229307494427643137 1258064421980620820732353)
                ·
                  refine ⟨943548316485465615549265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1258064421980620820732353 943548316485465615549265)
                  ·
                    refine ⟨707661237364099211661949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 943548316485465615549265 707661237364099211661949)
                    ·
                      refine ⟨265372964011537204373231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 707661237364099211661949 265372964011537204373231)
                      ·
                        rfl

theorem cell23_516812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_516812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516812 prefixEnd_516812 := by exact prefixLift 516812
  have htrace : WordTrace (prefixWord ++ tailWord_516812) baseStart_516812 baseEnd_516812 := by
    simpa [prefixWord, tailWord_516812, baseEnd_516812] using wordTrace_append hprefix tailTrace_516812
  have hstable : (prefixWord ++ tailWord_516812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516812).length < 2 ^ (prefixWord ++ tailWord_516812).sum := by decide
  have hdescent : baseEnd_516812 < baseStart_516812 := by decide
  rcases family_descends (prefixWord ++ tailWord_516812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516845 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_516845 : Nat := 118140960795 + 516845 * 2 ^ 59
def prefixEnd_516845 : Nat := 4983230072969 + 3 ^ 40 * 516845 * 2
def baseEnd_516845 : Nat := 88463302957711858420193

theorem tailTrace_516845 : CollatzResearch.WordTrace tailWord_516845 prefixEnd_516845 88463302957711858420193 := by
  unfold tailWord_516845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850885812566309943567989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12567257208377539962378659 18850885812566309943567989)
  ·
    refine ⟨1767270544928091557209499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18850885812566309943567989 1767270544928091557209499)
    ·
      refine ⟨2650905817392137335814249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1767270544928091557209499 2650905817392137335814249)
      ·
        refine ⟨1988179363044103001860687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650905817392137335814249 1988179363044103001860687)
        ·
          refine ⟨2982269044566154502791031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988179363044103001860687 2982269044566154502791031)
          ·
            refine ⟨4473403566849231754186547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982269044566154502791031 4473403566849231754186547)
            ·
              refine ⟨6710105350273847631279821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473403566849231754186547 6710105350273847631279821)
              ·
                refine ⟨2516289506352692861729933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6710105350273847631279821 2516289506352692861729933)
                ·
                  refine ⟨943608564882259823148725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2516289506352692861729933 943608564882259823148725)
                  ·
                    refine ⟨88463302957711858420193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 943608564882259823148725 88463302957711858420193)
                    ·
                      rfl

theorem cell23_516845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_516845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516845 prefixEnd_516845 := by exact prefixLift 516845
  have htrace : WordTrace (prefixWord ++ tailWord_516845) baseStart_516845 baseEnd_516845 := by
    simpa [prefixWord, tailWord_516845, baseEnd_516845] using wordTrace_append hprefix tailTrace_516845
  have hstable : (prefixWord ++ tailWord_516845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516845).length < 2 ^ (prefixWord ++ tailWord_516845).sum := by decide
  have hdescent : baseEnd_516845 < baseStart_516845 := by decide
  rcases family_descends (prefixWord ++ tailWord_516845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516885 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_516885 : Nat := 118140960795 + 516885 * 2 ^ 59
def prefixEnd_516885 : Nat := 4983230072969 + 3 ^ 40 * 516885 * 2
def baseEnd_516885 : Nat := 265410448099315418760395

theorem tailTrace_516885 : CollatzResearch.WordTrace tailWord_516885 prefixEnd_516885 265410448099315418760395 := by
  unfold tailWord_516885
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852344732421396775024109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12568229821614264516682739 18852344732421396775024109)
  ·
    refine ⟨7069629274658023790634041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18852344732421396775024109 7069629274658023790634041)
    ·
      refine ⟨5302221955993517842975531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7069629274658023790634041 5302221955993517842975531)
      ·
        refine ⟨7953332933990276764463297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302221955993517842975531 7953332933990276764463297)
        ·
          refine ⟨5964999700492707573347473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7953332933990276764463297 5964999700492707573347473)
          ·
            refine ⟨4473749775369530680010605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5964999700492707573347473 4473749775369530680010605)
            ·
              refine ⟨1677656165763574005003977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4473749775369530680010605 1677656165763574005003977)
              ·
                refine ⟨1258242124322680503752983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677656165763574005003977 1258242124322680503752983)
                ·
                  refine ⟨1887363186484020755629475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258242124322680503752983 1887363186484020755629475)
                  ·
                    refine ⟨2831044779726031133444213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1887363186484020755629475 2831044779726031133444213)
                    ·
                      refine ⟨265410448099315418760395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2831044779726031133444213 265410448099315418760395)
                      ·
                        rfl

theorem cell23_516885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_516885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516885 prefixEnd_516885 := by exact prefixLift 516885
  have htrace : WordTrace (prefixWord ++ tailWord_516885) baseStart_516885 baseEnd_516885 := by
    simpa [prefixWord, tailWord_516885, baseEnd_516885] using wordTrace_append hprefix tailTrace_516885
  have hstable : (prefixWord ++ tailWord_516885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516885).length < 2 ^ (prefixWord ++ tailWord_516885).sum := by decide
  have hdescent : baseEnd_516885 < baseStart_516885 := by decide
  rcases family_descends (prefixWord ++ tailWord_516885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516888 : List Nat := [2, 1, 2, 3, 1, 1, 1, 12]
def baseStart_516888 : Nat := 118140960795 + 516888 * 2 ^ 59
def prefixEnd_516888 : Nat := 4983230072969 + 3 ^ 40 * 516888 * 2
def baseEnd_516888 : Nat := 9830073649676996556403

theorem tailTrace_516888 : CollatzResearch.WordTrace tailWord_516888 prefixEnd_516888 9830073649676996556403 := by
  unfold tailWord_516888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9426227075705264143691659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12568302767607018858255545 9426227075705264143691659)
  ·
    refine ⟨14139340613557896215537489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9426227075705264143691659 14139340613557896215537489)
    ·
      refine ⟨10604505460168422161653117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14139340613557896215537489 10604505460168422161653117)
      ·
        refine ⟨3976689547563158310619919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10604505460168422161653117 3976689547563158310619919)
        ·
          refine ⟨5965034321344737465929879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976689547563158310619919 5965034321344737465929879)
          ·
            refine ⟨8947551482017106198894819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965034321344737465929879 8947551482017106198894819)
            ·
              refine ⟨13421327223025659298342229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947551482017106198894819 13421327223025659298342229)
              ·
                refine ⟨9830073649676996556403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 13421327223025659298342229 9830073649676996556403)
                ·
                  rfl

theorem cell23_516888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 12].length) (baseStart_516888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516888 prefixEnd_516888 := by exact prefixLift 516888
  have htrace : WordTrace (prefixWord ++ tailWord_516888) baseStart_516888 baseEnd_516888 := by
    simpa [prefixWord, tailWord_516888, baseEnd_516888] using wordTrace_append hprefix tailTrace_516888
  have hstable : (prefixWord ++ tailWord_516888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516888).length < 2 ^ (prefixWord ++ tailWord_516888).sum := by decide
  have hdescent : baseEnd_516888 < baseStart_516888 := by decide
  rcases family_descends (prefixWord ++ tailWord_516888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516892 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_516892 : Nat := 118140960795 + 516892 * 2 ^ 59
def prefixEnd_516892 : Nat := 4983230072969 + 3 ^ 40 * 516892 * 2
def baseEnd_516892 : Nat := 88471347487965630457621

theorem tailTrace_516892 : CollatzResearch.WordTrace tailWord_516892 prefixEnd_516892 88471347487965630457621 := by
  unfold tailWord_516892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9426300021698018485264465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12568400028930691313685953 9426300021698018485264465)
  ·
    refine ⟨7069725016273513863948349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9426300021698018485264465 7069725016273513863948349)
    ·
      refine ⟨2651146881102567698980631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7069725016273513863948349 2651146881102567698980631)
      ·
        refine ⟨3976720321653851548470947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651146881102567698980631 3976720321653851548470947)
        ·
          refine ⟨5965080482480777322706421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976720321653851548470947 5965080482480777322706421)
          ·
            refine ⟨559226295232572874003727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5965080482480777322706421 559226295232572874003727)
            ·
              refine ⟨838839442848859311005591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559226295232572874003727 838839442848859311005591)
              ·
                refine ⟨1258259164273288966508387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838839442848859311005591 1258259164273288966508387)
                ·
                  refine ⟨1887388746409933449762581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258259164273288966508387 1887388746409933449762581)
                  ·
                    refine ⟨88471347487965630457621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1887388746409933449762581 88471347487965630457621)
                    ·
                      rfl

theorem cell23_516892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_516892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_516892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_516892 prefixEnd_516892 := by exact prefixLift 516892
  have htrace : WordTrace (prefixWord ++ tailWord_516892) baseStart_516892 baseEnd_516892 := by
    simpa [prefixWord, tailWord_516892, baseEnd_516892] using wordTrace_append hprefix tailTrace_516892
  have hstable : (prefixWord ++ tailWord_516892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516892).length < 2 ^ (prefixWord ++ tailWord_516892).sum := by decide
  have hdescent : baseEnd_516892 < baseStart_516892 := by decide
  rcases family_descends (prefixWord ++ tailWord_516892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
