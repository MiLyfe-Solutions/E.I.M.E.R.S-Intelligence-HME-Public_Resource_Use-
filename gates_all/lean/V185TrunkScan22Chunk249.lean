import V185TrunkScan22Chunk248

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2222168 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 5]
def baseStart_2222168 : Nat := 118140960795 + 2222168 * 2 ^ 59
def prefixEnd_2222168 : Nat := 4983230072969 + 3 ^ 40 * 2222168 * 2
def baseEnd_2222168 : Nat := 253564506453414886928987

theorem tailTrace_2222168 : CollatzResearch.WordTrace tailWord_2222168 prefixEnd_2222168 253564506453414886928987 := by
  unfold tailWord_2222168
  simp only [CollatzResearch.WordTrace]
  refine ⟨40524562706736163462345579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54032750275648217949794105 40524562706736163462345579)
  ·
    refine ⟨60786844060104245193518369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40524562706736163462345579 60786844060104245193518369)
    ·
      refine ⟨45590133045078183895138777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60786844060104245193518369 45590133045078183895138777)
      ·
        refine ⟨34192599783808637921354083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45590133045078183895138777 34192599783808637921354083)
        ·
          refine ⟨51288899675712956882031125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34192599783808637921354083 51288899675712956882031125)
          ·
            refine ⟨2404167172299044853845209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51288899675712956882031125 2404167172299044853845209)
            ·
              refine ⟨1803125379224283640383907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2404167172299044853845209 1803125379224283640383907)
              ·
                refine ⟨2704688068836425460575861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803125379224283640383907 2704688068836425460575861)
                ·
                  refine ⟨253564506453414886928987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2704688068836425460575861 253564506453414886928987)
                  ·
                    rfl

theorem cell22_2222168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_2222168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222168 prefixEnd_2222168 := by exact prefixLift 2222168
  have htrace : WordTrace (prefixWord ++ tailWord_2222168) baseStart_2222168 baseEnd_2222168 := by
    simpa [prefixWord, tailWord_2222168, baseEnd_2222168] using wordTrace_append hprefix tailTrace_2222168
  have hstable : (prefixWord ++ tailWord_2222168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222168).length < 2 ^ (prefixWord ++ tailWord_2222168).sum := by decide
  have hdescent : baseEnd_2222168 < baseStart_2222168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222179 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 6]
def baseStart_2222179 : Nat := 118140960795 + 2222179 * 2 ^ 59
def prefixEnd_2222179 : Nat := 4983230072969 + 3 ^ 40 * 2222179 * 2
def baseEnd_2222179 : Nat := 253565761628348099587309

theorem tailTrace_2222179 : CollatzResearch.WordTrace tailWord_2222179 prefixEnd_2222179 253565761628348099587309 := by
  unfold tailWord_2222179
  simp only [CollatzResearch.WordTrace]
  refine ⟨81049526616432475803341591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54033017744288317202227727 81049526616432475803341591)
  ·
    refine ⟨121574289924648713705012387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81049526616432475803341591 121574289924648713705012387)
    ·
      refine ⟨182361434886973070557518581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121574289924648713705012387 182361434886973070557518581)
      ·
        refine ⟨17096384520653725364767367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182361434886973070557518581 17096384520653725364767367)
        ·
          refine ⟨25644576780980588047151051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17096384520653725364767367 25644576780980588047151051)
          ·
            refine ⟨38466865171470882070726577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25644576780980588047151051 38466865171470882070726577)
            ·
              refine ⟨28850148878603161553044933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38466865171470882070726577 28850148878603161553044933)
              ·
                refine ⟨5409402914738092791195925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28850148878603161553044933 5409402914738092791195925)
                ·
                  refine ⟨253565761628348099587309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5409402914738092791195925 253565761628348099587309)
                  ·
                    rfl

theorem cell22_2222179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 6].length) (baseStart_2222179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222179 prefixEnd_2222179 := by exact prefixLift 2222179
  have htrace : WordTrace (prefixWord ++ tailWord_2222179) baseStart_2222179 baseEnd_2222179 := by
    simpa [prefixWord, tailWord_2222179, baseEnd_2222179] using wordTrace_append hprefix tailTrace_2222179
  have hstable : (prefixWord ++ tailWord_2222179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222179).length < 2 ^ (prefixWord ++ tailWord_2222179).sum := by decide
  have hdescent : baseEnd_2222179 < baseStart_2222179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222181 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_2222181 : Nat := 118140960795 + 2222181 * 2 ^ 59
def prefixEnd_2222181 : Nat := 4983230072969 + 3 ^ 40 * 2222181 * 2
def baseEnd_2222181 : Nat := 760697969525916960211921

theorem tailTrace_2222181 : CollatzResearch.WordTrace tailWord_2222181 prefixEnd_2222181 760697969525916960211921 := by
  unfold tailWord_2222181
  simp only [CollatzResearch.WordTrace]
  refine ⟨81049599562425230144914397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54033066374950153429942931 81049599562425230144914397)
  ·
    refine ⟨30393599835909461304342899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81049599562425230144914397 30393599835909461304342899)
    ·
      refine ⟨45590399753864191956514349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30393599835909461304342899 45590399753864191956514349)
      ·
        refine ⟨17096399907699071983692881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45590399753864191956514349 17096399907699071983692881)
        ·
          refine ⟨12822299930774303987769661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17096399907699071983692881 12822299930774303987769661)
          ·
            refine ⟨4808362474040363995413623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12822299930774303987769661 4808362474040363995413623)
            ·
              refine ⟨7212543711060545993120435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808362474040363995413623 7212543711060545993120435)
              ·
                refine ⟨10818815566590818989680653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7212543711060545993120435 10818815566590818989680653)
                ·
                  refine ⟨4057055837471557121130245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10818815566590818989680653 4057055837471557121130245)
                  ·
                    refine ⟨760697969525916960211921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4057055837471557121130245 760697969525916960211921)
                    ·
                      rfl

theorem cell22_2222181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_2222181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222181 prefixEnd_2222181 := by exact prefixLift 2222181
  have htrace : WordTrace (prefixWord ++ tailWord_2222181) baseStart_2222181 baseEnd_2222181 := by
    simpa [prefixWord, tailWord_2222181, baseEnd_2222181] using wordTrace_append hprefix tailTrace_2222181
  have hstable : (prefixWord ++ tailWord_2222181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222181).length < 2 ^ (prefixWord ++ tailWord_2222181).sum := by decide
  have hdescent : baseEnd_2222181 < baseStart_2222181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222213 : List Nat := [1, 3, 1, 1, 5, 2, 1, 4, 4]
def baseStart_2222213 : Nat := 118140960795 + 2222213 * 2 ^ 59
def prefixEnd_2222213 : Nat := 4983230072969 + 3 ^ 40 * 2222213 * 2
def baseEnd_2222213 : Nat := 253569641259959847803941

theorem tailTrace_2222213 : CollatzResearch.WordTrace tailWord_2222213 prefixEnd_2222213 253569641259959847803941 := by
  unfold tailWord_2222213
  simp only [CollatzResearch.WordTrace]
  refine ⟨81050766698309299610079293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54033844465539533073386195 81050766698309299610079293)
  ·
    refine ⟨30394037511865987353779735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81050766698309299610079293 30394037511865987353779735)
    ·
      refine ⟨45591056267798981030669603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30394037511865987353779735 45591056267798981030669603)
      ·
        refine ⟨68386584401698471546004405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45591056267798981030669603 68386584401698471546004405)
        ·
          refine ⟨6411242287659231707437913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68386584401698471546004405 6411242287659231707437913)
          ·
            refine ⟨4808431715744423780578435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6411242287659231707437913 4808431715744423780578435)
            ·
              refine ⟨7212647573616635670867653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808431715744423780578435 7212647573616635670867653)
              ·
                refine ⟨1352371420053119188287685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7212647573616635670867653 1352371420053119188287685)
                ·
                  refine ⟨253569641259959847803941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352371420053119188287685 253569641259959847803941)
                  ·
                    rfl

theorem cell22_2222213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_2222213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222213 prefixEnd_2222213 := by exact prefixLift 2222213
  have htrace : WordTrace (prefixWord ++ tailWord_2222213) baseStart_2222213 baseEnd_2222213 := by
    simpa [prefixWord, tailWord_2222213, baseEnd_2222213] using wordTrace_append hprefix tailTrace_2222213
  have hstable : (prefixWord ++ tailWord_2222213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222213).length < 2 ^ (prefixWord ++ tailWord_2222213).sum := by decide
  have hdescent : baseEnd_2222213 < baseStart_2222213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222226 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2222226 : Nat := 118140960795 + 2222226 * 2 ^ 59
def prefixEnd_2222226 : Nat := 4983230072969 + 3 ^ 40 * 2222226 * 2
def baseEnd_2222226 : Nat := 760713373945551842836783

theorem tailTrace_2222226 : CollatzResearch.WordTrace tailWord_2222226 prefixEnd_2222226 760713373945551842836783 := by
  unfold tailWord_2222226
  simp only [CollatzResearch.WordTrace]
  refine ⟨20262810211815550707575633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54034160564841468553535021 20262810211815550707575633)
  ·
    refine ⟨15197107658861663030681725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20262810211815550707575633 15197107658861663030681725)
    ·
      refine ⟨5698915372073123636505647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15197107658861663030681725 5698915372073123636505647)
      ·
        refine ⟨8548373058109685454758471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698915372073123636505647 8548373058109685454758471)
        ·
          refine ⟨12822559587164528182137707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8548373058109685454758471 12822559587164528182137707)
          ·
            refine ⟨19233839380746792273206561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12822559587164528182137707 19233839380746792273206561)
            ·
              refine ⟨14425379535560094204904921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19233839380746792273206561 14425379535560094204904921)
              ·
                refine ⟨10819034651670070653678691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14425379535560094204904921 10819034651670070653678691)
                ·
                  refine ⟨16228551977505105980518037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10819034651670070653678691 16228551977505105980518037)
                  ·
                    refine ⟨760713373945551842836783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16228551977505105980518037 760713373945551842836783)
                    ·
                      rfl

theorem cell22_2222226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2222226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222226 prefixEnd_2222226 := by exact prefixLift 2222226
  have htrace : WordTrace (prefixWord ++ tailWord_2222226) baseStart_2222226 baseEnd_2222226 := by
    simpa [prefixWord, tailWord_2222226, baseEnd_2222226] using wordTrace_append hprefix tailTrace_2222226
  have hstable : (prefixWord ++ tailWord_2222226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222226).length < 2 ^ (prefixWord ++ tailWord_2222226).sum := by decide
  have hdescent : baseEnd_2222226 < baseStart_2222226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222375 : List Nat := [1, 1, 8, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2222375 : Nat := 118140960795 + 2222375 * 2 ^ 59
def prefixEnd_2222375 : Nat := 4983230072969 + 3 ^ 40 * 2222375 * 2
def baseEnd_2222375 : Nat := 760764379690565120861327

theorem tailTrace_2222375 : CollatzResearch.WordTrace tailWord_2222375 prefixEnd_2222375 760764379690565120861327 := by
  unfold tailWord_2222375
  simp only [CollatzResearch.WordTrace]
  refine ⟨81056675323722401277476579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54037783549148267518317719 81056675323722401277476579)
  ·
    refine ⟨121585012985583601916214869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81056675323722401277476579 121585012985583601916214869)
    ·
      refine ⟨1424824370924807834955643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 121585012985583601916214869 1424824370924807834955643)
      ·
        refine ⟨2137236556387211752433465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424824370924807834955643 2137236556387211752433465)
        ·
          refine ⟨1602927417290408814325099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2137236556387211752433465 1602927417290408814325099)
          ·
            refine ⟨2404391125935613221487649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602927417290408814325099 2404391125935613221487649)
            ·
              refine ⟨1803293344451709916115737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2404391125935613221487649 1803293344451709916115737)
              ·
                refine ⟨1352470008338782437086803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1803293344451709916115737 1352470008338782437086803)
                ·
                  refine ⟨2028705012508173655630205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352470008338782437086803 2028705012508173655630205)
                  ·
                    refine ⟨760764379690565120861327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2028705012508173655630205 760764379690565120861327)
                    ·
                      rfl

theorem cell22_2222375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2222375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222375 prefixEnd_2222375 := by exact prefixLift 2222375
  have htrace : WordTrace (prefixWord ++ tailWord_2222375) baseStart_2222375 baseEnd_2222375 := by
    simpa [prefixWord, tailWord_2222375, baseEnd_2222375] using wordTrace_append hprefix tailTrace_2222375
  have hstable : (prefixWord ++ tailWord_2222375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222375).length < 2 ^ (prefixWord ++ tailWord_2222375).sum := by decide
  have hdescent : baseEnd_2222375 < baseStart_2222375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222376 : List Nat := [2, 1, 5, 1, 13]
def baseStart_2222376 : Nat := 118140960795 + 2222376 * 2 ^ 59
def prefixEnd_2222376 : Nat := 4983230072969 + 3 ^ 40 * 2222376 * 2
def baseEnd_2222376 : Nat := 3130719020621405150561

theorem tailTrace_2222376 : CollatzResearch.WordTrace tailWord_2222376 prefixEnd_2222376 3130719020621405150561 := by
  unfold tailWord_2222376
  simp only [CollatzResearch.WordTrace]
  refine ⟨40528355898359389224131491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54037807864479185632175321 40528355898359389224131491)
  ·
    refine ⟨60792533847539083836197237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40528355898359389224131491 60792533847539083836197237)
    ·
      refine ⟨5699300048206789109643491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60792533847539083836197237 5699300048206789109643491)
      ·
        refine ⟨8548950072310183664465237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5699300048206789109643491 8548950072310183664465237)
        ·
          refine ⟨3130719020621405150561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8548950072310183664465237 3130719020621405150561)
          ·
            rfl

theorem cell22_2222376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 13].length) (baseStart_2222376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222376 prefixEnd_2222376 := by exact prefixLift 2222376
  have htrace : WordTrace (prefixWord ++ tailWord_2222376) baseStart_2222376 baseEnd_2222376 := by
    simpa [prefixWord, tailWord_2222376, baseEnd_2222376] using wordTrace_append hprefix tailTrace_2222376
  have hstable : (prefixWord ++ tailWord_2222376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222376).length < 2 ^ (prefixWord ++ tailWord_2222376).sum := by decide
  have hdescent : baseEnd_2222376 < baseStart_2222376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222393 : List Nat := [1, 2, 1, 6, 1, 1, 3, 7]
def baseStart_2222393 : Nat := 118140960795 + 2222393 * 2 ^ 59
def prefixEnd_2222393 : Nat := 4983230072969 + 3 ^ 40 * 2222393 * 2
def baseEnd_2222393 : Nat := 84530060162046563767919

theorem tailTrace_2222393 : CollatzResearch.WordTrace tailWord_2222393 prefixEnd_2222393 84530060162046563767919 := by
  unfold tailWord_2222393
  simp only [CollatzResearch.WordTrace]
  refine ⟨81057331837657190351631833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54038221225104793567754555 81057331837657190351631833)
  ·
    refine ⟨60792998878242892763723875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81057331837657190351631833 60792998878242892763723875)
    ·
      refine ⟨91189498317364339145585813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60792998878242892763723875 91189498317364339145585813)
      ·
        refine ⟨4274507733626453397449335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91189498317364339145585813 4274507733626453397449335)
        ·
          refine ⟨6411761600439680096174003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4274507733626453397449335 6411761600439680096174003)
          ·
            refine ⟨9617642400659520144261005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6411761600439680096174003 9617642400659520144261005)
            ·
              refine ⟨3606615900247320054097877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9617642400659520144261005 3606615900247320054097877)
              ·
                refine ⟨84530060162046563767919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3606615900247320054097877 84530060162046563767919)
                ·
                  rfl

theorem cell22_2222393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 7].length) (baseStart_2222393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222393 prefixEnd_2222393 := by exact prefixLift 2222393
  have htrace : WordTrace (prefixWord ++ tailWord_2222393) baseStart_2222393 baseEnd_2222393 := by
    simpa [prefixWord, tailWord_2222393, baseEnd_2222393] using wordTrace_append hprefix tailTrace_2222393
  have hstable : (prefixWord ++ tailWord_2222393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222393).length < 2 ^ (prefixWord ++ tailWord_2222393).sum := by decide
  have hdescent : baseEnd_2222393 < baseStart_2222393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222408 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 5, 3]
def baseStart_2222408 : Nat := 118140960795 + 2222408 * 2 ^ 59
def prefixEnd_2222408 : Nat := 4983230072969 + 3 ^ 40 * 2222408 * 2
def baseEnd_2222408 : Nat := 760775676264964034786225

theorem tailTrace_2222408 : CollatzResearch.WordTrace tailWord_2222408 prefixEnd_2222408 760775676264964034786225 := by
  unfold tailWord_2222408
  simp only [CollatzResearch.WordTrace]
  refine ⟨40528939466301423956713939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54038585955068565275618585 40528939466301423956713939)
  ·
    refine ⟨60793409199452135935070909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40528939466301423956713939 60793409199452135935070909)
    ·
      refine ⟨22797528449794550975651591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60793409199452135935070909 22797528449794550975651591)
      ·
        refine ⟨34196292674691826463477387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22797528449794550975651591 34196292674691826463477387)
        ·
          refine ⟨51294439012037739695216081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34196292674691826463477387 51294439012037739695216081)
          ·
            refine ⟨38470829259028304771412061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51294439012037739695216081 38470829259028304771412061)
            ·
              refine ⟨14426560972135614289279523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38470829259028304771412061 14426560972135614289279523)
              ·
                refine ⟨21639841458203421433919285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14426560972135614289279523 21639841458203421433919285)
                ·
                  refine ⟨2028735136706570759429933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21639841458203421433919285 2028735136706570759429933)
                  ·
                    refine ⟨760775676264964034786225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2028735136706570759429933 760775676264964034786225)
                    ·
                      rfl

theorem cell22_2222408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_2222408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222408 prefixEnd_2222408 := by exact prefixLift 2222408
  have htrace : WordTrace (prefixWord ++ tailWord_2222408) baseStart_2222408 baseEnd_2222408 := by
    simpa [prefixWord, tailWord_2222408, baseEnd_2222408] using wordTrace_append hprefix tailTrace_2222408
  have hstable : (prefixWord ++ tailWord_2222408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222408).length < 2 ^ (prefixWord ++ tailWord_2222408).sum := by decide
  have hdescent : baseEnd_2222408 < baseStart_2222408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222442 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_2222442 : Nat := 118140960795 + 2222442 * 2 ^ 59
def prefixEnd_2222442 : Nat := 4983230072969 + 3 ^ 40 * 2222442 * 2
def baseEnd_2222442 : Nat := 760787315159799279436121

theorem tailTrace_2222442 : CollatzResearch.WordTrace tailWord_2222442 prefixEnd_2222442 760787315159799279436121 := by
  unfold tailWord_2222442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20264779753619917930041395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54039412676319781146777053 20264779753619917930041395)
  ·
    refine ⟨30397169630429876895062093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20264779753619917930041395 30397169630429876895062093)
    ·
      refine ⟨11398938611411203835648285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30397169630429876895062093 11398938611411203835648285)
      ·
        refine ⟨4274601979279201438368107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11398938611411203835648285 4274601979279201438368107)
        ·
          refine ⟨6411902968918802157552161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4274601979279201438368107 6411902968918802157552161)
          ·
            refine ⟨4808927226689101618164121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6411902968918802157552161 4808927226689101618164121)
            ·
              refine ⟨3606695420016826213623091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4808927226689101618164121 3606695420016826213623091)
              ·
                refine ⟨5410043130025239320434637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606695420016826213623091 5410043130025239320434637)
                ·
                  refine ⟨2028766173759464745162989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5410043130025239320434637 2028766173759464745162989)
                  ·
                    refine ⟨760787315159799279436121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2028766173759464745162989 760787315159799279436121)
                    ·
                      rfl

theorem cell22_2222442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_2222442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222442 prefixEnd_2222442 := by exact prefixLift 2222442
  have htrace : WordTrace (prefixWord ++ tailWord_2222442) baseStart_2222442 baseEnd_2222442 := by
    simpa [prefixWord, tailWord_2222442, baseEnd_2222442] using wordTrace_append hprefix tailTrace_2222442
  have hstable : (prefixWord ++ tailWord_2222442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222442).length < 2 ^ (prefixWord ++ tailWord_2222442).sum := by decide
  have hdescent : baseEnd_2222442 < baseStart_2222442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222500 : List Nat := [2, 3, 1, 2, 1, 1, 2, 6, 4]
def baseStart_2222500 : Nat := 118140960795 + 2222500 * 2 ^ 59
def prefixEnd_2222500 : Nat := 4983230072969 + 3 ^ 40 * 2222500 * 2
def baseEnd_2222500 : Nat := 253602389915035487161981

theorem tailTrace_2222500 : CollatzResearch.WordTrace tailWord_2222500 prefixEnd_2222500 253602389915035487161981 := by
  unfold tailWord_2222500
  simp only [CollatzResearch.WordTrace]
  refine ⟨40530617224134773812888477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54040822965513031750517969 40530617224134773812888477)
  ·
    refine ⟨15198981459050540179833179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40530617224134773812888477 15198981459050540179833179)
    ·
      refine ⟨22798472188575810269749769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15198981459050540179833179 22798472188575810269749769)
      ·
        refine ⟨17098854141431857702312327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22798472188575810269749769 17098854141431857702312327)
        ·
          refine ⟨25648281212147786553468491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17098854141431857702312327 25648281212147786553468491)
          ·
            refine ⟨38472421818221679830202737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25648281212147786553468491 38472421818221679830202737)
            ·
              refine ⟨28854316363666259872652053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38472421818221679830202737 28854316363666259872652053)
              ·
                refine ⟨1352546079546855931530565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28854316363666259872652053 1352546079546855931530565)
                ·
                  refine ⟨253602389915035487161981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352546079546855931530565 253602389915035487161981)
                  ·
                    rfl

theorem cell22_2222500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_2222500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222500 prefixEnd_2222500 := by exact prefixLift 2222500
  have htrace : WordTrace (prefixWord ++ tailWord_2222500) baseStart_2222500 baseEnd_2222500 := by
    simpa [prefixWord, tailWord_2222500, baseEnd_2222500] using wordTrace_append hprefix tailTrace_2222500
  have hstable : (prefixWord ++ tailWord_2222500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222500).length < 2 ^ (prefixWord ++ tailWord_2222500).sum := by decide
  have hdescent : baseEnd_2222500 < baseStart_2222500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222532 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2222532 : Nat := 118140960795 + 2222532 * 2 ^ 59
def prefixEnd_2222532 : Nat := 4983230072969 + 3 ^ 40 * 2222532 * 2
def baseEnd_2222532 : Nat := 760818123999069044685845

theorem tailTrace_2222532 : CollatzResearch.WordTrace tailWord_2222532 prefixEnd_2222532 760818123999069044685845 := by
  unfold tailWord_2222532
  simp only [CollatzResearch.WordTrace]
  refine ⟨40531200792076808545470925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54041601056102411393961233 40531200792076808545470925)
  ·
    refine ⟨15199200297028803204551597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40531200792076808545470925 15199200297028803204551597)
    ·
      refine ⟨5699700111385801201706849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15199200297028803204551597 5699700111385801201706849)
      ·
        refine ⟨4274775083539350901280137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5699700111385801201706849 4274775083539350901280137)
        ·
          refine ⟨3206081312654513175960103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4274775083539350901280137 3206081312654513175960103)
          ·
            refine ⟨4809121968981769763940155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206081312654513175960103 4809121968981769763940155)
            ·
              refine ⟨7213682953472654645910233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809121968981769763940155 7213682953472654645910233)
              ·
                refine ⟨5410262215104490984432675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7213682953472654645910233 5410262215104490984432675)
                ·
                  refine ⟨8115393322656736476649013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5410262215104490984432675 8115393322656736476649013)
                  ·
                    refine ⟨760818123999069044685845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8115393322656736476649013 760818123999069044685845)
                    ·
                      rfl

theorem cell22_2222532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2222532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222532 prefixEnd_2222532 := by exact prefixLift 2222532
  have htrace : WordTrace (prefixWord ++ tailWord_2222532) baseStart_2222532 baseEnd_2222532 := by
    simpa [prefixWord, tailWord_2222532, baseEnd_2222532] using wordTrace_append hprefix tailTrace_2222532
  have hstable : (prefixWord ++ tailWord_2222532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222532).length < 2 ^ (prefixWord ++ tailWord_2222532).sum := by decide
  have hdescent : baseEnd_2222532 < baseStart_2222532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222560 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 3, 3]
def baseStart_2222560 : Nat := 118140960795 + 2222560 * 2 ^ 59
def prefixEnd_2222560 : Nat := 4983230072969 + 3 ^ 40 * 2222560 * 2
def baseEnd_2222560 : Nat := 760827708971286304985759

theorem tailTrace_2222560 : CollatzResearch.WordTrace tailWord_2222560 prefixEnd_2222560 760827708971286304985759 := by
  unfold tailWord_2222560
  simp only [CollatzResearch.WordTrace]
  refine ⟨40531711414026088936480567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54042281885368118581974089 40531711414026088936480567)
  ·
    refine ⟨60797567121039133404720851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40531711414026088936480567 60797567121039133404720851)
    ·
      refine ⟨91196350681558700107081277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60797567121039133404720851 91196350681558700107081277)
      ·
        refine ⟨34198631505584512540155479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91196350681558700107081277 34198631505584512540155479)
        ·
          refine ⟨51297947258376768810233219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34198631505584512540155479 51297947258376768810233219)
          ·
            refine ⟨76946920887565153215349829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51297947258376768810233219 76946920887565153215349829)
            ·
              refine ⟨14427547666418466227878093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76946920887565153215349829 14427547666418466227878093)
              ·
                refine ⟨5410330374906924835454285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14427547666418466227878093 5410330374906924835454285)
                ·
                  refine ⟨2028873890590096813295357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5410330374906924835454285 2028873890590096813295357)
                  ·
                    refine ⟨760827708971286304985759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2028873890590096813295357 760827708971286304985759)
                    ·
                      rfl

theorem cell22_2222560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_2222560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222560 prefixEnd_2222560 := by exact prefixLift 2222560
  have htrace : WordTrace (prefixWord ++ tailWord_2222560) baseStart_2222560 baseEnd_2222560 := by
    simpa [prefixWord, tailWord_2222560, baseEnd_2222560] using wordTrace_append hprefix tailTrace_2222560
  have hstable : (prefixWord ++ tailWord_2222560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222560).length < 2 ^ (prefixWord ++ tailWord_2222560).sum := by decide
  have hdescent : baseEnd_2222560 < baseStart_2222560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222581 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2222581 : Nat := 118140960795 + 2222581 * 2 ^ 59
def prefixEnd_2222581 : Nat := 4983230072969 + 3 ^ 40 * 2222581 * 2
def baseEnd_2222581 : Nat := 760834897700449250210695

theorem tailTrace_2222581 : CollatzResearch.WordTrace tailWord_2222581 prefixEnd_2222581 760834897700449250210695 := by
  unfold tailWord_2222581
  simp only [CollatzResearch.WordTrace]
  refine ⟨81064188760976098459475597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54042792507317398972983731 81064188760976098459475597)
  ·
    refine ⟨30399070785366036922303349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81064188760976098459475597 30399070785366036922303349)
    ·
      refine ⟨2849912886128065961465939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30399070785366036922303349 2849912886128065961465939)
      ·
        refine ⟨4274869329192098942198909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849912886128065961465939 4274869329192098942198909)
        ·
          refine ⟨1603075998447037103324591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4274869329192098942198909 1603075998447037103324591)
          ·
            refine ⟨2404613997670555654986887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603075998447037103324591 2404613997670555654986887)
            ·
              refine ⟨3606920996505833482480331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404613997670555654986887 3606920996505833482480331)
              ·
                refine ⟨5410381494758750223720497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606920996505833482480331 5410381494758750223720497)
                ·
                  refine ⟨4057786121069062667790373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5410381494758750223720497 4057786121069062667790373)
                  ·
                    refine ⟨760834897700449250210695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4057786121069062667790373 760834897700449250210695)
                    ·
                      rfl

theorem cell22_2222581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2222581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222581 prefixEnd_2222581 := by exact prefixLift 2222581
  have htrace : WordTrace (prefixWord ++ tailWord_2222581) baseStart_2222581 baseEnd_2222581 := by
    simpa [prefixWord, tailWord_2222581, baseEnd_2222581] using wordTrace_append hprefix tailTrace_2222581
  have hstable : (prefixWord ++ tailWord_2222581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222581).length < 2 ^ (prefixWord ++ tailWord_2222581).sum := by decide
  have hdescent : baseEnd_2222581 < baseStart_2222581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222588 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_2222588 : Nat := 118140960795 + 2222588 * 2 ^ 59
def prefixEnd_2222588 : Nat := 4983230072969 + 3 ^ 40 * 2222588 * 2
def baseEnd_2222588 : Nat := 760837293943503565285673

theorem tailTrace_2222588 : CollatzResearch.WordTrace tailWord_2222588 prefixEnd_2222588 760837293943503565285673 := by
  unfold tailWord_2222588
  simp only [CollatzResearch.WordTrace]
  refine ⟨40532222035975369327490209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54042962714633825769986945 40532222035975369327490209)
  ·
    refine ⟨30399166526981526995617657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40532222035975369327490209 30399166526981526995617657)
    ·
      refine ⟨22799374895236145246713243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30399166526981526995617657 22799374895236145246713243)
      ·
        refine ⟨34199062342854217870069865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22799374895236145246713243 34199062342854217870069865)
        ·
          refine ⟨25649296757140663402552399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34199062342854217870069865 25649296757140663402552399)
          ·
            refine ⟨38473945135710995103828599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25649296757140663402552399 38473945135710995103828599)
            ·
              refine ⟨57710917703566492655742899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38473945135710995103828599 57710917703566492655742899)
              ·
                refine ⟨86566376555349738983614349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57710917703566492655742899 86566376555349738983614349)
                ·
                  refine ⟨32462391208256152118855381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86566376555349738983614349 32462391208256152118855381)
                  ·
                    refine ⟨760837293943503565285673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32462391208256152118855381 760837293943503565285673)
                    ·
                      rfl

theorem cell22_2222588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_2222588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222588 prefixEnd_2222588 := by exact prefixLift 2222588
  have htrace : WordTrace (prefixWord ++ tailWord_2222588) baseStart_2222588 baseEnd_2222588 := by
    simpa [prefixWord, tailWord_2222588, baseEnd_2222588] using wordTrace_append hprefix tailTrace_2222588
  have hstable : (prefixWord ++ tailWord_2222588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222588).length < 2 ^ (prefixWord ++ tailWord_2222588).sum := by decide
  have hdescent : baseEnd_2222588 < baseStart_2222588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222624 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 5]
def baseStart_2222624 : Nat := 118140960795 + 2222624 * 2 ^ 59
def prefixEnd_2222624 : Nat := 4983230072969 + 3 ^ 40 * 2222624 * 2
def baseEnd_2222624 : Nat := 253616539159737157128521

theorem tailTrace_2222624 : CollatzResearch.WordTrace tailWord_2222624 prefixEnd_2222624 253616539159737157128521 := by
  unfold tailWord_2222624
  simp only [CollatzResearch.WordTrace]
  refine ⟨40532878549910158401645463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54043838066546877868860617 40532878549910158401645463)
  ·
    refine ⟨60799317824865237602468195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40532878549910158401645463 60799317824865237602468195)
    ·
      refine ⟨91198976737297856403702293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60799317824865237602468195 91198976737297856403702293)
      ·
        refine ⟨4274952034560837018923545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91198976737297856403702293 4274952034560837018923545)
        ·
          refine ⟨3206214025920627764192659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4274952034560837018923545 3206214025920627764192659)
          ·
            refine ⟨4809321038880941646288989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206214025920627764192659 4809321038880941646288989)
            ·
              refine ⟨1803495389580353117358371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4809321038880941646288989 1803495389580353117358371)
              ·
                refine ⟨2705243084370529676037557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803495389580353117358371 2705243084370529676037557)
                ·
                  refine ⟨253616539159737157128521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2705243084370529676037557 253616539159737157128521)
                  ·
                    rfl

theorem cell22_2222624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_2222624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222624 prefixEnd_2222624 := by exact prefixLift 2222624
  have htrace : WordTrace (prefixWord ++ tailWord_2222624) baseStart_2222624 baseEnd_2222624 := by
    simpa [prefixWord, tailWord_2222624, baseEnd_2222624] using wordTrace_append hprefix tailTrace_2222624
  have hstable : (prefixWord ++ tailWord_2222624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222624).length < 2 ^ (prefixWord ++ tailWord_2222624).sum := by decide
  have hdescent : baseEnd_2222624 < baseStart_2222624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222669 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2222669 : Nat := 118140960795 + 2222669 * 2 ^ 59
def prefixEnd_2222669 : Nat := 4983230072969 + 3 ^ 40 * 2222669 * 2
def baseEnd_2222669 : Nat := 253621673966282118003475

theorem tailTrace_2222669 : CollatzResearch.WordTrace tailWord_2222669 prefixEnd_2222669 253621673966282118003475 := by
  unfold tailWord_2222669
  simp only [CollatzResearch.WordTrace]
  refine ⟨81067398384657289488679061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54044932256438192992452707 81067398384657289488679061)
  ·
    refine ⟨3800034299280810444781831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81067398384657289488679061 3800034299280810444781831)
    ·
      refine ⟨5700051448921215667172747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3800034299280810444781831 5700051448921215667172747)
      ·
        refine ⟨8550077173381823500759121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5700051448921215667172747 8550077173381823500759121)
        ·
          refine ⟨6412557880036367625569341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8550077173381823500759121 6412557880036367625569341)
          ·
            refine ⟨2404709205013637859588503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6412557880036367625569341 2404709205013637859588503)
            ·
              refine ⟨3607063807520456789382755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404709205013637859588503 3607063807520456789382755)
              ·
                refine ⟨5410595711280685184074133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607063807520456789382755 5410595711280685184074133)
                ·
                  refine ⟨253621673966282118003475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5410595711280685184074133 253621673966282118003475)
                  ·
                    rfl

theorem cell22_2222669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2222669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222669 prefixEnd_2222669 := by exact prefixLift 2222669
  have htrace : WordTrace (prefixWord ++ tailWord_2222669) baseStart_2222669 baseEnd_2222669 := by
    simpa [prefixWord, tailWord_2222669, baseEnd_2222669] using wordTrace_append hprefix tailTrace_2222669
  have hstable : (prefixWord ++ tailWord_2222669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222669).length < 2 ^ (prefixWord ++ tailWord_2222669).sum := by decide
  have hdescent : baseEnd_2222669 < baseStart_2222669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222746 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_2222746 : Nat := 118140960795 + 2222746 * 2 ^ 59
def prefixEnd_2222746 : Nat := 4983230072969 + 3 ^ 40 * 2222746 * 2
def baseEnd_2222746 : Nat := 760891380572443819835189

theorem tailTrace_2222746 : CollatzResearch.WordTrace tailWord_2222746 prefixEnd_2222746 760891380572443819835189 := by
  unfold tailWord_2222746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20267551701344582909808023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54046804536918887759488061 20267551701344582909808023)
  ·
    refine ⟨30401327552016874364712035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20267551701344582909808023 30401327552016874364712035)
    ·
      refine ⟨45601991328025311547068053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30401327552016874364712035 45601991328025311547068053)
      ·
        refine ⟨2137593343501186478768815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45601991328025311547068053 2137593343501186478768815)
        ·
          refine ⟨3206390015251779718153223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137593343501186478768815 3206390015251779718153223)
          ·
            refine ⟨4809585022877669577229835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206390015251779718153223 4809585022877669577229835)
            ·
              refine ⟨7214377534316504365844753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809585022877669577229835 7214377534316504365844753)
              ·
                refine ⟨5410783150737378274383565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7214377534316504365844753 5410783150737378274383565)
                ·
                  refine ⟨2029043681526516852893837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5410783150737378274383565 2029043681526516852893837)
                  ·
                    refine ⟨760891380572443819835189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029043681526516852893837 760891380572443819835189)
                    ·
                      rfl

theorem cell22_2222746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_2222746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222746 prefixEnd_2222746 := by exact prefixLift 2222746
  have htrace : WordTrace (prefixWord ++ tailWord_2222746) baseStart_2222746 baseEnd_2222746 := by
    simpa [prefixWord, tailWord_2222746, baseEnd_2222746] using wordTrace_append hprefix tailTrace_2222746
  have hstable : (prefixWord ++ tailWord_2222746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222746).length < 2 ^ (prefixWord ++ tailWord_2222746).sum := by decide
  have hdescent : baseEnd_2222746 < baseStart_2222746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222770 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_2222770 : Nat := 118140960795 + 2222770 * 2 ^ 59
def prefixEnd_2222770 : Nat := 4983230072969 + 3 ^ 40 * 2222770 * 2
def baseEnd_2222770 : Nat := 253633198754305252411705

theorem tailTrace_2222770 : CollatzResearch.WordTrace tailWord_2222770 prefixEnd_2222770 253633198754305252411705 := by
  unfold tailWord_2222770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20267770539322845934526441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54047388104860922492070509 20267770539322845934526441)
  ·
    refine ⟨15200827904492134450894831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20267770539322845934526441 15200827904492134450894831)
    ·
      refine ⟨22801241856738201676342247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15200827904492134450894831 22801241856738201676342247)
      ·
        refine ⟨34201862785107302514513371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22801241856738201676342247 34201862785107302514513371)
        ·
          refine ⟨51302794177660953771770057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34201862785107302514513371 51302794177660953771770057)
          ·
            refine ⟨38477095633245715328827543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51302794177660953771770057 38477095633245715328827543)
            ·
              refine ⟨57715643449868572993241315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38477095633245715328827543 57715643449868572993241315)
              ·
                refine ⟨86573465174802859489861973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57715643449868572993241315 86573465174802859489861973)
                ·
                  refine ⟨253633198754305252411705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 86573465174802859489861973 253633198754305252411705)
                  ·
                    rfl

theorem cell22_2222770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_2222770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222770 prefixEnd_2222770 := by exact prefixLift 2222770
  have htrace : WordTrace (prefixWord ++ tailWord_2222770) baseStart_2222770 baseEnd_2222770 := by
    simpa [prefixWord, tailWord_2222770, baseEnd_2222770] using wordTrace_append hprefix tailTrace_2222770
  have hstable : (prefixWord ++ tailWord_2222770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222770).length < 2 ^ (prefixWord ++ tailWord_2222770).sum := by decide
  have hdescent : baseEnd_2222770 < baseStart_2222770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222817 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2222817 : Nat := 118140960795 + 2222817 * 2 ^ 59
def prefixEnd_2222817 : Nat := 4983230072969 + 3 ^ 40 * 2222817 * 2
def baseEnd_2222817 : Nat := 760915685323423301309971

theorem tailTrace_2222817 : CollatzResearch.WordTrace tailWord_2222817 prefixEnd_2222817 760915685323423301309971 := by
  unfold tailWord_2222817
  simp only [CollatzResearch.WordTrace]
  refine ⟨81072796388121110765066705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54048530925414073843377803 81072796388121110765066705)
  ·
    refine ⟨60804597291090833073800029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81072796388121110765066705 60804597291090833073800029)
    ·
      refine ⟨22801723984159062402675011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60804597291090833073800029 22801723984159062402675011)
      ·
        refine ⟨34202585976238593604012517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22801723984159062402675011 34202585976238593604012517)
        ·
          refine ⟨6412984870544736300752347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34202585976238593604012517 6412984870544736300752347)
          ·
            refine ⟨9619477305817104451128521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412984870544736300752347 9619477305817104451128521)
            ·
              refine ⟨7214607979362828338346391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9619477305817104451128521 7214607979362828338346391)
              ·
                refine ⟨10821911969044242507519587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7214607979362828338346391 10821911969044242507519587)
                ·
                  refine ⟨16232867953566363761279381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10821911969044242507519587 16232867953566363761279381)
                  ·
                    refine ⟨760915685323423301309971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16232867953566363761279381 760915685323423301309971)
                    ·
                      rfl

theorem cell22_2222817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2222817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222817 prefixEnd_2222817 := by exact prefixLift 2222817
  have htrace : WordTrace (prefixWord ++ tailWord_2222817) baseStart_2222817 baseEnd_2222817 := by
    simpa [prefixWord, tailWord_2222817, baseEnd_2222817] using wordTrace_append hprefix tailTrace_2222817
  have hstable : (prefixWord ++ tailWord_2222817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222817).length < 2 ^ (prefixWord ++ tailWord_2222817).sum := by decide
  have hdescent : baseEnd_2222817 < baseStart_2222817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222819 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 4, 3]
def baseStart_2222819 : Nat := 118140960795 + 2222819 * 2 ^ 59
def prefixEnd_2222819 : Nat := 4983230072969 + 3 ^ 40 * 2222819 * 2
def baseEnd_2222819 : Nat := 760916369964295962759965

theorem tailTrace_2222819 : CollatzResearch.WordTrace tailWord_2222819 prefixEnd_2222819 760916369964295962759965 := by
  unfold tailWord_2222819
  simp only [CollatzResearch.WordTrace]
  refine ⟨81072869334113865106639511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54048579556075910071093007 81072869334113865106639511)
  ·
    refine ⟨121609304001170797659959267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81072869334113865106639511 121609304001170797659959267)
    ·
      refine ⟨182413956001756196489938901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121609304001170797659959267 182413956001756196489938901)
      ·
        refine ⟨4275327093791160855232943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 182413956001756196489938901 4275327093791160855232943)
        ·
          refine ⟨6412990640686741282849415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275327093791160855232943 6412990640686741282849415)
          ·
            refine ⟨9619485961030111924274123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412990640686741282849415 9619485961030111924274123)
            ·
              refine ⟨14429228941545167886411185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9619485961030111924274123 14429228941545167886411185)
              ·
                refine ⟨10821921706158875914808389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14429228941545167886411185 10821921706158875914808389)
                ·
                  refine ⟨2029110319904789234026573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10821921706158875914808389 2029110319904789234026573)
                  ·
                    refine ⟨760916369964295962759965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029110319904789234026573 760916369964295962759965)
                    ·
                      rfl

theorem cell22_2222819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 3].length) (baseStart_2222819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222819 prefixEnd_2222819 := by exact prefixLift 2222819
  have htrace : WordTrace (prefixWord ++ tailWord_2222819) baseStart_2222819 baseEnd_2222819 := by
    simpa [prefixWord, tailWord_2222819, baseEnd_2222819] using wordTrace_append hprefix tailTrace_2222819
  have hstable : (prefixWord ++ tailWord_2222819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222819).length < 2 ^ (prefixWord ++ tailWord_2222819).sum := by decide
  have hdescent : baseEnd_2222819 < baseStart_2222819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222821 : List Nat := [1, 3, 1, 4, 1, 4, 1, 3, 4]
def baseStart_2222821 : Nat := 118140960795 + 2222821 * 2 ^ 59
def prefixEnd_2222821 : Nat := 4983230072969 + 3 ^ 40 * 2222821 * 2
def baseEnd_2222821 : Nat := 253639018201722874736653

theorem tailTrace_2222821 : CollatzResearch.WordTrace tailWord_2222821 prefixEnd_2222821 253639018201722874736653 := by
  unfold tailWord_2222821
  simp only [CollatzResearch.WordTrace]
  refine ⟨81072942280106619448212317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54048628186737746298808211 81072942280106619448212317)
  ·
    refine ⟨30402353355039982293079619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81072942280106619448212317 30402353355039982293079619)
    ·
      refine ⟨45603530032559973439619429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30402353355039982293079619 45603530032559973439619429)
      ·
        refine ⟨8550661881104995019928643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45603530032559973439619429 8550661881104995019928643)
        ·
          refine ⟨12825992821657492529892965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8550661881104995019928643 12825992821657492529892965)
          ·
            refine ⟨2404873654060779849354931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12825992821657492529892965 2404873654060779849354931)
            ·
              refine ⟨3607310481091169774032397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404873654060779849354931 3607310481091169774032397)
              ·
                refine ⟨1352741430409188665262149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3607310481091169774032397 1352741430409188665262149)
                ·
                  refine ⟨253639018201722874736653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352741430409188665262149 253639018201722874736653)
                  ·
                    rfl

theorem cell22_2222821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_2222821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222821 prefixEnd_2222821 := by exact prefixLift 2222821
  have htrace : WordTrace (prefixWord ++ tailWord_2222821) baseStart_2222821 baseEnd_2222821 := by
    simpa [prefixWord, tailWord_2222821, baseEnd_2222821] using wordTrace_append hprefix tailTrace_2222821
  have hstable : (prefixWord ++ tailWord_2222821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222821).length < 2 ^ (prefixWord ++ tailWord_2222821).sum := by decide
  have hdescent : baseEnd_2222821 < baseStart_2222821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222834 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_2222834 : Nat := 118140960795 + 2222834 * 2 ^ 59
def prefixEnd_2222834 : Nat := 4983230072969 + 3 ^ 40 * 2222834 * 2
def baseEnd_2222834 : Nat := 760921504770840923634919

theorem tailTrace_2222834 : CollatzResearch.WordTrace tailWord_2222834 prefixEnd_2222834 760921504770840923634919 := by
  unfold tailWord_2222834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20268354107264880667108889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54048944286039681778957037 20268354107264880667108889)
  ·
    refine ⟨15201265580448660500331667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20268354107264880667108889 15201265580448660500331667)
    ·
      refine ⟨22801898370672990750497501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15201265580448660500331667 22801898370672990750497501)
      ·
        refine ⟨8550711889002371531436563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22801898370672990750497501 8550711889002371531436563)
        ·
          refine ⟨12826067833503557297154845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8550711889002371531436563 12826067833503557297154845)
          ·
            refine ⟨4809775437563833986433067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12826067833503557297154845 4809775437563833986433067)
            ·
              refine ⟨7214663156345750979649601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809775437563833986433067 7214663156345750979649601)
              ·
                refine ⟨5410997367259313234737201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7214663156345750979649601 5410997367259313234737201)
                ·
                  refine ⟨4058248025444484926052901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5410997367259313234737201 4058248025444484926052901)
                  ·
                    refine ⟨760921504770840923634919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4058248025444484926052901 760921504770840923634919)
                    ·
                      rfl

theorem cell22_2222834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_2222834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222834 prefixEnd_2222834 := by exact prefixLift 2222834
  have htrace : WordTrace (prefixWord ++ tailWord_2222834) baseStart_2222834 baseEnd_2222834 := by
    simpa [prefixWord, tailWord_2222834, baseEnd_2222834] using wordTrace_append hprefix tailTrace_2222834
  have hstable : (prefixWord ++ tailWord_2222834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222834).length < 2 ^ (prefixWord ++ tailWord_2222834).sum := by decide
  have hdescent : baseEnd_2222834 < baseStart_2222834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222881 : List Nat := [1, 2, 3, 2, 1, 2, 2, 5, 1, 3]
def baseStart_2222881 : Nat := 118140960795 + 2222881 * 2 ^ 59
def prefixEnd_2222881 : Nat := 4983230072969 + 3 ^ 40 * 2222881 * 2
def baseEnd_2222881 : Nat := 760937593831348467709775

theorem tailTrace_2222881 : CollatzResearch.WordTrace tailWord_2222881 prefixEnd_2222881 760937593831348467709775 := by
  unfold tailWord_2222881
  simp only [CollatzResearch.WordTrace]
  refine ⟨81075130659889249695396497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54050087106592833130264331 81075130659889249695396497)
  ·
    refine ⟨60806347994916937271547373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81075130659889249695396497 60806347994916937271547373)
    ·
      refine ⟨22802380498093851476830265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60806347994916937271547373 22802380498093851476830265)
      ·
        refine ⟨17101785373570388607622699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22802380498093851476830265 17101785373570388607622699)
        ·
          refine ⟨25652678060355582911434049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17101785373570388607622699 25652678060355582911434049)
          ·
            refine ⟨19239508545266687183575537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25652678060355582911434049 19239508545266687183575537)
            ·
              refine ⟨14429631408950015387681653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19239508545266687183575537 14429631408950015387681653)
              ·
                refine ⟨1352777944589063942595155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14429631408950015387681653 1352777944589063942595155)
                ·
                  refine ⟨2029166916883595913892733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352777944589063942595155 2029166916883595913892733)
                  ·
                    refine ⟨760937593831348467709775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029166916883595913892733 760937593831348467709775)
                    ·
                      rfl

theorem cell22_2222881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_2222881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222881 prefixEnd_2222881 := by exact prefixLift 2222881
  have htrace : WordTrace (prefixWord ++ tailWord_2222881) baseStart_2222881 baseEnd_2222881 := by
    simpa [prefixWord, tailWord_2222881, baseEnd_2222881] using wordTrace_append hprefix tailTrace_2222881
  have hstable : (prefixWord ++ tailWord_2222881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222881).length < 2 ^ (prefixWord ++ tailWord_2222881).sum := by decide
  have hdescent : baseEnd_2222881 < baseStart_2222881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222892 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_2222892 : Nat := 118140960795 + 2222892 * 2 ^ 59
def prefixEnd_2222892 : Nat := 4983230072969 + 3 ^ 40 * 2222892 * 2
def baseEnd_2222892 : Nat := 760941359356148105684741

theorem tailTrace_2222892 : CollatzResearch.WordTrace tailWord_2222892 prefixEnd_2222892 760941359356148105684741 := by
  unfold tailWord_2222892
  simp only [CollatzResearch.WordTrace]
  refine ⟨40537765931424699287023465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54050354575232932382697953 40537765931424699287023465)
  ·
    refine ⟨30403324448568524465267599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40537765931424699287023465 30403324448568524465267599)
    ·
      refine ⟨45604986672852786697901399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30403324448568524465267599 45604986672852786697901399)
      ·
        refine ⟨68407480009279180046852099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45604986672852786697901399 68407480009279180046852099)
        ·
          refine ⟨102611220013918770070278149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68407480009279180046852099 102611220013918770070278149)
          ·
            refine ⟨19239603752609769388177153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102611220013918770070278149 19239603752609769388177153)
            ·
              refine ⟨14429702814457327041132865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19239603752609769388177153 14429702814457327041132865)
              ·
                refine ⟨10822277110842995280849649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14429702814457327041132865 10822277110842995280849649)
                ·
                  refine ⟨8116707833132246460637237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10822277110842995280849649 8116707833132246460637237)
                  ·
                    refine ⟨760941359356148105684741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8116707833132246460637237 760941359356148105684741)
                    ·
                      rfl

theorem cell22_2222892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_2222892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222892 prefixEnd_2222892 := by exact prefixLift 2222892
  have htrace : WordTrace (prefixWord ++ tailWord_2222892) baseStart_2222892 baseEnd_2222892 := by
    simpa [prefixWord, tailWord_2222892, baseEnd_2222892] using wordTrace_append hprefix tailTrace_2222892
  have hstable : (prefixWord ++ tailWord_2222892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222892).length < 2 ^ (prefixWord ++ tailWord_2222892).sum := by decide
  have hdescent : baseEnd_2222892 < baseStart_2222892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222924 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_2222924 : Nat := 118140960795 + 2222924 * 2 ^ 59
def prefixEnd_2222924 : Nat := 4983230072969 + 3 ^ 40 * 2222924 * 2
def baseEnd_2222924 : Nat := 760952313610110688884643

theorem tailTrace_2222924 : CollatzResearch.WordTrace tailWord_2222924 prefixEnd_2222924 760952313610110688884643 := by
  unfold tailWord_2222924
  simp only [CollatzResearch.WordTrace]
  refine ⟨40538349499366734019605913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54051132665822312026141217 40538349499366734019605913)
  ·
    refine ⟨30403762124525050514704435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40538349499366734019605913 30403762124525050514704435)
    ·
      refine ⟨45605643186787575772056653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30403762124525050514704435 45605643186787575772056653)
      ·
        refine ⟨17102116195045340914521245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45605643186787575772056653 17102116195045340914521245)
        ·
          refine ⟨6413293573142002842945467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17102116195045340914521245 6413293573142002842945467)
          ·
            refine ⟨9619940359713004264418201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6413293573142002842945467 9619940359713004264418201)
            ·
              refine ⟨7214955269784753198313651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9619940359713004264418201 7214955269784753198313651)
              ·
                refine ⟨10822432904677129797470477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7214955269784753198313651 10822432904677129797470477)
                ·
                  refine ⟨4058412339253923674051429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10822432904677129797470477 4058412339253923674051429)
                  ·
                    refine ⟨760952313610110688884643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4058412339253923674051429 760952313610110688884643)
                    ·
                      rfl

theorem cell22_2222924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_2222924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222924 prefixEnd_2222924 := by exact prefixLift 2222924
  have htrace : WordTrace (prefixWord ++ tailWord_2222924) baseStart_2222924 baseEnd_2222924 := by
    simpa [prefixWord, tailWord_2222924, baseEnd_2222924] using wordTrace_append hprefix tailTrace_2222924
  have hstable : (prefixWord ++ tailWord_2222924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222924).length < 2 ^ (prefixWord ++ tailWord_2222924).sum := by decide
  have hdescent : baseEnd_2222924 < baseStart_2222924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222984 : List Nat := [2, 1, 3, 3, 2, 2, 1, 8]
def baseStart_2222984 : Nat := 118140960795 + 2222984 * 2 ^ 59
def prefixEnd_2222984 : Nat := 4983230072969 + 3 ^ 40 * 2222984 * 2
def baseEnd_2222984 : Nat := 84552539204032281376051

theorem tailTrace_2222984 : CollatzResearch.WordTrace tailWord_2222984 prefixEnd_2222984 84552539204032281376051 := by
  unfold tailWord_2222984
  simp only [CollatzResearch.WordTrace]
  refine ⟨40539443689258049143198003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54052591585677398857597337 40539443689258049143198003)
  ·
    refine ⟨60809165533887073714797005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40539443689258049143198003 60809165533887073714797005)
    ·
      refine ⟨22803437075207652643048877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60809165533887073714797005 22803437075207652643048877)
      ·
        refine ⟨8551288903202869741143329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22803437075207652643048877 8551288903202869741143329)
        ·
          refine ⟨6413466677402152305857497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8551288903202869741143329 6413466677402152305857497)
          ·
            refine ⟨4810100008051614229393123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6413466677402152305857497 4810100008051614229393123)
            ·
              refine ⟨7215150012077421344089685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810100008051614229393123 7215150012077421344089685)
              ·
                refine ⟨84552539204032281376051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7215150012077421344089685 84552539204032281376051)
                ·
                  rfl

theorem cell22_2222984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_2222984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2222984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2222984 prefixEnd_2222984 := by exact prefixLift 2222984
  have htrace : WordTrace (prefixWord ++ tailWord_2222984) baseStart_2222984 baseEnd_2222984 := by
    simpa [prefixWord, tailWord_2222984, baseEnd_2222984] using wordTrace_append hprefix tailTrace_2222984
  have hstable : (prefixWord ++ tailWord_2222984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222984).length < 2 ^ (prefixWord ++ tailWord_2222984).sum := by decide
  have hdescent : baseEnd_2222984 < baseStart_2222984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223196 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2223196 : Nat := 118140960795 + 2223196 * 2 ^ 59
def prefixEnd_2223196 : Nat := 4983230072969 + 3 ^ 40 * 2223196 * 2
def baseEnd_2223196 : Nat := 761045424768792646083809

theorem tailTrace_2223196 : CollatzResearch.WordTrace tailWord_2223196 prefixEnd_2223196 761045424768792646083809 := by
  unfold tailWord_2223196
  simp only [CollatzResearch.WordTrace]
  refine ⟨40543309826874029246556721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54057746435832038995408961 40543309826874029246556721)
  ·
    refine ⟨30407482370155521934917541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40543309826874029246556721 30407482370155521934917541)
    ·
      refine ⟨5701402944404160362797039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30407482370155521934917541 5701402944404160362797039)
      ·
        refine ⟨8552104416606240544195559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701402944404160362797039 8552104416606240544195559)
        ·
          refine ⟨12828156624909360816293339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8552104416606240544195559 12828156624909360816293339)
          ·
            refine ⟨19242234937364041224440009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12828156624909360816293339 19242234937364041224440009)
            ·
              refine ⟨14431676203023030918330007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19242234937364041224440009 14431676203023030918330007)
              ·
                refine ⟨21647514304534546377495011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14431676203023030918330007 21647514304534546377495011)
                ·
                  refine ⟨32471271456801819566242517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21647514304534546377495011 32471271456801819566242517)
                  ·
                    refine ⟨761045424768792646083809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32471271456801819566242517 761045424768792646083809)
                    ·
                      rfl

theorem cell22_2223196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2223196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223196 prefixEnd_2223196 := by exact prefixLift 2223196
  have htrace : WordTrace (prefixWord ++ tailWord_2223196) baseStart_2223196 baseEnd_2223196 := by
    simpa [prefixWord, tailWord_2223196, baseEnd_2223196] using wordTrace_append hprefix tailTrace_2223196
  have hstable : (prefixWord ++ tailWord_2223196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223196).length < 2 ^ (prefixWord ++ tailWord_2223196).sum := by decide
  have hdescent : baseEnd_2223196 < baseStart_2223196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223258 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_2223258 : Nat := 118140960795 + 2223258 * 2 ^ 59
def prefixEnd_2223258 : Nat := 4983230072969 + 3 ^ 40 * 2223258 * 2
def baseEnd_2223258 : Nat := 761066648635845151033619

theorem tailTrace_2223258 : CollatzResearch.WordTrace tailWord_2223258 prefixEnd_2223258 761066648635845151033619 := by
  unfold tailWord_2223258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20272220244880860770467607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54059253986348962054580285 20272220244880860770467607)
  ·
    refine ⟨30408330367321291155701411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20272220244880860770467607 30408330367321291155701411)
    ·
      refine ⟨45612495550981936733552117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30408330367321291155701411 45612495550981936733552117)
      ·
        refine ⟨4276171457904556568770511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45612495550981936733552117 4276171457904556568770511)
        ·
          refine ⟨6414257186856834853155767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276171457904556568770511 6414257186856834853155767)
          ·
            refine ⟨9621385780285252279733651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6414257186856834853155767 9621385780285252279733651)
            ·
              refine ⟨14432078670427878419600477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9621385780285252279733651 14432078670427878419600477)
              ·
                refine ⟨5412029501410454407350179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14432078670427878419600477 5412029501410454407350179)
                ·
                  refine ⟨8118044252115681611025269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5412029501410454407350179 8118044252115681611025269)
                  ·
                    refine ⟨761066648635845151033619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8118044252115681611025269 761066648635845151033619)
                    ·
                      rfl

theorem cell22_2223258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_2223258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223258 prefixEnd_2223258 := by exact prefixLift 2223258
  have htrace : WordTrace (prefixWord ++ tailWord_2223258) baseStart_2223258 baseEnd_2223258 := by
    simpa [prefixWord, tailWord_2223258, baseEnd_2223258] using wordTrace_append hprefix tailTrace_2223258
  have hstable : (prefixWord ++ tailWord_2223258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223258).length < 2 ^ (prefixWord ++ tailWord_2223258).sum := by decide
  have hdescent : baseEnd_2223258 < baseStart_2223258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223277 : List Nat := [1, 5, 2, 1, 3, 1, 2, 3, 4]
def baseStart_2223277 : Nat := 118140960795 + 2223277 * 2 ^ 59
def prefixEnd_2223277 : Nat := 4983230072969 + 3 ^ 40 * 2223277 * 2
def baseEnd_2223277 : Nat := 253691050908045144936187

theorem tailTrace_2223277 : CollatzResearch.WordTrace tailWord_2223277 prefixEnd_2223277 253691050908045144936187 := by
  unfold tailWord_2223277
  simp only [CollatzResearch.WordTrace]
  refine ⟨81089573966454609326812085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54059715977636406217874723 81089573966454609326812085)
  ·
    refine ⟨7602147559355119624388633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81089573966454609326812085 7602147559355119624388633)
    ·
      refine ⟨5701610669516339718291475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7602147559355119624388633 5701610669516339718291475)
      ·
        refine ⟨8552416004274509577437213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701610669516339718291475 8552416004274509577437213)
        ·
          refine ⟨3207156001602941091538955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8552416004274509577437213 3207156001602941091538955)
          ·
            refine ⟨4810734002404411637308433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3207156001602941091538955 4810734002404411637308433)
            ·
              refine ⟨3608050501803308727981325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4810734002404411637308433 3608050501803308727981325)
              ·
                refine ⟨1353018938176240772992997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3608050501803308727981325 1353018938176240772992997)
                ·
                  refine ⟨253691050908045144936187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353018938176240772992997 253691050908045144936187)
                  ·
                    rfl

theorem cell22_2223277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_2223277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223277 prefixEnd_2223277 := by exact prefixLift 2223277
  have htrace : WordTrace (prefixWord ++ tailWord_2223277) baseStart_2223277 baseEnd_2223277 := by
    simpa [prefixWord, tailWord_2223277, baseEnd_2223277] using wordTrace_append hprefix tailTrace_2223277
  have hstable : (prefixWord ++ tailWord_2223277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223277).length < 2 ^ (prefixWord ++ tailWord_2223277).sum := by decide
  have hdescent : baseEnd_2223277 < baseStart_2223277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223292 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_2223292 : Nat := 118140960795 + 2223292 * 2 ^ 59
def prefixEnd_2223292 : Nat := 4983230072969 + 3 ^ 40 * 2223292 * 2
def baseEnd_2223292 : Nat := 761078287530680395683515

theorem tailTrace_2223292 : CollatzResearch.WordTrace tailWord_2223292 prefixEnd_2223292 761078287530680395683515 := by
  unfold tailWord_2223292
  simp only [CollatzResearch.WordTrace]
  refine ⟨40545060530700133444304065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54060080707600177925738753 40545060530700133444304065)
  ·
    refine ⟨30408795398025100083228049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40545060530700133444304065 30408795398025100083228049)
    ·
      refine ⟨22806596548518825062421037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30408795398025100083228049 22806596548518825062421037)
      ·
        refine ⟨8552473705694559398407889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22806596548518825062421037 8552473705694559398407889)
        ·
          refine ⟨6414355279270919548805917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8552473705694559398407889 6414355279270919548805917)
          ·
            refine ⟨2405383229726594830802219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6414355279270919548805917 2405383229726594830802219)
            ·
              refine ⟨3608074844589892246203329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405383229726594830802219 3608074844589892246203329)
              ·
                refine ⟨2706056133442419184652497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3608074844589892246203329 2706056133442419184652497)
                ·
                  refine ⟨2029542100081814388489373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2706056133442419184652497 2029542100081814388489373)
                  ·
                    refine ⟨761078287530680395683515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029542100081814388489373 761078287530680395683515)
                    ·
                      rfl

theorem cell22_2223292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_2223292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223292 prefixEnd_2223292 := by exact prefixLift 2223292
  have htrace : WordTrace (prefixWord ++ tailWord_2223292) baseStart_2223292 baseEnd_2223292 := by
    simpa [prefixWord, tailWord_2223292, baseEnd_2223292] using wordTrace_append hprefix tailTrace_2223292
  have hstable : (prefixWord ++ tailWord_2223292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223292).length < 2 ^ (prefixWord ++ tailWord_2223292).sum := by decide
  have hdescent : baseEnd_2223292 < baseStart_2223292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223309 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2223309 : Nat := 118140960795 + 2223309 * 2 ^ 59
def prefixEnd_2223309 : Nat := 4983230072969 + 3 ^ 40 * 2223309 * 2
def baseEnd_2223309 : Nat := 761084106978098018008463

theorem tailTrace_2223309 : CollatzResearch.WordTrace tailWord_2223309 prefixEnd_2223309 761084106978098018008463 := by
  unfold tailWord_2223309
  simp only [CollatzResearch.WordTrace]
  refine ⟨81090741102338678791976981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54060494068225785861317987 81090741102338678791976981)
  ·
    refine ⟨3801128489172125568373921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81090741102338678791976981 3801128489172125568373921)
    ·
      refine ⟨2850846366879094176280441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3801128489172125568373921 2850846366879094176280441)
      ·
        refine ⟨2138134775159320632210331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2850846366879094176280441 2138134775159320632210331)
        ·
          refine ⟨3207202162738980948315497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138134775159320632210331 3207202162738980948315497)
          ·
            refine ⟨2405401622054235711236623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3207202162738980948315497 2405401622054235711236623)
            ·
              refine ⟨3608102433081353566854935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405401622054235711236623 3608102433081353566854935)
              ·
                refine ⟨5412153649622030350282403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608102433081353566854935 5412153649622030350282403)
                ·
                  refine ⟨8118230474433045525423605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5412153649622030350282403 8118230474433045525423605)
                  ·
                    refine ⟨761084106978098018008463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8118230474433045525423605 761084106978098018008463)
                    ·
                      rfl

theorem cell22_2223309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2223309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223309 prefixEnd_2223309 := by exact prefixLift 2223309
  have htrace : WordTrace (prefixWord ++ tailWord_2223309) baseStart_2223309 baseEnd_2223309 := by
    simpa [prefixWord, tailWord_2223309, baseEnd_2223309] using wordTrace_append hprefix tailTrace_2223309
  have hstable : (prefixWord ++ tailWord_2223309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223309).length < 2 ^ (prefixWord ++ tailWord_2223309).sum := by decide
  have hdescent : baseEnd_2223309 < baseStart_2223309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223397 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_2223397 : Nat := 118140960795 + 2223397 * 2 ^ 59
def prefixEnd_2223397 : Nat := 4983230072969 + 3 ^ 40 * 2223397 * 2
def baseEnd_2223397 : Nat := 761114231176495121808193

theorem tailTrace_2223397 : CollatzResearch.WordTrace tailWord_2223397 prefixEnd_2223397 761114231176495121808193 := by
  unfold tailWord_2223397
  simp only [CollatzResearch.WordTrace]
  refine ⟨81093950726019869821180445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54062633817346579880786963 81093950726019869821180445)
  ·
    refine ⟨30410231522257451182942667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81093950726019869821180445 30410231522257451182942667)
    ·
      refine ⟨45615347283386176774414001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30410231522257451182942667 45615347283386176774414001)
      ·
        refine ⟨34211510462539632580810501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45615347283386176774414001 34211510462539632580810501)
        ·
          refine ⟨6414658211726181108901969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34211510462539632580810501 6414658211726181108901969)
          ·
            refine ⟨4810993658794635831676477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6414658211726181108901969 4810993658794635831676477)
            ·
              refine ⟨1804122622047988436878679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4810993658794635831676477 1804122622047988436878679)
              ·
                refine ⟨2706183933071982655318019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804122622047988436878679 2706183933071982655318019)
                ·
                  refine ⟨4059275899607973982977029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706183933071982655318019 4059275899607973982977029)
                  ·
                    refine ⟨761114231176495121808193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059275899607973982977029 761114231176495121808193)
                    ·
                      rfl

theorem cell22_2223397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_2223397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223397 prefixEnd_2223397 := by exact prefixLift 2223397
  have htrace : WordTrace (prefixWord ++ tailWord_2223397) baseStart_2223397 baseEnd_2223397 := by
    simpa [prefixWord, tailWord_2223397, baseEnd_2223397] using wordTrace_append hprefix tailTrace_2223397
  have hstable : (prefixWord ++ tailWord_2223397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223397).length < 2 ^ (prefixWord ++ tailWord_2223397).sum := by decide
  have hdescent : baseEnd_2223397 < baseStart_2223397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223408 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_2223408 : Nat := 118140960795 + 2223408 * 2 ^ 59
def prefixEnd_2223408 : Nat := 4983230072969 + 3 ^ 40 * 2223408 * 2
def baseEnd_2223408 : Nat := 761117996701294759783159

theorem tailTrace_2223408 : CollatzResearch.WordTrace tailWord_2223408 prefixEnd_2223408 761117996701294759783159 := by
  unfold tailWord_2223408
  simp only [CollatzResearch.WordTrace]
  refine ⟨40547175964490009349915439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54062901285986679133220585 40547175964490009349915439)
  ·
    refine ⟨60820763946735014024873159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40547175964490009349915439 60820763946735014024873159)
    ·
      refine ⟨91231145920102521037309739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60820763946735014024873159 91231145920102521037309739)
      ·
        refine ⟨136846718880153781555964609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91231145920102521037309739 136846718880153781555964609)
        ·
          refine ⟨102635039160115336166973457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136846718880153781555964609 102635039160115336166973457)
          ·
            refine ⟨76976279370086502125230093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102635039160115336166973457 76976279370086502125230093)
            ·
              refine ⟨28866104763782438296961285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76976279370086502125230093 28866104763782438296961285)
              ·
                refine ⟨5412394643209207180680241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28866104763782438296961285 5412394643209207180680241)
                ·
                  refine ⟨4059295982406905385510181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5412394643209207180680241 4059295982406905385510181)
                  ·
                    refine ⟨761117996701294759783159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059295982406905385510181 761117996701294759783159)
                    ·
                      rfl

theorem cell22_2223408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_2223408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223408 prefixEnd_2223408 := by exact prefixLift 2223408
  have htrace : WordTrace (prefixWord ++ tailWord_2223408) baseStart_2223408 baseEnd_2223408 := by
    simpa [prefixWord, tailWord_2223408, baseEnd_2223408] using wordTrace_append hprefix tailTrace_2223408
  have hstable : (prefixWord ++ tailWord_2223408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223408).length < 2 ^ (prefixWord ++ tailWord_2223408).sum := by decide
  have hdescent : baseEnd_2223408 < baseStart_2223408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223412 : List Nat := [2, 5, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2223412 : Nat := 118140960795 + 2223412 * 2 ^ 59
def prefixEnd_2223412 : Nat := 4983230072969 + 3 ^ 40 * 2223412 * 2
def baseEnd_2223412 : Nat := 253706455327680027561049

theorem tailTrace_2223412 : CollatzResearch.WordTrace tailWord_2223412 prefixEnd_2223412 253706455327680027561049 := by
  unfold tailWord_2223412
  simp only [CollatzResearch.WordTrace]
  refine ⟨40547248910482763691488245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54062998547310351588650993 40547248910482763691488245)
  ·
    refine ⟨3801304585357759096077023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40547248910482763691488245 3801304585357759096077023)
    ·
      refine ⟨5701956878036638644115535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3801304585357759096077023 5701956878036638644115535)
      ·
        refine ⟨8552935317054957966173303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701956878036638644115535 8552935317054957966173303)
        ·
          refine ⟨12829402975582436949259955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8552935317054957966173303 12829402975582436949259955)
          ·
            refine ⟨19244104463373655423889933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12829402975582436949259955 19244104463373655423889933)
            ·
              refine ⟨7216539173765120783958725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19244104463373655423889933 7216539173765120783958725)
              ·
                refine ⟨1353101095080960146992261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7216539173765120783958725 1353101095080960146992261)
                ·
                  refine ⟨253706455327680027561049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353101095080960146992261 253706455327680027561049)
                  ·
                    rfl

theorem cell22_2223412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2223412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223412 prefixEnd_2223412 := by exact prefixLift 2223412
  have htrace : WordTrace (prefixWord ++ tailWord_2223412) baseStart_2223412 baseEnd_2223412 := by
    simpa [prefixWord, tailWord_2223412, baseEnd_2223412] using wordTrace_append hprefix tailTrace_2223412
  have hstable : (prefixWord ++ tailWord_2223412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223412).length < 2 ^ (prefixWord ++ tailWord_2223412).sum := by decide
  have hdescent : baseEnd_2223412 < baseStart_2223412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223423 : List Nat := [1, 1, 2, 2, 4, 2, 3, 7]
def baseStart_2223423 : Nat := 118140960795 + 2223423 * 2 ^ 59
def prefixEnd_2223423 : Nat := 4983230072969 + 3 ^ 40 * 2223423 * 2
def baseEnd_2223423 : Nat := 84569236834204413406457

theorem tailTrace_2223423 : CollatzResearch.WordTrace tailWord_2223423 prefixEnd_2223423 84569236834204413406457 := by
  unfold tailWord_2223423
  simp only [CollatzResearch.WordTrace]
  refine ⟨81094899023925676261626923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54063266015950450841084615 81094899023925676261626923)
  ·
    refine ⟨121642348535888514392440385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81094899023925676261626923 121642348535888514392440385)
    ·
      refine ⟨91231761401916385794330289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121642348535888514392440385 91231761401916385794330289)
      ·
        refine ⟨68423821051437289345747717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91231761401916385794330289 68423821051437289345747717)
        ·
          refine ⟨12829466447144491752327697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68423821051437289345747717 12829466447144491752327697)
          ·
            refine ⟨9622099835358368814245773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12829466447144491752327697 9622099835358368814245773)
            ·
              refine ⟨3608287438259388305342165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9622099835358368814245773 3608287438259388305342165)
              ·
                refine ⟨84569236834204413406457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3608287438259388305342165 84569236834204413406457)
                ·
                  rfl

theorem cell22_2223423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 7].length) (baseStart_2223423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223423 prefixEnd_2223423 := by exact prefixLift 2223423
  have htrace : WordTrace (prefixWord ++ tailWord_2223423) baseStart_2223423 baseEnd_2223423 := by
    simpa [prefixWord, tailWord_2223423, baseEnd_2223423] using wordTrace_append hprefix tailTrace_2223423
  have hstable : (prefixWord ++ tailWord_2223423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223423).length < 2 ^ (prefixWord ++ tailWord_2223423).sum := by decide
  have hdescent : baseEnd_2223423 < baseStart_2223423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223472 : List Nat := [2, 1, 1, 1, 4, 2, 1, 6, 1, 3]
def baseStart_2223472 : Nat := 118140960795 + 2223472 * 2 ^ 59
def prefixEnd_2223472 : Nat := 4983230072969 + 3 ^ 40 * 2223472 * 2
def baseEnd_2223472 : Nat := 761139905209219926182963

theorem tailTrace_2223472 : CollatzResearch.WordTrace tailWord_2223472 prefixEnd_2223472 761139905209219926182963 := by
  unfold tailWord_2223472
  simp only [CollatzResearch.WordTrace]
  refine ⟨40548343100374078815080335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54064457467165438420107113 40548343100374078815080335)
  ·
    refine ⟨60822514650561118222620503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40548343100374078815080335 60822514650561118222620503)
    ·
      refine ⟨91233771975841677333930755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60822514650561118222620503 91233771975841677333930755)
      ·
        refine ⟨136850657963762516000896133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91233771975841677333930755 136850657963762516000896133)
        ·
          refine ⟨25659498368205471750168025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136850657963762516000896133 25659498368205471750168025)
          ·
            refine ⟨19244623776154103812626019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25659498368205471750168025 19244623776154103812626019)
            ·
              refine ⟨28866935664231155718939029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19244623776154103812626019 28866935664231155718939029)
              ·
                refine ⟨1353137609260835424325267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28866935664231155718939029 1353137609260835424325267)
                ·
                  refine ⟨2029706413891253136487901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353137609260835424325267 2029706413891253136487901)
                  ·
                    refine ⟨761139905209219926182963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029706413891253136487901 761139905209219926182963)
                    ·
                      rfl

theorem cell22_2223472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 3].length) (baseStart_2223472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223472 prefixEnd_2223472 := by exact prefixLift 2223472
  have htrace : WordTrace (prefixWord ++ tailWord_2223472) baseStart_2223472 baseEnd_2223472 := by
    simpa [prefixWord, tailWord_2223472, baseEnd_2223472] using wordTrace_append hprefix tailTrace_2223472
  have hstable : (prefixWord ++ tailWord_2223472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223472).length < 2 ^ (prefixWord ++ tailWord_2223472).sum := by decide
  have hdescent : baseEnd_2223472 < baseStart_2223472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223483 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 2, 5]
def baseStart_2223483 : Nat := 118140960795 + 2223483 * 2 ^ 59
def prefixEnd_2223483 : Nat := 4983230072969 + 3 ^ 40 * 2223483 * 2
def baseEnd_2223483 : Nat := 761143670734019564157929

theorem tailTrace_2223483 : CollatzResearch.WordTrace tailWord_2223483 prefixEnd_2223483 761143670734019564157929 := by
  unfold tailWord_2223483
  simp only [CollatzResearch.WordTrace]
  refine ⟨81097087403708306508811103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54064724935805537672540735 81097087403708306508811103)
  ·
    refine ⟨121645631105562459763216655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81097087403708306508811103 121645631105562459763216655)
    ·
      refine ⟨182468446658343689644824983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121645631105562459763216655 182468446658343689644824983)
      ·
        refine ⟨273702669987515534467237475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182468446658343689644824983 273702669987515534467237475)
        ·
          refine ⟨410554004981273301700856213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273702669987515534467237475 410554004981273301700856213)
          ·
            refine ⟨19244718983497186017227635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 410554004981273301700856213 19244718983497186017227635)
            ·
              refine ⟨28867078475245779025841453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19244718983497186017227635 28867078475245779025841453)
              ·
                refine ⟨10825154428217167134690545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28867078475245779025841453 10825154428217167134690545)
                ·
                  refine ⟨8118865821162875351017909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10825154428217167134690545 8118865821162875351017909)
                  ·
                    refine ⟨761143670734019564157929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8118865821162875351017909 761143670734019564157929)
                    ·
                      rfl

theorem cell22_2223483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_2223483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223483 prefixEnd_2223483 := by exact prefixLift 2223483
  have htrace : WordTrace (prefixWord ++ tailWord_2223483) baseStart_2223483 baseEnd_2223483 := by
    simpa [prefixWord, tailWord_2223483, baseEnd_2223483] using wordTrace_append hprefix tailTrace_2223483
  have hstable : (prefixWord ++ tailWord_2223483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223483).length < 2 ^ (prefixWord ++ tailWord_2223483).sum := by decide
  have hdescent : baseEnd_2223483 < baseStart_2223483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223581 : List Nat := [1, 4, 3, 1, 1, 4, 2, 2, 4]
def baseStart_2223581 : Nat := 118140960795 + 2223581 * 2 ^ 59
def prefixEnd_2223581 : Nat := 4983230072969 + 3 ^ 40 * 2223581 * 2
def baseEnd_2223581 : Nat := 253725739378926658402543

theorem tailTrace_2223581 : CollatzResearch.WordTrace tailWord_2223581 prefixEnd_2223581 253725739378926658402543 := by
  unfold tailWord_2223581
  simp only [CollatzResearch.WordTrace]
  refine ⟨81100661757353269245878597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54067107838235512830585731 81100661757353269245878597)
  ·
    refine ⟨15206374079503737983602237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81100661757353269245878597 15206374079503737983602237)
    ·
      refine ⟨5702390279813901743850839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15206374079503737983602237 5702390279813901743850839)
      ·
        refine ⟨8553585419720852615776259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702390279813901743850839 8553585419720852615776259)
        ·
          refine ⟨12830378129581278923664389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8553585419720852615776259 12830378129581278923664389)
          ·
            refine ⟨2405695899296489798187073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12830378129581278923664389 2405695899296489798187073)
            ·
              refine ⟨1804271924472367348640305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405695899296489798187073 1804271924472367348640305)
              ·
                refine ⟨1353203943354275511480229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804271924472367348640305 1353203943354275511480229)
                ·
                  refine ⟨253725739378926658402543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353203943354275511480229 253725739378926658402543)
                  ·
                    rfl

theorem cell22_2223581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_2223581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223581 prefixEnd_2223581 := by exact prefixLift 2223581
  have htrace : WordTrace (prefixWord ++ tailWord_2223581) baseStart_2223581 baseEnd_2223581 := by
    simpa [prefixWord, tailWord_2223581, baseEnd_2223581] using wordTrace_append hprefix tailTrace_2223581
  have hstable : (prefixWord ++ tailWord_2223581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223581).length < 2 ^ (prefixWord ++ tailWord_2223581).sum := by decide
  have hdescent : baseEnd_2223581 < baseStart_2223581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223624 : List Nat := [2, 1, 3, 2, 1, 1, 3, 5, 1, 3]
def baseStart_2223624 : Nat := 118140960795 + 2223624 * 2 ^ 59
def prefixEnd_2223624 : Nat := 4983230072969 + 3 ^ 40 * 2223624 * 2
def baseEnd_2223624 : Nat := 761191937915542196382497

theorem tailTrace_2223624 : CollatzResearch.WordTrace tailWord_2223624 prefixEnd_2223624 761191937915542196382497 := by
  unfold tailWord_2223624
  simp only [CollatzResearch.WordTrace]
  refine ⟨40551115048098743794846963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54068153397464991726462617 40551115048098743794846963)
  ·
    refine ⟨60826672572148115692270445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40551115048098743794846963 60826672572148115692270445)
    ·
      refine ⟨22810002214555543384601417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60826672572148115692270445 22810002214555543384601417)
      ·
        refine ⟨17107501660916657538451063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22810002214555543384601417 17107501660916657538451063)
        ·
          refine ⟨25661252491374986307676595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17107501660916657538451063 25661252491374986307676595)
          ·
            refine ⟨38491878737062479461514893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25661252491374986307676595 38491878737062479461514893)
            ·
              refine ⟨14434454526398429798068085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38491878737062479461514893 14434454526398429798068085)
              ·
                refine ⟨1353230111849852793568883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14434454526398429798068085 1353230111849852793568883)
                ·
                  refine ⟨2029845167774779190353325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353230111849852793568883 2029845167774779190353325)
                  ·
                    refine ⟨761191937915542196382497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029845167774779190353325 761191937915542196382497)
                    ·
                      rfl

theorem cell22_2223624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_2223624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223624 prefixEnd_2223624 := by exact prefixLift 2223624
  have htrace : WordTrace (prefixWord ++ tailWord_2223624) baseStart_2223624 baseEnd_2223624 := by
    simpa [prefixWord, tailWord_2223624, baseEnd_2223624] using wordTrace_append hprefix tailTrace_2223624
  have hstable : (prefixWord ++ tailWord_2223624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223624).length < 2 ^ (prefixWord ++ tailWord_2223624).sum := by decide
  have hdescent : baseEnd_2223624 < baseStart_2223624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223635 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 2, 5]
def baseStart_2223635 : Nat := 118140960795 + 2223635 * 2 ^ 59
def prefixEnd_2223635 : Nat := 4983230072969 + 3 ^ 40 * 2223635 * 2
def baseEnd_2223635 : Nat := 761195703440341834357463

theorem tailTrace_2223635 : CollatzResearch.WordTrace tailWord_2223635 prefixEnd_2223635 761195703440341834357463 := by
  unfold tailWord_2223635
  simp only [CollatzResearch.WordTrace]
  refine ⟨81102631299157636468344359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54068420866105090978896239 81102631299157636468344359)
  ·
    refine ⟨121653946948736454702516539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81102631299157636468344359 121653946948736454702516539)
    ·
      refine ⟨182480920423104682053774809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121653946948736454702516539 182480920423104682053774809)
      ·
        refine ⟨136860690317328511540331107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182480920423104682053774809 136860690317328511540331107)
        ·
          refine ⟨205291035475992767310496661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136860690317328511540331107 205291035475992767310496661)
          ·
            refine ⟨9623017287937160967679531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 205291035475992767310496661 9623017287937160967679531)
            ·
              refine ⟨14434525931905741451519297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9623017287937160967679531 14434525931905741451519297)
              ·
                refine ⟨10825894448929306088639473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14434525931905741451519297 10825894448929306088639473)
                ·
                  refine ⟨8119420836696979566479605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10825894448929306088639473 8119420836696979566479605)
                  ·
                    refine ⟨761195703440341834357463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8119420836696979566479605 761195703440341834357463)
                    ·
                      rfl

theorem cell22_2223635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_2223635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223635 prefixEnd_2223635 := by exact prefixLift 2223635
  have htrace : WordTrace (prefixWord ++ tailWord_2223635) baseStart_2223635 baseEnd_2223635 := by
    simpa [prefixWord, tailWord_2223635, baseEnd_2223635] using wordTrace_append hprefix tailTrace_2223635
  have hstable : (prefixWord ++ tailWord_2223635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223635).length < 2 ^ (prefixWord ++ tailWord_2223635).sum := by decide
  have hdescent : baseEnd_2223635 < baseStart_2223635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223637 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 5]
def baseStart_2223637 : Nat := 118140960795 + 2223637 * 2 ^ 59
def prefixEnd_2223637 : Nat := 4983230072969 + 3 ^ 40 * 2223637 * 2
def baseEnd_2223637 : Nat := 253732129360404831935819

theorem tailTrace_2223637 : CollatzResearch.WordTrace tailWord_2223637 prefixEnd_2223637 253732129360404831935819 := by
  unfold tailWord_2223637
  simp only [CollatzResearch.WordTrace]
  refine ⟨81102704245150390809917165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54068469496766927206611443 81102704245150390809917165)
  ·
    refine ⟨30413514091931396553718937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81102704245150390809917165 30413514091931396553718937)
    ·
      refine ⟨22810135568948547415289203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30413514091931396553718937 22810135568948547415289203)
      ·
        refine ⟨34215203353422821122933805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22810135568948547415289203 34215203353422821122933805)
        ·
          refine ⟨12830701257533557921100177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34215203353422821122933805 12830701257533557921100177)
          ·
            refine ⟨9623025943150168440825133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12830701257533557921100177 9623025943150168440825133)
            ·
              refine ⟨3608634728681313165309425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9623025943150168440825133 3608634728681313165309425)
              ·
                refine ⟨2706476046510984873982069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3608634728681313165309425 2706476046510984873982069)
                ·
                  refine ⟨253732129360404831935819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2706476046510984873982069 253732129360404831935819)
                  ·
                    rfl

theorem cell22_2223637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_2223637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223637 prefixEnd_2223637 := by exact prefixLift 2223637
  have htrace : WordTrace (prefixWord ++ tailWord_2223637) baseStart_2223637 baseEnd_2223637 := by
    simpa [prefixWord, tailWord_2223637, baseEnd_2223637] using wordTrace_append hprefix tailTrace_2223637
  have hstable : (prefixWord ++ tailWord_2223637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223637).length < 2 ^ (prefixWord ++ tailWord_2223637).sum := by decide
  have hdescent : baseEnd_2223637 < baseStart_2223637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223667 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 1, 4]
def baseStart_2223667 : Nat := 118140960795 + 2223667 * 2 ^ 59
def prefixEnd_2223667 : Nat := 4983230072969 + 3 ^ 40 * 2223667 * 2
def baseEnd_2223667 : Nat := 761206657694304417557365

theorem tailTrace_2223667 : CollatzResearch.WordTrace tailWord_2223667 prefixEnd_2223667 761206657694304417557365 := by
  unfold tailWord_2223667
  simp only [CollatzResearch.WordTrace]
  refine ⟨81103798435041705933509255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54069198956694470622339503 81103798435041705933509255)
  ·
    refine ⟨121655697652562558900263883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81103798435041705933509255 121655697652562558900263883)
    ·
      refine ⟨182483546478843838350395825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121655697652562558900263883 182483546478843838350395825)
      ·
        refine ⟨136862659859132878762796869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182483546478843838350395825 136862659859132878762796869)
        ·
          refine ⟨25661748723587414768024413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136862659859132878762796869 25661748723587414768024413)
          ·
            refine ⟨9623155771345280538009155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25661748723587414768024413 9623155771345280538009155)
            ·
              refine ⟨14434733657017920807013733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9623155771345280538009155 14434733657017920807013733)
              ·
                refine ⟨2706512560690860151315075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14434733657017920807013733 2706512560690860151315075)
                ·
                  refine ⟨4059768841036290226972613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706512560690860151315075 4059768841036290226972613)
                  ·
                    refine ⟨761206657694304417557365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4059768841036290226972613 761206657694304417557365)
                    ·
                      rfl

theorem cell22_2223667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 4].length) (baseStart_2223667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223667 prefixEnd_2223667 := by exact prefixLift 2223667
  have htrace : WordTrace (prefixWord ++ tailWord_2223667) baseStart_2223667 baseEnd_2223667 := by
    simpa [prefixWord, tailWord_2223667, baseEnd_2223667] using wordTrace_append hprefix tailTrace_2223667
  have hstable : (prefixWord ++ tailWord_2223667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223667).length < 2 ^ (prefixWord ++ tailWord_2223667).sum := by decide
  have hdescent : baseEnd_2223667 < baseStart_2223667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223680 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_2223680 : Nat := 118140960795 + 2223680 * 2 ^ 59
def prefixEnd_2223680 : Nat := 4983230072969 + 3 ^ 40 * 2223680 * 2
def baseEnd_2223680 : Nat := 761211107859976716982325

theorem tailTrace_2223680 : CollatzResearch.WordTrace tailWord_2223680 prefixEnd_2223680 761211107859976716982325 := by
  unfold tailWord_2223680
  simp only [CollatzResearch.WordTrace]
  refine ⟨40552136291997304576866247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54069515055996406102488329 40552136291997304576866247)
  ·
    refine ⟨60828204437995956865299371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40552136291997304576866247 60828204437995956865299371)
    ·
      refine ⟨91242306656993935297949057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60828204437995956865299371 91242306656993935297949057)
      ·
        refine ⟨68431729992745451473461793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91242306656993935297949057 68431729992745451473461793)
        ·
          refine ⟨51323797494559088605096345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68431729992745451473461793 51323797494559088605096345)
          ·
            refine ⟨38492848120919316453822259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51323797494559088605096345 38492848120919316453822259)
            ·
              refine ⟨57739272181378974680733389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38492848120919316453822259 57739272181378974680733389)
              ·
                refine ⟨21652227068017115505275021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57739272181378974680733389 21652227068017115505275021)
                ·
                  refine ⟨8119585150506418314478133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21652227068017115505275021 8119585150506418314478133)
                  ·
                    refine ⟨761211107859976716982325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8119585150506418314478133 761211107859976716982325)
                    ·
                      rfl

theorem cell22_2223680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_2223680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223680 prefixEnd_2223680 := by exact prefixLift 2223680
  have htrace : WordTrace (prefixWord ++ tailWord_2223680) baseStart_2223680 baseEnd_2223680 := by
    simpa [prefixWord, tailWord_2223680, baseEnd_2223680] using wordTrace_append hprefix tailTrace_2223680
  have hstable : (prefixWord ++ tailWord_2223680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223680).length < 2 ^ (prefixWord ++ tailWord_2223680).sum := by decide
  have hdescent : baseEnd_2223680 < baseStart_2223680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223697 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 4, 3]
def baseStart_2223697 : Nat := 118140960795 + 2223697 * 2 ^ 59
def prefixEnd_2223697 : Nat := 4983230072969 + 3 ^ 40 * 2223697 * 2
def baseEnd_2223697 : Nat := 761216927307394339307273

theorem tailTrace_2223697 : CollatzResearch.WordTrace tailWord_2223697 prefixEnd_2223697 761216927307394339307273 := by
  unfold tailWord_2223697
  simp only [CollatzResearch.WordTrace]
  refine ⟨81104892624933021057101345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54069928416622014038067563 81104892624933021057101345)
  ·
    refine ⟨60828669468699765792826009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81104892624933021057101345 60828669468699765792826009)
    ·
      refine ⟨45621502101524824344619507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60828669468699765792826009 45621502101524824344619507)
      ·
        refine ⟨68432253152287236516929261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45621502101524824344619507 68432253152287236516929261)
        ·
          refine ⟨25662094932107713693848473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68432253152287236516929261 25662094932107713693848473)
          ·
            refine ⟨19246571199080785270386355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25662094932107713693848473 19246571199080785270386355)
            ·
              refine ⟨28869856798621177905579533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19246571199080785270386355 28869856798621177905579533)
              ·
                refine ⟨10826196299482941714592325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28869856798621177905579533 10826196299482941714592325)
                ·
                  refine ⟨2029911806153051571486061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10826196299482941714592325 2029911806153051571486061)
                  ·
                    refine ⟨761216927307394339307273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029911806153051571486061 761216927307394339307273)
                    ·
                      rfl

theorem cell22_2223697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_2223697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223697 prefixEnd_2223697 := by exact prefixLift 2223697
  have htrace : WordTrace (prefixWord ++ tailWord_2223697) baseStart_2223697 baseEnd_2223697 := by
    simpa [prefixWord, tailWord_2223697, baseEnd_2223697] using wordTrace_append hprefix tailTrace_2223697
  have hstable : (prefixWord ++ tailWord_2223697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223697).length < 2 ^ (prefixWord ++ tailWord_2223697).sum := by decide
  have hdescent : baseEnd_2223697 < baseStart_2223697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223806 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_2223806 : Nat := 118140960795 + 2223806 * 2 ^ 59
def prefixEnd_2223806 : Nat := 4983230072969 + 3 ^ 40 * 2223806 * 2
def baseEnd_2223806 : Nat := 253751413411651462777313

theorem tailTrace_2223806 : CollatzResearch.WordTrace tailWord_2223806 prefixEnd_2223806 253751413411651462777313 := by
  unfold tailWord_2223806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10138608522692266584102409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54072578787692088448546181 10138608522692266584102409)
  ·
    refine ⟨7603956392019199938076807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10138608522692266584102409 7603956392019199938076807)
    ·
      refine ⟨11405934588028799907115211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7603956392019199938076807 11405934588028799907115211)
      ·
        refine ⟨17108901882043199860672817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11405934588028799907115211 17108901882043199860672817)
        ·
          refine ⟨12831676411532399895504613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17108901882043199860672817 12831676411532399895504613)
          ·
            refine ⟨2405939327162324980407115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12831676411532399895504613 2405939327162324980407115)
            ·
              refine ⟨3608908990743487470610673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405939327162324980407115 3608908990743487470610673)
              ·
                refine ⟨2706681743057615602958005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3608908990743487470610673 2706681743057615602958005)
                ·
                  refine ⟨253751413411651462777313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2706681743057615602958005 253751413411651462777313)
                  ·
                    rfl

theorem cell22_2223806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_2223806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223806 prefixEnd_2223806 := by exact prefixLift 2223806
  have htrace : WordTrace (prefixWord ++ tailWord_2223806) baseStart_2223806 baseEnd_2223806 := by
    simpa [prefixWord, tailWord_2223806, baseEnd_2223806] using wordTrace_append hprefix tailTrace_2223806
  have hstable : (prefixWord ++ tailWord_2223806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223806).length < 2 ^ (prefixWord ++ tailWord_2223806).sum := by decide
  have hdescent : baseEnd_2223806 < baseStart_2223806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223821 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2223821 : Nat := 118140960795 + 2223821 * 2 ^ 59
def prefixEnd_2223821 : Nat := 4983230072969 + 3 ^ 40 * 2223821 * 2
def baseEnd_2223821 : Nat := 761259375041499349206893

theorem tailTrace_2223821 : CollatzResearch.WordTrace tailWord_2223821 prefixEnd_2223821 761259375041499349206893 := by
  unfold tailWord_2223821
  simp only [CollatzResearch.WordTrace]
  refine ⟨81109415276483790234615317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54072943517655860156410211 81109415276483790234615317)
  ·
    refine ⟨3802003841085177667247593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81109415276483790234615317 3802003841085177667247593)
    ·
      refine ⟨2851502880813883250435695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3802003841085177667247593 2851502880813883250435695)
      ·
        refine ⟨4277254321220824875653543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851502880813883250435695 4277254321220824875653543)
        ·
          refine ⟨6415881481831237313480315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277254321220824875653543 6415881481831237313480315)
          ·
            refine ⟨9623822222746855970220473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415881481831237313480315 9623822222746855970220473)
            ·
              refine ⟨7217866667060141977665355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9623822222746855970220473 7217866667060141977665355)
              ·
                refine ⟨10826800000590212966498033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7217866667060141977665355 10826800000590212966498033)
                ·
                  refine ⟨8120100000442659724873525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10826800000590212966498033 8120100000442659724873525)
                  ·
                    refine ⟨761259375041499349206893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8120100000442659724873525 761259375041499349206893)
                    ·
                      rfl

theorem cell22_2223821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2223821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223821 prefixEnd_2223821 := by exact prefixLift 2223821
  have htrace : WordTrace (prefixWord ++ tailWord_2223821) baseStart_2223821 baseEnd_2223821 := by
    simpa [prefixWord, tailWord_2223821, baseEnd_2223821] using wordTrace_append hprefix tailTrace_2223821
  have hstable : (prefixWord ++ tailWord_2223821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223821).length < 2 ^ (prefixWord ++ tailWord_2223821).sum := by decide
  have hdescent : baseEnd_2223821 < baseStart_2223821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223907 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 9]
def baseStart_2223907 : Nat := 118140960795 + 2223907 * 2 ^ 59
def prefixEnd_2223907 : Nat := 4983230072969 + 3 ^ 40 * 2223907 * 2
def baseEnd_2223907 : Nat := 253762938199674597185543

theorem tailTrace_2223907 : CollatzResearch.WordTrace tailWord_2223907 prefixEnd_2223907 253762938199674597185543 := by
  unfold tailWord_2223907
  simp only [CollatzResearch.WordTrace]
  refine ⟨81112551954172226922245975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54075034636114817948163983 81112551954172226922245975)
  ·
    refine ⟨121668827931258340383368963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81112551954172226922245975 121668827931258340383368963)
    ·
      refine ⟨182503241896887510575053445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121668827931258340383368963 182503241896887510575053445)
      ·
        refine ⟨34219357855666408232822521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182503241896887510575053445 34219357855666408232822521)
        ·
          refine ⟨25664518391749806174616891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34219357855666408232822521 25664518391749806174616891)
          ·
            refine ⟨38496777587624709261925337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25664518391749806174616891 38496777587624709261925337)
            ·
              refine ⟨28872583190718531946444003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38496777587624709261925337 28872583190718531946444003)
              ·
                refine ⟨43308874786077797919666005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28872583190718531946444003 43308874786077797919666005)
                ·
                  refine ⟨253762938199674597185543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43308874786077797919666005 253762938199674597185543)
                  ·
                    rfl

theorem cell22_2223907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_2223907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223907 prefixEnd_2223907 := by exact prefixLift 2223907
  have htrace : WordTrace (prefixWord ++ tailWord_2223907) baseStart_2223907 baseEnd_2223907 := by
    simpa [prefixWord, tailWord_2223907, baseEnd_2223907] using wordTrace_append hprefix tailTrace_2223907
  have hstable : (prefixWord ++ tailWord_2223907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223907).length < 2 ^ (prefixWord ++ tailWord_2223907).sum := by decide
  have hdescent : baseEnd_2223907 < baseStart_2223907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223926 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2223926 : Nat := 118140960795 + 2223926 * 2 ^ 59
def prefixEnd_2223926 : Nat := 4983230072969 + 3 ^ 40 * 2223926 * 2
def baseEnd_2223926 : Nat := 761295318687314075331571

theorem tailTrace_2223926 : CollatzResearch.WordTrace tailWord_2223926 prefixEnd_2223926 761295318687314075331571 := by
  unfold tailWord_2223926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069577808818962072949227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54075496627402262111458421 5069577808818962072949227)
  ·
    refine ⟨7604366713228443109423841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5069577808818962072949227 7604366713228443109423841)
    ·
      refine ⟨5703275034921332332067881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7604366713228443109423841 5703275034921332332067881)
      ·
        refine ⟨4277456276190999249050911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5703275034921332332067881 4277456276190999249050911)
        ·
          refine ⟨6416184414286498873576367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277456276190999249050911 6416184414286498873576367)
          ·
            refine ⟨9624276621429748310364551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6416184414286498873576367 9624276621429748310364551)
            ·
              refine ⟨14436414932144622465546827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9624276621429748310364551 14436414932144622465546827)
              ·
                refine ⟨21654622398216933698320241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14436414932144622465546827 21654622398216933698320241)
                ·
                  refine ⟨16240966798662700273740181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21654622398216933698320241 16240966798662700273740181)
                  ·
                    refine ⟨761295318687314075331571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16240966798662700273740181 761295318687314075331571)
                    ·
                      rfl

theorem cell22_2223926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2223926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223926 prefixEnd_2223926 := by exact prefixLift 2223926
  have htrace : WordTrace (prefixWord ++ tailWord_2223926) baseStart_2223926 baseEnd_2223926 := by
    simpa [prefixWord, tailWord_2223926, baseEnd_2223926] using wordTrace_append hprefix tailTrace_2223926
  have hstable : (prefixWord ++ tailWord_2223926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223926).length < 2 ^ (prefixWord ++ tailWord_2223926).sum := by decide
  have hdescent : baseEnd_2223926 < baseStart_2223926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223928 : List Nat := [2, 1, 2, 1, 3, 4, 1, 4, 1, 3]
def baseStart_2223928 : Nat := 118140960795 + 2223928 * 2 ^ 59
def prefixEnd_2223928 : Nat := 4983230072969 + 3 ^ 40 * 2223928 * 2
def baseEnd_2223928 : Nat := 761296003328186736781565

theorem tailTrace_2223928 : CollatzResearch.WordTrace tailWord_2223928 prefixEnd_2223928 761296003328186736781565 := by
  unfold tailWord_2223928
  simp only [CollatzResearch.WordTrace]
  refine ⟨40556658943548073754380219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54075545258064098339173625 40556658943548073754380219)
  ·
    refine ⟨60834988415322110631570329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40556658943548073754380219 60834988415322110631570329)
    ·
      refine ⟨45626241311491582973677747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60834988415322110631570329 45626241311491582973677747)
      ·
        refine ⟨68439361967237374460516621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45626241311491582973677747 68439361967237374460516621)
        ·
          refine ⟨25664760737714015422693733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68439361967237374460516621 25664760737714015422693733)
          ·
            refine ⟨4812142638321377891755075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25664760737714015422693733 4812142638321377891755075)
            ·
              refine ⟨7218213957482066837632613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812142638321377891755075 7218213957482066837632613)
              ·
                refine ⟨1353415117027887532056115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7218213957482066837632613 1353415117027887532056115)
                ·
                  refine ⟨2030122675541831298084173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353415117027887532056115 2030122675541831298084173)
                  ·
                    refine ⟨761296003328186736781565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030122675541831298084173 761296003328186736781565)
                    ·
                      rfl

theorem cell22_2223928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_2223928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223928 prefixEnd_2223928 := by exact prefixLift 2223928
  have htrace : WordTrace (prefixWord ++ tailWord_2223928) baseStart_2223928 baseEnd_2223928 := by
    simpa [prefixWord, tailWord_2223928, baseEnd_2223928] using wordTrace_append hprefix tailTrace_2223928
  have hstable : (prefixWord ++ tailWord_2223928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223928).length < 2 ^ (prefixWord ++ tailWord_2223928).sum := by decide
  have hdescent : baseEnd_2223928 < baseStart_2223928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223939 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 2, 5]
def baseStart_2223939 : Nat := 118140960795 + 2223939 * 2 ^ 59
def prefixEnd_2223939 : Nat := 4983230072969 + 3 ^ 40 * 2223939 * 2
def baseEnd_2223939 : Nat := 761299768852986374756531

theorem tailTrace_2223939 : CollatzResearch.WordTrace tailWord_2223939 prefixEnd_2223939 761299768852986374756531 := by
  unfold tailWord_2223939
  simp only [CollatzResearch.WordTrace]
  refine ⟨81113719090056296387410871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54075812726704197591607247 81113719090056296387410871)
  ·
    refine ⟨121670578635084444581116307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81113719090056296387410871 121670578635084444581116307)
    ·
      refine ⟨182505867952626666871674461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121670578635084444581116307 182505867952626666871674461)
      ·
        refine ⟨68439700482235000076877923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182505867952626666871674461 68439700482235000076877923)
        ·
          refine ⟨102659550723352500115316885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68439700482235000076877923 102659550723352500115316885)
          ·
            refine ⟨4812166440157148442905479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102659550723352500115316885 4812166440157148442905479)
            ·
              refine ⟨7218249660235722664358219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812166440157148442905479 7218249660235722664358219)
              ·
                refine ⟨10827374490353583996537329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7218249660235722664358219 10827374490353583996537329)
                ·
                  refine ⟨8120530867765187997402997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10827374490353583996537329 8120530867765187997402997)
                  ·
                    refine ⟨761299768852986374756531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8120530867765187997402997 761299768852986374756531)
                    ·
                      rfl

theorem cell22_2223939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_2223939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2223939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2223939 prefixEnd_2223939 := by exact prefixLift 2223939
  have htrace : WordTrace (prefixWord ++ tailWord_2223939) baseStart_2223939 baseEnd_2223939 := by
    simpa [prefixWord, tailWord_2223939, baseEnd_2223939] using wordTrace_append hprefix tailTrace_2223939
  have hstable : (prefixWord ++ tailWord_2223939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223939).length < 2 ^ (prefixWord ++ tailWord_2223939).sum := by decide
  have hdescent : baseEnd_2223939 < baseStart_2223939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224018 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2224018 : Nat := 118140960795 + 2224018 * 2 ^ 59
def prefixEnd_2224018 : Nat := 4983230072969 + 3 ^ 40 * 2224018 * 2
def baseEnd_2224018 : Nat := 761326812167456502031289

theorem tailTrace_2224018 : CollatzResearch.WordTrace tailWord_2224018 prefixEnd_2224018 761326812167456502031289 := by
  unfold tailWord_2224018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20279150114192523219884177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54077733637846728586357805 20279150114192523219884177)
  ·
    refine ⟨15209362585644392414913133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20279150114192523219884177 15209362585644392414913133)
    ·
      refine ⟨5703510969616647155592425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15209362585644392414913133 5703510969616647155592425)
      ·
        refine ⟨4277633227212485366694319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5703510969616647155592425 4277633227212485366694319)
        ·
          refine ⟨6416449840818728050041479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277633227212485366694319 6416449840818728050041479)
          ·
            refine ⟨9624674761228092075062219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6416449840818728050041479 9624674761228092075062219)
            ·
              refine ⟨14437012141842138112593329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9624674761228092075062219 14437012141842138112593329)
              ·
                refine ⟨10827759106381603584444997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14437012141842138112593329 10827759106381603584444997)
                ·
                  refine ⟨2030204832446550672083437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10827759106381603584444997 2030204832446550672083437)
                  ·
                    refine ⟨761326812167456502031289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030204832446550672083437 761326812167456502031289)
                    ·
                      rfl

theorem cell22_2224018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2224018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224018 prefixEnd_2224018 := by exact prefixLift 2224018
  have htrace : WordTrace (prefixWord ++ tailWord_2224018) baseStart_2224018 baseEnd_2224018 := by
    simpa [prefixWord, tailWord_2224018, baseEnd_2224018] using wordTrace_append hprefix tailTrace_2224018
  have hstable : (prefixWord ++ tailWord_2224018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224018).length < 2 ^ (prefixWord ++ tailWord_2224018).sum := by decide
  have hdescent : baseEnd_2224018 < baseStart_2224018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224020 : List Nat := [2, 4, 2, 1, 1, 4, 1, 3, 4]
def baseStart_2224020 : Nat := 118140960795 + 2224020 * 2 ^ 59
def prefixEnd_2224020 : Nat := 4983230072969 + 3 ^ 40 * 2224020 * 2
def baseEnd_2224020 : Nat := 253775832269443054493761

theorem tailTrace_2224020 : CollatzResearch.WordTrace tailWord_2224020 prefixEnd_2224020 253775832269443054493761 := by
  unfold tailWord_2224020
  simp only [CollatzResearch.WordTrace]
  refine ⟨40558336701381423610554757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54077782268508564814073009 40558336701381423610554757)
  ·
    refine ⟨7604688131509016926979017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40558336701381423610554757 7604688131509016926979017)
    ·
      refine ⟨5703516098631762695234263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7604688131509016926979017 5703516098631762695234263)
      ·
        refine ⟨8555274147947644042851395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703516098631762695234263 8555274147947644042851395)
        ·
          refine ⟨12832911221921466064277093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8555274147947644042851395 12832911221921466064277093)
          ·
            refine ⟨2406170854110274887051955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12832911221921466064277093 2406170854110274887051955)
            ·
              refine ⟨3609256281165412330577933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406170854110274887051955 3609256281165412330577933)
              ·
                refine ⟨1353471105437029623966725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3609256281165412330577933 1353471105437029623966725)
                ·
                  refine ⟨253775832269443054493761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353471105437029623966725 253775832269443054493761)
                  ·
                    rfl

theorem cell22_2224020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_2224020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224020 prefixEnd_2224020 := by exact prefixLift 2224020
  have htrace : WordTrace (prefixWord ++ tailWord_2224020) baseStart_2224020 baseEnd_2224020 := by
    simpa [prefixWord, tailWord_2224020, baseEnd_2224020] using wordTrace_append hprefix tailTrace_2224020
  have hstable : (prefixWord ++ tailWord_2224020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224020).length < 2 ^ (prefixWord ++ tailWord_2224020).sum := by decide
  have hdescent : baseEnd_2224020 < baseStart_2224020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224031 : List Nat := [1, 1, 2, 5, 3, 2, 8]
def baseStart_2224031 : Nat := 118140960795 + 2224031 * 2 ^ 59
def prefixEnd_2224031 : Nat := 4983230072969 + 3 ^ 40 * 2224031 * 2
def baseEnd_2224031 : Nat := 28197454160486251905787

theorem tailTrace_2224031 : CollatzResearch.WordTrace tailWord_2224031 prefixEnd_2224031 28197454160486251905787 := by
  unfold tailWord_2224031
  simp only [CollatzResearch.WordTrace]
  refine ⟨81117074605722996099759947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54078049737148664066506631 81117074605722996099759947)
  ·
    refine ⟨121675611908584494149639921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81117074605722996099759947 121675611908584494149639921)
    ·
      refine ⟨91256708931438370612229941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121675611908584494149639921 91256708931438370612229941)
      ·
        refine ⟨8555316462322347244896557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91256708931438370612229941 8555316462322347244896557)
        ·
          refine ⟨3208243673370880216836209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8555316462322347244896557 3208243673370880216836209)
          ·
            refine ⟨2406182755028160162627157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3208243673370880216836209 2406182755028160162627157)
            ·
              refine ⟨28197454160486251905787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2406182755028160162627157 28197454160486251905787)
              ·
                rfl

theorem cell22_2224031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 8].length) (baseStart_2224031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224031 prefixEnd_2224031 := by exact prefixLift 2224031
  have htrace : WordTrace (prefixWord ++ tailWord_2224031) baseStart_2224031 baseEnd_2224031 := by
    simpa [prefixWord, tailWord_2224031, baseEnd_2224031] using wordTrace_append hprefix tailTrace_2224031
  have hstable : (prefixWord ++ tailWord_2224031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224031).length < 2 ^ (prefixWord ++ tailWord_2224031).sum := by decide
  have hdescent : baseEnd_2224031 < baseStart_2224031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224033 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2224033 : Nat := 118140960795 + 2224033 * 2 ^ 59
def prefixEnd_2224033 : Nat := 4983230072969 + 3 ^ 40 * 2224033 * 2
def baseEnd_2224033 : Nat := 761331946974001462906243

theorem tailTrace_2224033 : CollatzResearch.WordTrace tailWord_2224033 prefixEnd_2224033 761331946974001462906243 := by
  unfold tailWord_2224033
  simp only [CollatzResearch.WordTrace]
  refine ⟨81117147551715750441332753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54078098367810500294221835 81117147551715750441332753)
  ·
    refine ⟨60837860663786812830999565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81117147551715750441332753 60837860663786812830999565)
    ·
      refine ⟨22814197748920054811624837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60837860663786812830999565 22814197748920054811624837)
      ·
        refine ⟨4277662077922510277179657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22814197748920054811624837 4277662077922510277179657)
        ·
          refine ⟨3208246558441882707884743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277662077922510277179657 3208246558441882707884743)
          ·
            refine ⟨4812369837662824061827115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208246558441882707884743 4812369837662824061827115)
            ·
              refine ⟨7218554756494236092740673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812369837662824061827115 7218554756494236092740673)
              ·
                refine ⟨5413916067370677069555505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7218554756494236092740673 5413916067370677069555505)
                ·
                  refine ⟨4060437050528007802166629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5413916067370677069555505 4060437050528007802166629)
                  ·
                    refine ⟨761331946974001462906243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4060437050528007802166629 761331946974001462906243)
                    ·
                      rfl

theorem cell22_2224033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2224033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224033 prefixEnd_2224033 := by exact prefixLift 2224033
  have htrace : WordTrace (prefixWord ++ tailWord_2224033) baseStart_2224033 baseEnd_2224033 := by
    simpa [prefixWord, tailWord_2224033, baseEnd_2224033] using wordTrace_append hprefix tailTrace_2224033
  have hstable : (prefixWord ++ tailWord_2224033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224033).length < 2 ^ (prefixWord ++ tailWord_2224033).sum := by decide
  have hdescent : baseEnd_2224033 < baseStart_2224033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224052 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2224052 : Nat := 118140960795 + 2224052 * 2 ^ 59
def prefixEnd_2224052 : Nat := 4983230072969 + 3 ^ 40 * 2224052 * 2
def baseEnd_2224052 : Nat := 761338451062291746681185

theorem tailTrace_2224052 : CollatzResearch.WordTrace tailWord_2224052 prefixEnd_2224052 761338451062291746681185 := by
  unfold tailWord_2224052
  simp only [CollatzResearch.WordTrace]
  refine ⟨40558920269323458343137205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54078560359097944457516273 40558920269323458343137205)
  ·
    refine ⟨3802398775249074219669113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40558920269323458343137205 3802398775249074219669113)
    ·
      refine ⟨2851799081436805664751835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3802398775249074219669113 2851799081436805664751835)
      ·
        refine ⟨4277698622155208497127753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851799081436805664751835 4277698622155208497127753)
        ·
          refine ⟨3208273966616406372845815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277698622155208497127753 3208273966616406372845815)
          ·
            refine ⟨4812410949924609559268723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208273966616406372845815 4812410949924609559268723)
            ·
              refine ⟨7218616424886914338903085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812410949924609559268723 7218616424886914338903085)
              ·
                refine ⟨2706981159332592877088657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7218616424886914338903085 2706981159332592877088657)
                ·
                  refine ⟨2030235869499444657816493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2706981159332592877088657 2030235869499444657816493)
                  ·
                    refine ⟨761338451062291746681185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030235869499444657816493 761338451062291746681185)
                    ·
                      rfl

theorem cell22_2224052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2224052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224052 prefixEnd_2224052 := by exact prefixLift 2224052
  have htrace : WordTrace (prefixWord ++ tailWord_2224052) baseStart_2224052 baseEnd_2224052 := by
    simpa [prefixWord, tailWord_2224052, baseEnd_2224052] using wordTrace_append hprefix tailTrace_2224052
  have hstable : (prefixWord ++ tailWord_2224052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224052).length < 2 ^ (prefixWord ++ tailWord_2224052).sum := by decide
  have hdescent : baseEnd_2224052 < baseStart_2224052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224106 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2224106 : Nat := 118140960795 + 2224106 * 2 ^ 59
def prefixEnd_2224106 : Nat := 4983230072969 + 3 ^ 40 * 2224106 * 2
def baseEnd_2224106 : Nat := 761356936365853605831019

theorem tailTrace_2224106 : CollatzResearch.WordTrace tailWord_2224106 prefixEnd_2224106 761356936365853605831019 := by
  unfold tailWord_2224106
  simp only [CollatzResearch.WordTrace]
  refine ⟨20279952520112820977185043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54079873386967522605826781 20279952520112820977185043)
  ·
    refine ⟨30419928780169231465777565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20279952520112820977185043 30419928780169231465777565)
    ·
      refine ⟨11407473292563461799666587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30419928780169231465777565 11407473292563461799666587)
      ·
        refine ⟨17111209938845192699499881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11407473292563461799666587 17111209938845192699499881)
        ·
          refine ⟨12833407454133894524624911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17111209938845192699499881 12833407454133894524624911)
          ·
            refine ⟨19250111181200841786937367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12833407454133894524624911 19250111181200841786937367)
            ·
              refine ⟨28875166771801262680406051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19250111181200841786937367 28875166771801262680406051)
              ·
                refine ⟨43312750157701894020609077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28875166771801262680406051 43312750157701894020609077)
                ·
                  refine ⟨4060570327284552564432101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43312750157701894020609077 4060570327284552564432101)
                  ·
                    refine ⟨761356936365853605831019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4060570327284552564432101 761356936365853605831019)
                    ·
                      rfl

theorem cell22_2224106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2224106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224106 prefixEnd_2224106 := by exact prefixLift 2224106
  have htrace : WordTrace (prefixWord ++ tailWord_2224106) baseStart_2224106 baseEnd_2224106 := by
    simpa [prefixWord, tailWord_2224106, baseEnd_2224106] using wordTrace_append hprefix tailTrace_2224106
  have hstable : (prefixWord ++ tailWord_2224106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224106).length < 2 ^ (prefixWord ++ tailWord_2224106).sum := by decide
  have hdescent : baseEnd_2224106 < baseStart_2224106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224121 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 6]
def baseStart_2224121 : Nat := 118140960795 + 2224121 * 2 ^ 59
def prefixEnd_2224121 : Nat := 4983230072969 + 3 ^ 40 * 2224121 * 2
def baseEnd_2224121 : Nat := 253787357057466188901991

theorem tailTrace_2224121 : CollatzResearch.WordTrace tailWord_2224121 prefixEnd_2224121 253787357057466188901991 := by
  unfold tailWord_2224121
  simp only [CollatzResearch.WordTrace]
  refine ⟨81120357175396941470536217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54080238116931294313690811 81120357175396941470536217)
  ·
    refine ⟨60840267881547706102902163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81120357175396941470536217 60840267881547706102902163)
    ·
      refine ⟨91260401822321559154353245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60840267881547706102902163 91260401822321559154353245)
      ·
        refine ⟨34222650683370584682882467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91260401822321559154353245 34222650683370584682882467)
        ·
          refine ⟨51333976025055877024323701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34222650683370584682882467 51333976025055877024323701)
          ·
            refine ⟨4812560252348988471030347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51333976025055877024323701 4812560252348988471030347)
            ·
              refine ⟨7218840378523482706545521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812560252348988471030347 7218840378523482706545521)
              ·
                refine ⟨5414130283892612029909141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7218840378523482706545521 5414130283892612029909141)
                ·
                  refine ⟨253787357057466188901991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5414130283892612029909141 253787357057466188901991)
                  ·
                    rfl

theorem cell22_2224121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_2224121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224121 prefixEnd_2224121 := by exact prefixLift 2224121
  have htrace : WordTrace (prefixWord ++ tailWord_2224121) baseStart_2224121 baseEnd_2224121 := by
    simpa [prefixWord, tailWord_2224121, baseEnd_2224121] using wordTrace_append hprefix tailTrace_2224121
  have hstable : (prefixWord ++ tailWord_2224121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224121).length < 2 ^ (prefixWord ++ tailWord_2224121).sum := by decide
  have hdescent : baseEnd_2224121 < baseStart_2224121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224136 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2224136 : Nat := 118140960795 + 2224136 * 2 ^ 59
def prefixEnd_2224136 : Nat := 4983230072969 + 3 ^ 40 * 2224136 * 2
def baseEnd_2224136 : Nat := 761367205978943527580927

theorem tailTrace_2224136 : CollatzResearch.WordTrace tailWord_2224136 prefixEnd_2224136 761367205978943527580927 := by
  unfold tailWord_2224136
  simp only [CollatzResearch.WordTrace]
  refine ⟨40560452135171299516166131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54080602846895066021554841 40560452135171299516166131)
  ·
    refine ⟨60840678202756949274249197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40560452135171299516166131 60840678202756949274249197)
    ·
      refine ⟨22815254326033855977843449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60840678202756949274249197 22815254326033855977843449)
      ·
        refine ⟨17111440744525391983382587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22815254326033855977843449 17111440744525391983382587)
        ·
          refine ⟨25667161116788087975073881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17111440744525391983382587 25667161116788087975073881)
          ·
            refine ⟨19250370837591065981305411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25667161116788087975073881 19250370837591065981305411)
            ·
              refine ⟨28875556256386598971958117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19250370837591065981305411 28875556256386598971958117)
              ·
                refine ⟨5414166798072487307242147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28875556256386598971958117 5414166798072487307242147)
                ·
                  refine ⟨8121250197108730960863221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5414166798072487307242147 8121250197108730960863221)
                  ·
                    refine ⟨761367205978943527580927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8121250197108730960863221 761367205978943527580927)
                    ·
                      rfl

theorem cell22_2224136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2224136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224136 prefixEnd_2224136 := by exact prefixLift 2224136
  have htrace : WordTrace (prefixWord ++ tailWord_2224136) baseStart_2224136 baseEnd_2224136 := by
    simpa [prefixWord, tailWord_2224136, baseEnd_2224136] using wordTrace_append hprefix tailTrace_2224136
  have hstable : (prefixWord ++ tailWord_2224136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224136).length < 2 ^ (prefixWord ++ tailWord_2224136).sum := by decide
  have hdescent : baseEnd_2224136 < baseStart_2224136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224170 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2224170 : Nat := 118140960795 + 2224170 * 2 ^ 59
def prefixEnd_2224170 : Nat := 4983230072969 + 3 ^ 40 * 2224170 * 2
def baseEnd_2224170 : Nat := 761378844873778772230823

theorem tailTrace_2224170 : CollatzResearch.WordTrace tailWord_2224170 prefixEnd_2224170 761378844873778772230823 := by
  unfold tailWord_2224170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20280536088054855709767491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54081429568146281892713309 20280536088054855709767491)
  ·
    refine ⟨30420804132082283564651237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20280536088054855709767491 30420804132082283564651237)
    ·
      refine ⟨5703900774765428168372107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30420804132082283564651237 5703900774765428168372107)
      ·
        refine ⟨8555851162148142252558161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703900774765428168372107 8555851162148142252558161)
        ·
          refine ⟨6416888371611106689418621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8555851162148142252558161 6416888371611106689418621)
          ·
            refine ⟨2406333139354165008531983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6416888371611106689418621 2406333139354165008531983)
            ·
              refine ⟨3609499709031247512797975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406333139354165008531983 3609499709031247512797975)
              ·
                refine ⟨5414249563546871269196963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3609499709031247512797975 5414249563546871269196963)
                ·
                  refine ⟨8121374345320306903795445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5414249563546871269196963 8121374345320306903795445)
                  ·
                    refine ⟨761378844873778772230823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8121374345320306903795445 761378844873778772230823)
                    ·
                      rfl

theorem cell22_2224170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2224170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224170 prefixEnd_2224170 := by exact prefixLift 2224170
  have htrace : WordTrace (prefixWord ++ tailWord_2224170) baseStart_2224170 baseEnd_2224170 := by
    simpa [prefixWord, tailWord_2224170, baseEnd_2224170] using wordTrace_append hprefix tailTrace_2224170
  have hstable : (prefixWord ++ tailWord_2224170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224170).length < 2 ^ (prefixWord ++ tailWord_2224170).sum := by decide
  have hdescent : baseEnd_2224170 < baseStart_2224170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224215 : List Nat := [1, 1, 3, 2, 2, 1, 2, 6, 1, 3]
def baseStart_2224215 : Nat := 118140960795 + 2224215 * 2 ^ 59
def prefixEnd_2224215 : Nat := 4983230072969 + 3 ^ 40 * 2224215 * 2
def baseEnd_2224215 : Nat := 761394249293413654855685

theorem tailTrace_2224215 : CollatzResearch.WordTrace tailWord_2224215 prefixEnd_2224215 761394249293413654855685 := by
  unfold tailWord_2224215
  simp only [CollatzResearch.WordTrace]
  refine ⟨81123785637056395524458099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54082523758037597016305399 81123785637056395524458099)
  ·
    refine ⟨121685678455584593286687149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81123785637056395524458099 121685678455584593286687149)
    ·
      refine ⟨45632129420844222482507681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121685678455584593286687149 45632129420844222482507681)
      ·
        refine ⟨34224097065633166861880761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45632129420844222482507681 34224097065633166861880761)
        ·
          refine ⟨25668072799224875146410571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34224097065633166861880761 25668072799224875146410571)
          ·
            refine ⟨38502109198837312719615857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25668072799224875146410571 38502109198837312719615857)
            ·
              refine ⟨28876581899127984539711893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38502109198837312719615857 28876581899127984539711893)
              ·
                refine ⟨1353589776521624275298995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28876581899127984539711893 1353589776521624275298995)
                ·
                  refine ⟨2030384664782436412948493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353589776521624275298995 2030384664782436412948493)
                  ·
                    refine ⟨761394249293413654855685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030384664782436412948493 761394249293413654855685)
                    ·
                      rfl

theorem cell22_2224215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_2224215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224215 prefixEnd_2224215 := by exact prefixLift 2224215
  have htrace : WordTrace (prefixWord ++ tailWord_2224215) baseStart_2224215 baseEnd_2224215 := by
    simpa [prefixWord, tailWord_2224215, baseEnd_2224215] using wordTrace_append hprefix tailTrace_2224215
  have hstable : (prefixWord ++ tailWord_2224215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224215).length < 2 ^ (prefixWord ++ tailWord_2224215).sum := by decide
  have hdescent : baseEnd_2224215 < baseStart_2224215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224288 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_2224288 : Nat := 118140960795 + 2224288 * 2 ^ 59
def prefixEnd_2224288 : Nat := 4983230072969 + 3 ^ 40 * 2224288 * 2
def baseEnd_2224288 : Nat := 761419238685265797780461

theorem tailTrace_2224288 : CollatzResearch.WordTrace tailWord_2224288 prefixEnd_2224288 761419238685265797780461 := by
  unfold tailWord_2224288
  simp only [CollatzResearch.WordTrace]
  refine ⟨40563224082895964495932759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54084298777194619327910345 40563224082895964495932759)
  ·
    refine ⟨60844836124343946743899139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40563224082895964495932759 60844836124343946743899139)
    ·
      refine ⟨91267254186515920115848709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60844836124343946743899139 91267254186515920115848709)
      ·
        refine ⟨17112610159971735021721633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91267254186515920115848709 17112610159971735021721633)
        ·
          refine ⟨12834457619978801266291225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17112610159971735021721633 12834457619978801266291225)
          ·
            refine ⟨9625843214984100949718419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12834457619978801266291225 9625843214984100949718419)
            ·
              refine ⟨14438764822476151424577629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9625843214984100949718419 14438764822476151424577629)
              ·
                refine ⟨5414536808428556784216611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14438764822476151424577629 5414536808428556784216611)
                ·
                  refine ⟨8121805212642835176324917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5414536808428556784216611 8121805212642835176324917)
                  ·
                    refine ⟨761419238685265797780461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8121805212642835176324917 761419238685265797780461)
                    ·
                      rfl

theorem cell22_2224288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_2224288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224288 prefixEnd_2224288 := by exact prefixLift 2224288
  have htrace : WordTrace (prefixWord ++ tailWord_2224288) baseStart_2224288 baseEnd_2224288 := by
    simpa [prefixWord, tailWord_2224288, baseEnd_2224288] using wordTrace_append hprefix tailTrace_2224288
  have hstable : (prefixWord ++ tailWord_2224288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224288).length < 2 ^ (prefixWord ++ tailWord_2224288).sum := by decide
  have hdescent : baseEnd_2224288 < baseStart_2224288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224290 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_2224290 : Nat := 118140960795 + 2224290 * 2 ^ 59
def prefixEnd_2224290 : Nat := 4983230072969 + 3 ^ 40 * 2224290 * 2
def baseEnd_2224290 : Nat := 253806641108712819743485

theorem tailTrace_2224290 : CollatzResearch.WordTrace tailWord_2224290 prefixEnd_2224290 253806641108712819743485 := by
  unfold tailWord_2224290
  simp only [CollatzResearch.WordTrace]
  refine ⟨20281630277946170833359581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54084347407856455555625549 20281630277946170833359581)
  ·
    refine ⟨7605611354229814062509843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20281630277946170833359581 7605611354229814062509843)
    ·
      refine ⟨11408417031344721093764765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7605611354229814062509843 11408417031344721093764765)
      ·
        refine ⟨4278156386754270410161787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11408417031344721093764765 4278156386754270410161787)
        ·
          refine ⟨6417234580131405615242681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278156386754270410161787 6417234580131405615242681)
          ·
            refine ⟨4812925935098554211432011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6417234580131405615242681 4812925935098554211432011)
            ·
              refine ⟨7219388902647831317148017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812925935098554211432011 7219388902647831317148017)
              ·
                refine ⟨5414541676985873487861013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7219388902647831317148017 5414541676985873487861013)
                ·
                  refine ⟨253806641108712819743485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5414541676985873487861013 253806641108712819743485)
                  ·
                    rfl

theorem cell22_2224290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_2224290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224290 prefixEnd_2224290 := by exact prefixLift 2224290
  have htrace : WordTrace (prefixWord ++ tailWord_2224290) baseStart_2224290 baseEnd_2224290 := by
    simpa [prefixWord, tailWord_2224290, baseEnd_2224290] using wordTrace_append hprefix tailTrace_2224290
  have hstable : (prefixWord ++ tailWord_2224290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224290).length < 2 ^ (prefixWord ++ tailWord_2224290).sum := by decide
  have hdescent : baseEnd_2224290 < baseStart_2224290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224408 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 8]
def baseStart_2224408 : Nat := 118140960795 + 2224408 * 2 ^ 59
def prefixEnd_2224408 : Nat := 4983230072969 + 3 ^ 40 * 2224408 * 2
def baseEnd_2224408 : Nat := 253820105712541828260031

theorem tailTrace_2224408 : CollatzResearch.WordTrace tailWord_2224408 prefixEnd_2224408 253820105712541828260031 := by
  unfold tailWord_2224408
  simp only [CollatzResearch.WordTrace]
  refine ⟨40565412462678594743116939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54087216616904792990822585 40565412462678594743116939)
  ·
    refine ⟨60848118694017892114675409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40565412462678594743116939 60848118694017892114675409)
    ·
      refine ⟨45636089020513419086006557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60848118694017892114675409 45636089020513419086006557)
      ·
        refine ⟨17113533382692532157252459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45636089020513419086006557 17113533382692532157252459)
        ·
          refine ⟨25670300074038798235878689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17113533382692532157252459 25670300074038798235878689)
          ·
            refine ⟨19252725055529098676909017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25670300074038798235878689 19252725055529098676909017)
            ·
              refine ⟨14439543791646824007681763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19252725055529098676909017 14439543791646824007681763)
              ·
                refine ⟨21659315687470236011522645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14439543791646824007681763 21659315687470236011522645)
                ·
                  refine ⟨253820105712541828260031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21659315687470236011522645 253820105712541828260031)
                  ·
                    rfl

theorem cell22_2224408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_2224408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224408 prefixEnd_2224408 := by exact prefixLift 2224408
  have htrace : WordTrace (prefixWord ++ tailWord_2224408) baseStart_2224408 baseEnd_2224408 := by
    simpa [prefixWord, tailWord_2224408, baseEnd_2224408] using wordTrace_append hprefix tailTrace_2224408
  have hstable : (prefixWord ++ tailWord_2224408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224408).length < 2 ^ (prefixWord ++ tailWord_2224408).sum := by decide
  have hdescent : baseEnd_2224408 < baseStart_2224408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224440 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 4, 3]
def baseStart_2224440 : Nat := 118140960795 + 2224440 * 2 ^ 59
def prefixEnd_2224440 : Nat := 4983230072969 + 3 ^ 40 * 2224440 * 2
def baseEnd_2224440 : Nat := 761471271391588067979995

theorem tailTrace_2224440 : CollatzResearch.WordTrace tailWord_2224440 prefixEnd_2224440 761471271391588067979995 := by
  unfold tailWord_2224440
  simp only [CollatzResearch.WordTrace]
  refine ⟨40565996030620629475699387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54087994707494172634265849 40565996030620629475699387)
  ·
    refine ⟨60848994045930944213549081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40565996030620629475699387 60848994045930944213549081)
    ·
      refine ⟨45636745534448208160161811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60848994045930944213549081 45636745534448208160161811)
      ·
        refine ⟨68455118301672312240242717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45636745534448208160161811 68455118301672312240242717)
        ·
          refine ⟨25670669363127117090091019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68455118301672312240242717 25670669363127117090091019)
          ·
            refine ⟨38506004044690675635136529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25670669363127117090091019 38506004044690675635136529)
            ·
              refine ⟨28879503033518006726352397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38506004044690675635136529 28879503033518006726352397)
              ·
                refine ⟨10829813637569252522382149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28879503033518006726352397 10829813637569252522382149)
                ·
                  refine ⟨2030590057044234847946653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10829813637569252522382149 2030590057044234847946653)
                  ·
                    refine ⟨761471271391588067979995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030590057044234847946653 761471271391588067979995)
                    ·
                      rfl

theorem cell22_2224440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_2224440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224440 prefixEnd_2224440 := by exact prefixLift 2224440
  have htrace : WordTrace (prefixWord ++ tailWord_2224440) baseStart_2224440 baseEnd_2224440 := by
    simpa [prefixWord, tailWord_2224440, baseEnd_2224440] using wordTrace_append hprefix tailTrace_2224440
  have hstable : (prefixWord ++ tailWord_2224440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224440).length < 2 ^ (prefixWord ++ tailWord_2224440).sum := by decide
  have hdescent : baseEnd_2224440 < baseStart_2224440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224442 : List Nat := [3, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_2224442 : Nat := 118140960795 + 2224442 * 2 ^ 59
def prefixEnd_2224442 : Nat := 4983230072969 + 3 ^ 40 * 2224442 * 2
def baseEnd_2224442 : Nat := 253823985344153576476663

theorem tailTrace_2224442 : CollatzResearch.WordTrace tailWord_2224442 prefixEnd_2224442 253823985344153576476663 := by
  unfold tailWord_2224442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20283016251808503323242895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54088043338156008861981053 20283016251808503323242895)
  ·
    refine ⟨30424524377712754984864343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20283016251808503323242895 30424524377712754984864343)
    ·
      refine ⟨45636786566569132477296515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30424524377712754984864343 45636786566569132477296515)
      ·
        refine ⟨68455179849853698715944773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45636786566569132477296515 68455179849853698715944773)
        ·
          refine ⟨12835346221847568509239645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68455179849853698715944773 12835346221847568509239645)
          ·
            refine ⟨4813254833192838190964867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12835346221847568509239645 4813254833192838190964867)
            ·
              refine ⟨7219882249789257286447301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4813254833192838190964867 7219882249789257286447301)
              ·
                refine ⟨1353727921835485741208869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7219882249789257286447301 1353727921835485741208869)
                ·
                  refine ⟨253823985344153576476663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353727921835485741208869 253823985344153576476663)
                  ·
                    rfl

theorem cell22_2224442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_2224442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224442 prefixEnd_2224442 := by exact prefixLift 2224442
  have htrace : WordTrace (prefixWord ++ tailWord_2224442) baseStart_2224442 baseEnd_2224442 := by
    simpa [prefixWord, tailWord_2224442, baseEnd_2224442] using wordTrace_append hprefix tailTrace_2224442
  have hstable : (prefixWord ++ tailWord_2224442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224442).length < 2 ^ (prefixWord ++ tailWord_2224442).sum := by decide
  have hdescent : baseEnd_2224442 < baseStart_2224442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224476 : List Nat := [2, 2, 4, 3, 1, 1, 2, 3, 4]
def baseStart_2224476 : Nat := 118140960795 + 2224476 * 2 ^ 59
def prefixEnd_2224476 : Nat := 4983230072969 + 3 ^ 40 * 2224476 * 2
def baseEnd_2224476 : Nat := 253827864975765324693295

theorem tailTrace_2224476 : CollatzResearch.WordTrace tailWord_2224476 prefixEnd_2224476 253827864975765324693295 := by
  unfold tailWord_2224476
  simp only [CollatzResearch.WordTrace]
  refine ⟨40566652544555418549854641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54088870059407224733139521 40566652544555418549854641)
  ·
    refine ⟨30424989408416563912390981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40566652544555418549854641 30424989408416563912390981)
    ·
      refine ⟨5704685514078105733573309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30424989408416563912390981 5704685514078105733573309)
      ·
        refine ⟨2139257067779289650089991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5704685514078105733573309 2139257067779289650089991)
        ·
          refine ⟨3208885601668934475134987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139257067779289650089991 3208885601668934475134987)
          ·
            refine ⟨4813328402503401712702481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208885601668934475134987 4813328402503401712702481)
            ·
              refine ⟨3609996301877551284526861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4813328402503401712702481 3609996301877551284526861)
              ·
                refine ⟨1353748613204081731697573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3609996301877551284526861 1353748613204081731697573)
                ·
                  refine ⟨253827864975765324693295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353748613204081731697573 253827864975765324693295)
                  ·
                    rfl

theorem cell22_2224476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_2224476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224476 prefixEnd_2224476 := by exact prefixLift 2224476
  have htrace : WordTrace (prefixWord ++ tailWord_2224476) baseStart_2224476 baseEnd_2224476 := by
    simpa [prefixWord, tailWord_2224476, baseEnd_2224476] using wordTrace_append hprefix tailTrace_2224476
  have hstable : (prefixWord ++ tailWord_2224476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224476).length < 2 ^ (prefixWord ++ tailWord_2224476).sum := by decide
  have hdescent : baseEnd_2224476 < baseStart_2224476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224536 : List Nat := [2, 1, 2, 5, 1, 1, 3, 3, 1, 3]
def baseStart_2224536 : Nat := 118140960795 + 2224536 * 2 ^ 59
def prefixEnd_2224536 : Nat := 4983230072969 + 3 ^ 40 * 2224536 * 2
def baseEnd_2224536 : Nat := 761504134153475817579701

theorem tailTrace_2224536 : CollatzResearch.WordTrace tailWord_2224536 prefixEnd_2224536 761504134153475817579701 := by
  unfold tailWord_2224536
  simp only [CollatzResearch.WordTrace]
  refine ⟨40567746734446733673446731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54090328979262311564595641 40567746734446733673446731)
  ·
    refine ⟨60851620101670100510170097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40567746734446733673446731 60851620101670100510170097)
    ·
      refine ⟨45638715076252575382627573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60851620101670100510170097 45638715076252575382627573)
      ·
        refine ⟨4278629538398678942121335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45638715076252575382627573 4278629538398678942121335)
        ·
          refine ⟨6417944307598018413182003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278629538398678942121335 6417944307598018413182003)
          ·
            refine ⟨9626916461397027619773005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417944307598018413182003 9626916461397027619773005)
            ·
              refine ⟨3610093673023885357414877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9626916461397027619773005 3610093673023885357414877)
              ·
                refine ⟨1353785127383957009030579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3610093673023885357414877 1353785127383957009030579)
                ·
                  refine ⟨2030677691075935513545869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1353785127383957009030579 2030677691075935513545869)
                  ·
                    refine ⟨761504134153475817579701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030677691075935513545869 761504134153475817579701)
                    ·
                      rfl

theorem cell22_2224536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_2224536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224536 prefixEnd_2224536 := by exact prefixLift 2224536
  have htrace : WordTrace (prefixWord ++ tailWord_2224536) baseStart_2224536 baseEnd_2224536 := by
    simpa [prefixWord, tailWord_2224536, baseEnd_2224536] using wordTrace_append hprefix tailTrace_2224536
  have hstable : (prefixWord ++ tailWord_2224536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224536).length < 2 ^ (prefixWord ++ tailWord_2224536).sum := by decide
  have hdescent : baseEnd_2224536 < baseStart_2224536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224596 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2224596 : Nat := 118140960795 + 2224596 * 2 ^ 59
def prefixEnd_2224596 : Nat := 4983230072969 + 3 ^ 40 * 2224596 * 2
def baseEnd_2224596 : Nat := 761524673379655661079517

theorem tailTrace_2224596 : CollatzResearch.WordTrace tailWord_2224596 prefixEnd_2224596 761524673379655661079517 := by
  unfold tailWord_2224596
  simp only [CollatzResearch.WordTrace]
  refine ⟨40568840924338048797038821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54091787899117398396051761 40568840924338048797038821)
  ·
    refine ⟨7606657673313384149444779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40568840924338048797038821 7606657673313384149444779)
    ·
      refine ⟨11409986509970076224167169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7606657673313384149444779 11409986509970076224167169)
      ·
        refine ⟨8557489882477557168125377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11409986509970076224167169 8557489882477557168125377)
        ·
          refine ⟨6418117411858167876094033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8557489882477557168125377 6418117411858167876094033)
          ·
            refine ⟨4813588058893625907070525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6418117411858167876094033 4813588058893625907070525)
            ·
              refine ⟨1805095522085109715151447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4813588058893625907070525 1805095522085109715151447)
              ·
                refine ⟨2707643283127664572727171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805095522085109715151447 2707643283127664572727171)
                ·
                  refine ⟨4061464924691496859090757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707643283127664572727171 4061464924691496859090757)
                  ·
                    refine ⟨761524673379655661079517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061464924691496859090757 761524673379655661079517)
                    ·
                      rfl

theorem cell22_2224596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2224596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224596 prefixEnd_2224596 := by exact prefixLift 2224596
  have htrace : WordTrace (prefixWord ++ tailWord_2224596) baseStart_2224596 baseEnd_2224596 := by
    simpa [prefixWord, tailWord_2224596, baseEnd_2224596] using wordTrace_append hprefix tailTrace_2224596
  have hstable : (prefixWord ++ tailWord_2224596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224596).length < 2 ^ (prefixWord ++ tailWord_2224596).sum := by decide
  have hdescent : baseEnd_2224596 < baseStart_2224596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224607 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 2, 4]
def baseStart_2224607 : Nat := 118140960795 + 2224607 * 2 ^ 59
def prefixEnd_2224607 : Nat := 4983230072969 + 3 ^ 40 * 2224607 * 2
def baseEnd_2224607 : Nat := 761528438904455299054483

theorem tailTrace_2224607 : CollatzResearch.WordTrace tailWord_2224607 prefixEnd_2224607 761528438904455299054483 := by
  unfold tailWord_2224607
  simp only [CollatzResearch.WordTrace]
  refine ⟨81138083051636246472728075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54092055367757497648485383 81138083051636246472728075)
  ·
    refine ⟨121707124577454369709092113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81138083051636246472728075 121707124577454369709092113)
    ·
      refine ⟨91280343433090777281819085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121707124577454369709092113 91280343433090777281819085)
      ·
        refine ⟨34230128787409041480682157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91280343433090777281819085 34230128787409041480682157)
        ·
          refine ⟨12836298295278390555255809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34230128787409041480682157 12836298295278390555255809)
          ·
            refine ⟨9627223721458792916441857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12836298295278390555255809 9627223721458792916441857)
            ·
              refine ⟨7220417791094094687331393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9627223721458792916441857 7220417791094094687331393)
              ·
                refine ⟨5415313343320571015498545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7220417791094094687331393 5415313343320571015498545)
                ·
                  refine ⟨4061485007490428261623909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5415313343320571015498545 4061485007490428261623909)
                  ·
                    refine ⟨761528438904455299054483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061485007490428261623909 761528438904455299054483)
                    ·
                      rfl

theorem cell22_2224607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_2224607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224607 prefixEnd_2224607 := by exact prefixLift 2224607
  have htrace : WordTrace (prefixWord ++ tailWord_2224607) baseStart_2224607 baseEnd_2224607 := by
    simpa [prefixWord, tailWord_2224607, baseEnd_2224607] using wordTrace_append hprefix tailTrace_2224607
  have hstable : (prefixWord ++ tailWord_2224607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224607).length < 2 ^ (prefixWord ++ tailWord_2224607).sum := by decide
  have hdescent : baseEnd_2224607 < baseStart_2224607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224609 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 2, 3]
def baseStart_2224609 : Nat := 118140960795 + 2224609 * 2 ^ 59
def prefixEnd_2224609 : Nat := 4983230072969 + 3 ^ 40 * 2224609 * 2
def baseEnd_2224609 : Nat := 761529123545327960504477

theorem tailTrace_2224609 : CollatzResearch.WordTrace tailWord_2224609 prefixEnd_2224609 761529123545327960504477 := by
  unfold tailWord_2224609
  simp only [CollatzResearch.WordTrace]
  refine ⟨81138155997629000814300881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54092103998419333876200587 81138155997629000814300881)
  ·
    refine ⟨60853616998221750610725661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81138155997629000814300881 60853616998221750610725661)
    ·
      refine ⟨22820106374333156479022123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60853616998221750610725661 22820106374333156479022123)
      ·
        refine ⟨34230159561499734718533185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22820106374333156479022123 34230159561499734718533185)
        ·
          refine ⟨25672619671124801038899889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34230159561499734718533185 25672619671124801038899889)
          ·
            refine ⟨19254464753343600779174917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25672619671124801038899889 19254464753343600779174917)
            ·
              refine ⟨3610212141251925146095297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19254464753343600779174917 3610212141251925146095297)
              ·
                refine ⟨2707659105938943859571473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610212141251925146095297 2707659105938943859571473)
                ·
                  refine ⟨2030744329454207894678605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2707659105938943859571473 2030744329454207894678605)
                  ·
                    refine ⟨761529123545327960504477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030744329454207894678605 761529123545327960504477)
                    ·
                      rfl

theorem cell22_2224609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_2224609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224609 prefixEnd_2224609 := by exact prefixLift 2224609
  have htrace : WordTrace (prefixWord ++ tailWord_2224609) baseStart_2224609 baseEnd_2224609 := by
    simpa [prefixWord, tailWord_2224609, baseEnd_2224609] using wordTrace_append hprefix tailTrace_2224609
  have hstable : (prefixWord ++ tailWord_2224609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224609).length < 2 ^ (prefixWord ++ tailWord_2224609).sum := by decide
  have hdescent : baseEnd_2224609 < baseStart_2224609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224622 : List Nat := [4, 1, 2, 1, 2, 2, 3, 7]
def baseStart_2224622 : Nat := 118140960795 + 2224622 * 2 ^ 59
def prefixEnd_2224622 : Nat := 4983230072969 + 3 ^ 40 * 2224622 * 2
def baseEnd_2224622 : Nat := 84614841523444473325493

theorem tailTrace_2224622 : CollatzResearch.WordTrace tailWord_2224622 prefixEnd_2224622 84614841523444473325493 := by
  unfold tailWord_2224622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10142328768322738004315515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54092420097721269356349413 10142328768322738004315515)
  ·
    refine ⟨15213493152484107006473273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10142328768322738004315515 15213493152484107006473273)
    ·
      refine ⟨11410119864363080254854955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15213493152484107006473273 11410119864363080254854955)
      ·
        refine ⟨17115179796544620382282433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11410119864363080254854955 17115179796544620382282433)
        ·
          refine ⟨12836384847408465286711825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17115179796544620382282433 12836384847408465286711825)
          ·
            refine ⟨9627288635556348965033869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12836384847408465286711825 9627288635556348965033869)
            ·
              refine ⟨3610233238333630861887701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9627288635556348965033869 3610233238333630861887701)
              ·
                refine ⟨84614841523444473325493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3610233238333630861887701 84614841523444473325493)
                ·
                  rfl

theorem cell22_2224622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_2224622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224622 prefixEnd_2224622 := by exact prefixLift 2224622
  have htrace : WordTrace (prefixWord ++ tailWord_2224622) baseStart_2224622 baseEnd_2224622 := by
    simpa [prefixWord, tailWord_2224622, baseEnd_2224622] using wordTrace_append hprefix tailTrace_2224622
  have hstable : (prefixWord ++ tailWord_2224622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224622).length < 2 ^ (prefixWord ++ tailWord_2224622).sum := by decide
  have hdescent : baseEnd_2224622 < baseStart_2224622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224665 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_2224665 : Nat := 118140960795 + 2224665 * 2 ^ 59
def prefixEnd_2224665 : Nat := 4983230072969 + 3 ^ 40 * 2224665 * 2
def baseEnd_2224665 : Nat := 761548293489762481104305

theorem tailTrace_2224665 : CollatzResearch.WordTrace tailWord_2224665 prefixEnd_2224665 761548293489762481104305 := by
  unfold tailWord_2224665
  simp only [CollatzResearch.WordTrace]
  refine ⟨81140198485426122378339449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54093465656950748252226299 81140198485426122378339449)
  ·
    refine ⟨60855148864069591783754587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81140198485426122378339449 60855148864069591783754587)
    ·
      refine ⟨91282723296104387675631881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60855148864069591783754587 91282723296104387675631881)
      ·
        refine ⟨68462042472078290756723911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91282723296104387675631881 68462042472078290756723911)
        ·
          refine ⟨102693063708117436135085867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68462042472078290756723911 102693063708117436135085867)
          ·
            refine ⟨154039595562176154202628801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102693063708117436135085867 154039595562176154202628801)
            ·
              refine ⟨115529696671632115651971601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154039595562176154202628801 115529696671632115651971601)
              ·
                refine ⟨86647272503724086738978701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115529696671632115651971601 86647272503724086738978701)
                ·
                  refine ⟨32492727188896532527117013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86647272503724086738978701 32492727188896532527117013)
                  ·
                    refine ⟨761548293489762481104305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32492727188896532527117013 761548293489762481104305)
                    ·
                      rfl

theorem cell22_2224665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_2224665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224665 prefixEnd_2224665 := by exact prefixLift 2224665
  have htrace : WordTrace (prefixWord ++ tailWord_2224665) baseStart_2224665 baseEnd_2224665 := by
    simpa [prefixWord, tailWord_2224665, baseEnd_2224665] using wordTrace_append hprefix tailTrace_2224665
  have hstable : (prefixWord ++ tailWord_2224665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224665).length < 2 ^ (prefixWord ++ tailWord_2224665).sum := by decide
  have hdescent : baseEnd_2224665 < baseStart_2224665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224714 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_2224714 : Nat := 118140960795 + 2224714 * 2 ^ 59
def prefixEnd_2224714 : Nat := 4983230072969 + 3 ^ 40 * 2224714 * 2
def baseEnd_2224714 : Nat := 761565067191142686629155

theorem tailTrace_2224714 : CollatzResearch.WordTrace tailWord_2224714 prefixEnd_2224714 761565067191142686629155 := by
  unfold tailWord_2224714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20285496415562150936718299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54094657108165735831248797 20285496415562150936718299)
  ·
    refine ⟨30428244623343226405077449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20285496415562150936718299 30428244623343226405077449)
    ·
      refine ⟨22821183467507419803808087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30428244623343226405077449 22821183467507419803808087)
      ·
        refine ⟨34231775201261129705712131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22821183467507419803808087 34231775201261129705712131)
        ·
          refine ⟨51347662801891694558568197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34231775201261129705712131 51347662801891694558568197)
          ·
            refine ⟨9627686775354692729731537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51347662801891694558568197 9627686775354692729731537)
            ·
              refine ⟨7220765081516019547298653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9627686775354692729731537 7220765081516019547298653)
              ·
                refine ⟨2707786905568507330236995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7220765081516019547298653 2707786905568507330236995)
                ·
                  refine ⟨4061680358352760995355493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2707786905568507330236995 4061680358352760995355493)
                  ·
                    refine ⟨761565067191142686629155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061680358352760995355493 761565067191142686629155)
                    ·
                      rfl

theorem cell22_2224714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_2224714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224714 prefixEnd_2224714 := by exact prefixLift 2224714
  have htrace : WordTrace (prefixWord ++ tailWord_2224714) baseStart_2224714 baseEnd_2224714 := by
    simpa [prefixWord, tailWord_2224714, baseEnd_2224714] using wordTrace_append hprefix tailTrace_2224714
  have hstable : (prefixWord ++ tailWord_2224714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224714).length < 2 ^ (prefixWord ++ tailWord_2224714).sum := by decide
  have hdescent : baseEnd_2224714 < baseStart_2224714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224778 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_2224778 : Nat := 118140960795 + 2224778 * 2 ^ 59
def prefixEnd_2224778 : Nat := 4983230072969 + 3 ^ 40 * 2224778 * 2
def baseEnd_2224778 : Nat := 761586975699067853028959

theorem tailTrace_2224778 : CollatzResearch.WordTrace tailWord_2224778 prefixEnd_2224778 761586975699067853028959 := by
  unfold tailWord_2224778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20286079983504185669300747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54096213289344495118135325 20286079983504185669300747)
  ·
    refine ⟨30429119975256278503951121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20286079983504185669300747 30429119975256278503951121)
    ·
      refine ⟨22821839981442208877963341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30429119975256278503951121 22821839981442208877963341)
      ·
        refine ⟨8558189993040828329236253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22821839981442208877963341 8558189993040828329236253)
        ·
          refine ⟨3209321247390310623463595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8558189993040828329236253 3209321247390310623463595)
          ·
            refine ⟨4813981871085465935195393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209321247390310623463595 4813981871085465935195393)
            ·
              refine ⟨3610486403314099451396545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4813981871085465935195393 3610486403314099451396545)
              ·
                refine ⟨2707864802485574588547409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610486403314099451396545 2707864802485574588547409)
                ·
                  refine ⟨2030898601864180941410557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2707864802485574588547409 2030898601864180941410557)
                  ·
                    refine ⟨761586975699067853028959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2030898601864180941410557 761586975699067853028959)
                    ·
                      rfl

theorem cell22_2224778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_2224778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224778 prefixEnd_2224778 := by exact prefixLift 2224778
  have htrace : WordTrace (prefixWord ++ tailWord_2224778) baseStart_2224778 baseEnd_2224778 := by
    simpa [prefixWord, tailWord_2224778, baseEnd_2224778] using wordTrace_append hprefix tailTrace_2224778
  have hstable : (prefixWord ++ tailWord_2224778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224778).length < 2 ^ (prefixWord ++ tailWord_2224778).sum := by decide
  have hdescent : baseEnd_2224778 < baseStart_2224778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224810 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2224810 : Nat := 118140960795 + 2224810 * 2 ^ 59
def prefixEnd_2224810 : Nat := 4983230072969 + 3 ^ 40 * 2224810 * 2
def baseEnd_2224810 : Nat := 761597929953030436228861

theorem tailTrace_2224810 : CollatzResearch.WordTrace tailWord_2224810 prefixEnd_2224810 761597929953030436228861 := by
  unfold tailWord_2224810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20286371767475203035591971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54096991379933874761578589 20286371767475203035591971)
  ·
    refine ⟨30429557651212804553387957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20286371767475203035591971 30429557651212804553387957)
    ·
      refine ⟨2852771029801200426880121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30429557651212804553387957 2852771029801200426880121)
      ·
        refine ⟨2139578272350900320160091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2852771029801200426880121 2139578272350900320160091)
        ·
          refine ⟨3209367408526350480240137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139578272350900320160091 3209367408526350480240137)
          ·
            refine ⟨2407025556394762860180103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3209367408526350480240137 2407025556394762860180103)
            ·
              refine ⟨3610538334592144290270155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407025556394762860180103 3610538334592144290270155)
              ·
                refine ⟨5415807501888216435405233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610538334592144290270155 5415807501888216435405233)
                ·
                  refine ⟨4061855626416162326553925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5415807501888216435405233 4061855626416162326553925)
                  ·
                    refine ⟨761597929953030436228861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4061855626416162326553925 761597929953030436228861)
                    ·
                      rfl

theorem cell22_2224810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2224810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224810 prefixEnd_2224810 := by exact prefixLift 2224810
  have htrace : WordTrace (prefixWord ++ tailWord_2224810) baseStart_2224810 baseEnd_2224810 := by
    simpa [prefixWord, tailWord_2224810, baseEnd_2224810] using wordTrace_append hprefix tailTrace_2224810
  have hstable : (prefixWord ++ tailWord_2224810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224810).length < 2 ^ (prefixWord ++ tailWord_2224810).sum := by decide
  have hdescent : baseEnd_2224810 < baseStart_2224810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224836 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 5]
def baseStart_2224836 : Nat := 118140960795 + 2224836 * 2 ^ 59
def prefixEnd_2224836 : Nat := 4983230072969 + 3 ^ 40 * 2224836 * 2
def baseEnd_2224836 : Nat := 253868943428125011692927

theorem tailTrace_2224836 : CollatzResearch.WordTrace tailWord_2224836 prefixEnd_2224836 253868943428125011692927 := by
  unfold tailWord_2224836
  simp only [CollatzResearch.WordTrace]
  refine ⟨40573217683903309291407181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54097623578537745721876241 40573217683903309291407181)
  ·
    refine ⟨15214956631463740984277693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40573217683903309291407181 15214956631463740984277693)
    ·
      refine ⟨5705608736798902869104135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15214956631463740984277693 5705608736798902869104135)
      ·
        refine ⟨8558413105198354303656203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5705608736798902869104135 8558413105198354303656203)
        ·
          refine ⟨12837619657797531455484305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558413105198354303656203 12837619657797531455484305)
          ·
            refine ⟨9628214743348148591613229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12837619657797531455484305 9628214743348148591613229)
            ·
              refine ⟨3610580528755555721854961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9628214743348148591613229 3610580528755555721854961)
              ·
                refine ⟨2707935396566666791391221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610580528755555721854961 2707935396566666791391221)
                ·
                  refine ⟨253868943428125011692927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2707935396566666791391221 253868943428125011692927)
                  ·
                    rfl

theorem cell22_2224836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_2224836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224836 prefixEnd_2224836 := by exact prefixLift 2224836
  have htrace : WordTrace (prefixWord ++ tailWord_2224836) baseStart_2224836 baseEnd_2224836 := by
    simpa [prefixWord, tailWord_2224836, baseEnd_2224836] using wordTrace_append hprefix tailTrace_2224836
  have hstable : (prefixWord ++ tailWord_2224836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224836).length < 2 ^ (prefixWord ++ tailWord_2224836).sum := by decide
  have hdescent : baseEnd_2224836 < baseStart_2224836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224898 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2224898 : Nat := 118140960795 + 2224898 * 2 ^ 59
def prefixEnd_2224898 : Nat := 4983230072969 + 3 ^ 40 * 2224898 * 2
def baseEnd_2224898 : Nat := 253876018050475846676197

theorem tailTrace_2224898 : CollatzResearch.WordTrace tailWord_2224898 prefixEnd_2224898 253876018050475846676197 := by
  unfold tailWord_2224898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20287174173395500792892837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54099131129054668781047565 20287174173395500792892837)
  ·
    refine ⟨3803845157511656398667407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20287174173395500792892837 3803845157511656398667407)
    ·
      refine ⟨5705767736267484598001111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3803845157511656398667407 5705767736267484598001111)
      ·
        refine ⟨8558651604401226897001667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5705767736267484598001111 8558651604401226897001667)
        ·
          refine ⟨12837977406601840345502501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558651604401226897001667 12837977406601840345502501)
          ·
            refine ⟨2407120763737845064781719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12837977406601840345502501 2407120763737845064781719)
            ·
              refine ⟨3610681145606767597172579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407120763737845064781719 3610681145606767597172579)
              ·
                refine ⟨5416021718410151395758869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610681145606767597172579 5416021718410151395758869)
                ·
                  refine ⟨253876018050475846676197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5416021718410151395758869 253876018050475846676197)
                  ·
                    rfl

theorem cell22_2224898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2224898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224898 prefixEnd_2224898 := by exact prefixLift 2224898
  have htrace : WordTrace (prefixWord ++ tailWord_2224898) baseStart_2224898 baseEnd_2224898 := by
    simpa [prefixWord, tailWord_2224898, baseEnd_2224898] using wordTrace_append hprefix tailTrace_2224898
  have hstable : (prefixWord ++ tailWord_2224898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224898).length < 2 ^ (prefixWord ++ tailWord_2224898).sum := by decide
  have hdescent : baseEnd_2224898 < baseStart_2224898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224913 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 2, 3]
def baseStart_2224913 : Nat := 118140960795 + 2224913 * 2 ^ 59
def prefixEnd_2224913 : Nat := 4983230072969 + 3 ^ 40 * 2224913 * 2
def baseEnd_2224913 : Nat := 761633188957972500903545

theorem tailTrace_2224913 : CollatzResearch.WordTrace tailWord_2224913 prefixEnd_2224913 761633188957972500903545 := by
  unfold tailWord_2224913
  simp only [CollatzResearch.WordTrace]
  refine ⟨81149243788527660733367393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54099495859018440488911595 81149243788527660733367393)
  ·
    refine ⟨60861932841395745550025545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81149243788527660733367393 60861932841395745550025545)
    ·
      refine ⟨45646449631046809162519159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60861932841395745550025545 45646449631046809162519159)
      ·
        refine ⟨68469674446570213743778739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45646449631046809162519159 68469674446570213743778739)
        ·
          refine ⟨102704511669855320615668109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68469674446570213743778739 102704511669855320615668109)
          ·
            refine ⟨38514191876195745230875541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102704511669855320615668109 38514191876195745230875541)
            ·
              refine ⟨1805352744196675557697291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38514191876195745230875541 1805352744196675557697291)
              ·
                refine ⟨2708029116295013336545937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805352744196675557697291 2708029116295013336545937)
                ·
                  refine ⟨2031021837221260002409453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2708029116295013336545937 2031021837221260002409453)
                  ·
                    refine ⟨761633188957972500903545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031021837221260002409453 761633188957972500903545)
                    ·
                      rfl

theorem cell22_2224913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_2224913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224913 prefixEnd_2224913 := by exact prefixLift 2224913
  have htrace : WordTrace (prefixWord ++ tailWord_2224913) baseStart_2224913 baseEnd_2224913 := by
    simpa [prefixWord, tailWord_2224913, baseEnd_2224913] using wordTrace_append hprefix tailTrace_2224913
  have hstable : (prefixWord ++ tailWord_2224913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224913).length < 2 ^ (prefixWord ++ tailWord_2224913).sum := by decide
  have hdescent : baseEnd_2224913 < baseStart_2224913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2224969 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_2224969 : Nat := 118140960795 + 2224969 * 2 ^ 59
def prefixEnd_2224969 : Nat := 4983230072969 + 3 ^ 40 * 2224969 * 2
def baseEnd_2224969 : Nat := 761652358902407021503373

theorem tailTrace_2224969 : CollatzResearch.WordTrace tailWord_2224969 prefixEnd_2224969 761652358902407021503373 := by
  unfold tailWord_2224969
  simp only [CollatzResearch.WordTrace]
  refine ⟨81151286276324782297405961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54100857517549854864937307 81151286276324782297405961)
  ·
    refine ⟨60863464707243586723054471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81151286276324782297405961 60863464707243586723054471)
    ·
      refine ⟨91295197060865380084581707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60863464707243586723054471 91295197060865380084581707)
      ·
        refine ⟨136942795591298070126872561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91295197060865380084581707 136942795591298070126872561)
        ·
          refine ⟨102707096693473552595154421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136942795591298070126872561 102707096693473552595154421)
          ·
            refine ⟨9628790315013145555795727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102707096693473552595154421 9628790315013145555795727)
            ·
              refine ⟨14443185472519718333693591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9628790315013145555795727 14443185472519718333693591)
              ·
                refine ⟨21664778208779577500540387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14443185472519718333693591 21664778208779577500540387)
                ·
                  refine ⟨32497167313169366250810581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21664778208779577500540387 32497167313169366250810581)
                  ·
                    refine ⟨761652358902407021503373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32497167313169366250810581 761652358902407021503373)
                    ·
                      rfl

theorem cell22_2224969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_2224969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2224969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2224969 prefixEnd_2224969 := by exact prefixLift 2224969
  have htrace : WordTrace (prefixWord ++ tailWord_2224969) baseStart_2224969 baseEnd_2224969 := by
    simpa [prefixWord, tailWord_2224969, baseEnd_2224969] using wordTrace_append hprefix tailTrace_2224969
  have hstable : (prefixWord ++ tailWord_2224969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2224969).length < 2 ^ (prefixWord ++ tailWord_2224969).sum := by decide
  have hdescent : baseEnd_2224969 < baseStart_2224969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2224969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225022 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_2225022 : Nat := 118140960795 + 2225022 * 2 ^ 59
def prefixEnd_2225022 : Nat := 4983230072969 + 3 ^ 40 * 2225022 * 2
def baseEnd_2225022 : Nat := 253890167295177516642737

theorem tailTrace_2225022 : CollatzResearch.WordTrace tailWord_2225022 prefixEnd_2225022 253890167295177516642737 := by
  unfold tailWord_2225022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10144152418141596543635665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54102146230088514899390213 10144152418141596543635665)
  ·
    refine ⟨7608114313606197407726749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10144152418141596543635665 7608114313606197407726749)
    ·
      refine ⟨2853042867602324027897531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7608114313606197407726749 2853042867602324027897531)
      ·
        refine ⟨4279564301403486041846297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853042867602324027897531 4279564301403486041846297)
        ·
          refine ⟨3209673226052614531384723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4279564301403486041846297 3209673226052614531384723)
          ·
            refine ⟨4814509839078921797077085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209673226052614531384723 4814509839078921797077085)
            ·
              refine ⟨1805441189654595673903907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4814509839078921797077085 1805441189654595673903907)
              ·
                refine ⟨2708161784481893510855861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805441189654595673903907 2708161784481893510855861)
                ·
                  refine ⟨253890167295177516642737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2708161784481893510855861 253890167295177516642737)
                  ·
                    rfl

theorem cell22_2225022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_2225022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225022 prefixEnd_2225022 := by exact prefixLift 2225022
  have htrace : WordTrace (prefixWord ++ tailWord_2225022) baseStart_2225022 baseEnd_2225022 := by
    simpa [prefixWord, tailWord_2225022, baseEnd_2225022] using wordTrace_append hprefix tailTrace_2225022
  have hstable : (prefixWord ++ tailWord_2225022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225022).length < 2 ^ (prefixWord ++ tailWord_2225022).sum := by decide
  have hdescent : baseEnd_2225022 < baseStart_2225022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225121 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2225121 : Nat := 118140960795 + 2225121 * 2 ^ 59
def prefixEnd_2225121 : Nat := 4983230072969 + 3 ^ 40 * 2225121 * 2
def baseEnd_2225121 : Nat := 761704391608729291702907

theorem tailTrace_2225121 : CollatzResearch.WordTrace tailWord_2225121 prefixEnd_2225121 761704391608729291702907 := by
  unfold tailWord_2225121
  simp only [CollatzResearch.WordTrace]
  refine ⟨81156830171774112256939217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54104553447849408171292811 81156830171774112256939217)
  ·
    refine ⟨60867622628830584192704413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81156830171774112256939217 60867622628830584192704413)
    ·
      refine ⟨22825358485811469072264155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60867622628830584192704413 22825358485811469072264155)
      ·
        refine ⟨34238037728717203608396233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22825358485811469072264155 34238037728717203608396233)
        ·
          refine ⟨25678528296537902706297175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34238037728717203608396233 25678528296537902706297175)
          ·
            refine ⟨38517792444806854059445763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25678528296537902706297175 38517792444806854059445763)
            ·
              refine ⟨57776688667210281089168645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38517792444806854059445763 57776688667210281089168645)
              ·
                refine ⟨10833129125101927704219121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57776688667210281089168645 10833129125101927704219121)
                ·
                  refine ⟨8124846843826445778164341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10833129125101927704219121 8124846843826445778164341)
                  ·
                    refine ⟨761704391608729291702907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8124846843826445778164341 761704391608729291702907)
                    ·
                      rfl

theorem cell22_2225121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2225121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225121 prefixEnd_2225121 := by exact prefixLift 2225121
  have htrace : WordTrace (prefixWord ++ tailWord_2225121) baseStart_2225121 baseEnd_2225121 := by
    simpa [prefixWord, tailWord_2225121, baseEnd_2225121] using wordTrace_append hprefix tailTrace_2225121
  have hstable : (prefixWord ++ tailWord_2225121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225121).length < 2 ^ (prefixWord ++ tailWord_2225121).sum := by decide
  have hdescent : baseEnd_2225121 < baseStart_2225121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225123 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 5]
def baseStart_2225123 : Nat := 118140960795 + 2225123 * 2 ^ 59
def prefixEnd_2225123 : Nat := 4983230072969 + 3 ^ 40 * 2225123 * 2
def baseEnd_2225123 : Nat := 253901692083200651050967

theorem tailTrace_2225123 : CollatzResearch.WordTrace tailWord_2225123 prefixEnd_2225123 253901692083200651050967 := by
  unfold tailWord_2225123
  simp only [CollatzResearch.WordTrace]
  refine ⟨81156903117766866598512023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54104602078511244399008015 81156903117766866598512023)
  ·
    refine ⟨121735354676650299897768035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81156903117766866598512023 121735354676650299897768035)
    ·
      refine ⟨182603032014975449846652053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121735354676650299897768035 182603032014975449846652053)
      ·
        refine ⟨8559517125701974211561815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 182603032014975449846652053 8559517125701974211561815)
        ·
          refine ⟨12839275688552961317342723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559517125701974211561815 12839275688552961317342723)
          ·
            refine ⟨19258913532829441976014085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12839275688552961317342723 19258913532829441976014085)
            ·
              refine ⟨3611046287405520370502641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19258913532829441976014085 3611046287405520370502641)
              ·
                refine ⟨2708284715554140277876981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611046287405520370502641 2708284715554140277876981)
                ·
                  refine ⟨253901692083200651050967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2708284715554140277876981 253901692083200651050967)
                  ·
                    rfl

theorem cell22_2225123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 5].length) (baseStart_2225123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225123 prefixEnd_2225123 := by exact prefixLift 2225123
  have htrace : WordTrace (prefixWord ++ tailWord_2225123) baseStart_2225123 baseEnd_2225123 := by
    simpa [prefixWord, tailWord_2225123, baseEnd_2225123] using wordTrace_append hprefix tailTrace_2225123
  have hstable : (prefixWord ++ tailWord_2225123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225123).length < 2 ^ (prefixWord ++ tailWord_2225123).sum := by decide
  have hdescent : baseEnd_2225123 < baseStart_2225123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225127 : List Nat := [1, 1, 5, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2225127 : Nat := 118140960795 + 2225127 * 2 ^ 59
def prefixEnd_2225127 : Nat := 4983230072969 + 3 ^ 40 * 2225127 * 2
def baseEnd_2225127 : Nat := 761706445531347276052889

theorem tailTrace_2225127 : CollatzResearch.WordTrace tailWord_2225127 prefixEnd_2225127 761706445531347276052889 := by
  unfold tailWord_2225127
  simp only [CollatzResearch.WordTrace]
  refine ⟨81157049009752375281657635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54104699339834916854438423 81157049009752375281657635)
  ·
    refine ⟨121735573514628562922486453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81157049009752375281657635 121735573514628562922486453)
    ·
      refine ⟨11412710016996427773983105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121735573514628562922486453 11412710016996427773983105)
      ·
        refine ⟨8559532512747320830487329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11412710016996427773983105 8559532512747320830487329)
        ·
          refine ⟨6419649384560490622865497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8559532512747320830487329 6419649384560490622865497)
          ·
            refine ⟨4814737038420367967149123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6419649384560490622865497 4814737038420367967149123)
            ·
              refine ⟨7222105557630551950723685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814737038420367967149123 7222105557630551950723685)
              ·
                refine ⟨1354144792055728490760691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7222105557630551950723685 1354144792055728490760691)
                ·
                  refine ⟨2031217188083592736141037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354144792055728490760691 2031217188083592736141037)
                  ·
                    refine ⟨761706445531347276052889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031217188083592736141037 761706445531347276052889)
                    ·
                      rfl

theorem cell22_2225127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2225127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225127 prefixEnd_2225127 := by exact prefixLift 2225127
  have htrace : WordTrace (prefixWord ++ tailWord_2225127) baseStart_2225127 baseEnd_2225127 := by
    simpa [prefixWord, tailWord_2225127, baseEnd_2225127] using wordTrace_append hprefix tailTrace_2225127
  have hstable : (prefixWord ++ tailWord_2225127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225127).length < 2 ^ (prefixWord ++ tailWord_2225127).sum := by decide
  have hdescent : baseEnd_2225127 < baseStart_2225127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225153 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2225153 : Nat := 118140960795 + 2225153 * 2 ^ 59
def prefixEnd_2225153 : Nat := 4983230072969 + 3 ^ 40 * 2225153 * 2
def baseEnd_2225153 : Nat := 761715345862691874902809

theorem tailTrace_2225153 : CollatzResearch.WordTrace tailWord_2225153 prefixEnd_2225153 761715345862691874902809 := by
  unfold tailWord_2225153
  simp only [CollatzResearch.WordTrace]
  refine ⟨81157997307658181722104113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54105331538438787814736075 81157997307658181722104113)
  ·
    refine ⟨60868497980743636291578085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81157997307658181722104113 60868497980743636291578085)
    ·
      refine ⟨11412843371389431804670891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60868497980743636291578085 11412843371389431804670891)
      ·
        refine ⟨17119265057084147707006337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11412843371389431804670891 17119265057084147707006337)
        ·
          refine ⟨12839448792813110780254753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17119265057084147707006337 12839448792813110780254753)
          ·
            refine ⟨9629586594609833085191065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12839448792813110780254753 9629586594609833085191065)
            ·
              refine ⟨7222189945957374813893299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9629586594609833085191065 7222189945957374813893299)
              ·
                refine ⟨10833284918936062220839949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222189945957374813893299 10833284918936062220839949)
                ·
                  refine ⟨4062481844601023332814981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10833284918936062220839949 4062481844601023332814981)
                  ·
                    refine ⟨761715345862691874902809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4062481844601023332814981 761715345862691874902809)
                    ·
                      rfl

theorem cell22_2225153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2225153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225153 prefixEnd_2225153 := by exact prefixLift 2225153
  have htrace : WordTrace (prefixWord ++ tailWord_2225153) baseStart_2225153 baseEnd_2225153 := by
    simpa [prefixWord, tailWord_2225153, baseEnd_2225153] using wordTrace_append hprefix tailTrace_2225153
  have hstable : (prefixWord ++ tailWord_2225153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225153).length < 2 ^ (prefixWord ++ tailWord_2225153).sum := by decide
  have hdescent : baseEnd_2225153 < baseStart_2225153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225185 : List Nat := [1, 2, 3, 2, 3, 1, 2, 4, 4]
def baseStart_2225185 : Nat := 118140960795 + 2225185 * 2 ^ 59
def prefixEnd_2225185 : Nat := 4983230072969 + 3 ^ 40 * 2225185 * 2
def baseEnd_2225185 : Nat := 253908766705551486034237

theorem tailTrace_2225185 : CollatzResearch.WordTrace tailWord_2225185 prefixEnd_2225185 253908766705551486034237 := by
  unfold tailWord_2225185
  simp only [CollatzResearch.WordTrace]
  refine ⟨81159164443542251187269009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54106109629028167458179339 81159164443542251187269009)
  ·
    refine ⟨60869373332656688390451757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81159164443542251187269009 60869373332656688390451757)
    ·
      refine ⟨22826014999746258146419409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60869373332656688390451757 22826014999746258146419409)
      ·
        refine ⟨17119511249809693609814557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22826014999746258146419409 17119511249809693609814557)
        ·
          refine ⟨6419816718678635103680459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17119511249809693609814557 6419816718678635103680459)
          ·
            refine ⟨9629725078017952655520689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419816718678635103680459 9629725078017952655520689)
            ·
              refine ⟨7222293808513464491640517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9629725078017952655520689 7222293808513464491640517)
              ·
                refine ⟨1354180089096274592182597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7222293808513464491640517 1354180089096274592182597)
                ·
                  refine ⟨253908766705551486034237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354180089096274592182597 253908766705551486034237)
                  ·
                    rfl

theorem cell22_2225185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_2225185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225185 prefixEnd_2225185 := by exact prefixLift 2225185
  have htrace : WordTrace (prefixWord ++ tailWord_2225185) baseStart_2225185 baseEnd_2225185 := by
    simpa [prefixWord, tailWord_2225185, baseEnd_2225185] using wordTrace_append hprefix tailTrace_2225185
  have hstable : (prefixWord ++ tailWord_2225185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225185).length < 2 ^ (prefixWord ++ tailWord_2225185).sum := by decide
  have hdescent : baseEnd_2225185 < baseStart_2225185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225196 : List Nat := [2, 2, 1, 1, 1, 2, 4, 9]
def baseStart_2225196 : Nat := 118140960795 + 2225196 * 2 ^ 59
def prefixEnd_2225196 : Nat := 4983230072969 + 3 ^ 40 * 2225196 * 2
def baseEnd_2225196 : Nat := 84636673960161566230853

theorem tailTrace_2225196 : CollatzResearch.WordTrace tailWord_2225196 prefixEnd_2225196 84636673960161566230853 := by
  unfold tailWord_2225196
  simp only [CollatzResearch.WordTrace]
  refine ⟨40579782823251200032959721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54106377097668266710612961 40579782823251200032959721)
  ·
    refine ⟨30434837117438400024719791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40579782823251200032959721 30434837117438400024719791)
    ·
      refine ⟨45652255676157600037079687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30434837117438400024719791 45652255676157600037079687)
      ·
        refine ⟨68478383514236400055619531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45652255676157600037079687 68478383514236400055619531)
        ·
          refine ⟨102717575271354600083429297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68478383514236400055619531 102717575271354600083429297)
          ·
            refine ⟨77038181453515950062571973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102717575271354600083429297 77038181453515950062571973)
            ·
              refine ⟨14444659022534240636732245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77038181453515950062571973 14444659022534240636732245)
              ·
                refine ⟨84636673960161566230853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14444659022534240636732245 84636673960161566230853)
                ·
                  rfl

theorem cell22_2225196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 9].length) (baseStart_2225196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225196 prefixEnd_2225196 := by exact prefixLift 2225196
  have htrace : WordTrace (prefixWord ++ tailWord_2225196) baseStart_2225196 baseEnd_2225196 := by
    simpa [prefixWord, tailWord_2225196, baseEnd_2225196] using wordTrace_append hprefix tailTrace_2225196
  have hstable : (prefixWord ++ tailWord_2225196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225196).length < 2 ^ (prefixWord ++ tailWord_2225196).sum := by decide
  have hdescent : baseEnd_2225196 < baseStart_2225196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225198 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2225198 : Nat := 118140960795 + 2225198 * 2 ^ 59
def prefixEnd_2225198 : Nat := 4983230072969 + 3 ^ 40 * 2225198 * 2
def baseEnd_2225198 : Nat := 761730750282326757527671

theorem tailTrace_2225198 : CollatzResearch.WordTrace tailWord_2225198 prefixEnd_2225198 761730750282326757527671 := by
  unfold tailWord_2225198
  simp only [CollatzResearch.WordTrace]
  refine ⟨10144954824061894300936531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54106425728330102938328165 10144954824061894300936531)
  ·
    refine ⟨15217432236092841451404797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10144954824061894300936531 15217432236092841451404797)
    ·
      refine ⟨5706537088534815544276799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15217432236092841451404797 5706537088534815544276799)
      ·
        refine ⟨8559805632802223316415199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5706537088534815544276799 8559805632802223316415199)
        ·
          refine ⟨12839708449203334974622799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559805632802223316415199 12839708449203334974622799)
          ·
            refine ⟨19259562673805002461934199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12839708449203334974622799 19259562673805002461934199)
            ·
              refine ⟨28889344010707503692901299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19259562673805002461934199 28889344010707503692901299)
              ·
                refine ⟨43334016016061255539351949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28889344010707503692901299 43334016016061255539351949)
                ·
                  refine ⟨16250256006022970827256981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43334016016061255539351949 16250256006022970827256981)
                  ·
                    refine ⟨761730750282326757527671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16250256006022970827256981 761730750282326757527671)
                    ·
                      rfl

theorem cell22_2225198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2225198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225198 prefixEnd_2225198 := by exact prefixLift 2225198
  have htrace : WordTrace (prefixWord ++ tailWord_2225198) baseStart_2225198 baseEnd_2225198 := by
    simpa [prefixWord, tailWord_2225198, baseEnd_2225198] using wordTrace_append hprefix tailTrace_2225198
  have hstable : (prefixWord ++ tailWord_2225198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225198).length < 2 ^ (prefixWord ++ tailWord_2225198).sum := by decide
  have hdescent : baseEnd_2225198 < baseStart_2225198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225213 : List Nat := [1, 4, 1, 3, 1, 3, 1, 8]
def baseStart_2225213 : Nat := 118140960795 + 2225213 * 2 ^ 59
def prefixEnd_2225213 : Nat := 4983230072969 + 3 ^ 40 * 2225213 * 2
def baseEnd_2225213 : Nat := 84637320565430190933625

theorem tailTrace_2225213 : CollatzResearch.WordTrace tailWord_2225213 prefixEnd_2225213 84637320565430190933625 := by
  unfold tailWord_2225213
  simp only [CollatzResearch.WordTrace]
  refine ⟨81160185687440811969288293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54106790458293874646192195 81160185687440811969288293)
  ·
    refine ⟨15217534816395152244241555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81160185687440811969288293 15217534816395152244241555)
    ·
      refine ⟨22826302224592728366362333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15217534816395152244241555 22826302224592728366362333)
      ·
        refine ⟨8559863334222273137385875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22826302224592728366362333 8559863334222273137385875)
        ·
          refine ⟨12839795001333409706078813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559863334222273137385875 12839795001333409706078813)
          ·
            refine ⟨4814923125500028639779555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12839795001333409706078813 4814923125500028639779555)
            ·
              refine ⟨7222384688250042959669333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814923125500028639779555 7222384688250042959669333)
              ·
                refine ⟨84637320565430190933625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7222384688250042959669333 84637320565430190933625)
                ·
                  rfl

theorem cell22_2225213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 8].length) (baseStart_2225213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225213 prefixEnd_2225213 := by exact prefixLift 2225213
  have htrace : WordTrace (prefixWord ++ tailWord_2225213) baseStart_2225213 baseEnd_2225213 := by
    simpa [prefixWord, tailWord_2225213, baseEnd_2225213] using wordTrace_append hprefix tailTrace_2225213
  have hstable : (prefixWord ++ tailWord_2225213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225213).length < 2 ^ (prefixWord ++ tailWord_2225213).sum := by decide
  have hdescent : baseEnd_2225213 < baseStart_2225213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225322 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2225322 : Nat := 118140960795 + 2225322 * 2 ^ 59
def prefixEnd_2225322 : Nat := 4983230072969 + 3 ^ 40 * 2225322 * 2
def baseEnd_2225322 : Nat := 761773198016431767427291

theorem tailTrace_2225322 : CollatzResearch.WordTrace tailWord_2225322 prefixEnd_2225322 761773198016431767427291 := by
  unfold tailWord_2225322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20291040311011480896251555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54109440829363949056670813 20291040311011480896251555)
  ·
    refine ⟨30436560466517221344377333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20291040311011480896251555 30436560466517221344377333)
    ·
      refine ⟨2853427543735989501035375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30436560466517221344377333 2853427543735989501035375)
      ·
        refine ⟨4280141315603984251553063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853427543735989501035375 4280141315603984251553063)
        ·
          refine ⟨6420211973405976377329595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4280141315603984251553063 6420211973405976377329595)
          ·
            refine ⟨9630317960108964565994393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6420211973405976377329595 9630317960108964565994393)
            ·
              refine ⟨7222738470081723424495795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9630317960108964565994393 7222738470081723424495795)
              ·
                refine ⟨10834107705122585136743693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7222738470081723424495795 10834107705122585136743693)
                ·
                  refine ⟨4062790389420969426278885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10834107705122585136743693 4062790389420969426278885)
                  ·
                    refine ⟨761773198016431767427291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4062790389420969426278885 761773198016431767427291)
                    ·
                      rfl

theorem cell22_2225322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2225322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225322 prefixEnd_2225322 := by exact prefixLift 2225322
  have htrace : WordTrace (prefixWord ++ tailWord_2225322) baseStart_2225322 baseEnd_2225322 := by
    simpa [prefixWord, tailWord_2225322, baseEnd_2225322] using wordTrace_append hprefix tailTrace_2225322
  have hstable : (prefixWord ++ tailWord_2225322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225322).length < 2 ^ (prefixWord ++ tailWord_2225322).sum := by decide
  have hdescent : baseEnd_2225322 < baseStart_2225322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225335 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 4, 3]
def baseStart_2225335 : Nat := 118140960795 + 2225335 * 2 ^ 59
def prefixEnd_2225335 : Nat := 4983230072969 + 3 ^ 40 * 2225335 * 2
def baseEnd_2225335 : Nat := 761777648182104066852251

theorem tailTrace_2225335 : CollatzResearch.WordTrace tailWord_2225335 prefixEnd_2225335 761777648182104066852251 := by
  unfold tailWord_2225335
  simp only [CollatzResearch.WordTrace]
  refine ⟨81164635392998826805229459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54109756928665884536819639 81164635392998826805229459)
  ·
    refine ⟨121746953089498240207844189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81164635392998826805229459 121746953089498240207844189)
    ·
      refine ⟨45655107408561840077941571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121746953089498240207844189 45655107408561840077941571)
      ·
        refine ⟨68482661112842760116912357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45655107408561840077941571 68482661112842760116912357)
        ·
          refine ⟨12840498958658017521921067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68482661112842760116912357 12840498958658017521921067)
          ·
            refine ⟨19260748437987026282881601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12840498958658017521921067 19260748437987026282881601)
            ·
              refine ⟨14445561328490269712161201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19260748437987026282881601 14445561328490269712161201)
              ·
                refine ⟨10834170996367702284120901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14445561328490269712161201 10834170996367702284120901)
                ·
                  refine ⟨2031407061818944178272669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10834170996367702284120901 2031407061818944178272669)
                  ·
                    refine ⟨761777648182104066852251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031407061818944178272669 761777648182104066852251)
                    ·
                      rfl

theorem cell22_2225335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_2225335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225335 prefixEnd_2225335 := by exact prefixLift 2225335
  have htrace : WordTrace (prefixWord ++ tailWord_2225335) baseStart_2225335 baseEnd_2225335 := by
    simpa [prefixWord, tailWord_2225335, baseEnd_2225335] using wordTrace_append hprefix tailTrace_2225335
  have hstable : (prefixWord ++ tailWord_2225335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225335).length < 2 ^ (prefixWord ++ tailWord_2225335).sum := by decide
  have hdescent : baseEnd_2225335 < baseStart_2225335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225337 : List Nat := [1, 2, 1, 4, 1, 4, 2, 3, 4]
def baseStart_2225337 : Nat := 118140960795 + 2225337 * 2 ^ 59
def prefixEnd_2225337 : Nat := 4983230072969 + 3 ^ 40 * 2225337 * 2
def baseEnd_2225337 : Nat := 253926110940992242767415

theorem tailTrace_2225337 : CollatzResearch.WordTrace tailWord_2225337 prefixEnd_2225337 253926110940992242767415 := by
  unfold tailWord_2225337
  simp only [CollatzResearch.WordTrace]
  refine ⟨81164708338991581146802265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54109805559327720764534843 81164708338991581146802265)
  ·
    refine ⟨60873531254243685860101699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81164708338991581146802265 60873531254243685860101699)
    ·
      refine ⟨91310296881365528790152549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60873531254243685860101699 91310296881365528790152549)
      ·
        refine ⟨17120680665256036648153603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91310296881365528790152549 17120680665256036648153603)
        ·
          refine ⟨25681020997884054972230405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17120680665256036648153603 25681020997884054972230405)
          ·
            refine ⟨4815191437103260307293201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25681020997884054972230405 4815191437103260307293201)
            ·
              refine ⟨3611393577827445230469901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4815191437103260307293201 3611393577827445230469901)
              ·
                refine ⟨1354272591685291961426213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3611393577827445230469901 1354272591685291961426213)
                ·
                  refine ⟨253926110940992242767415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354272591685291961426213 253926110940992242767415)
                  ·
                    rfl

theorem cell22_2225337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_2225337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225337 prefixEnd_2225337 := by exact prefixLift 2225337
  have htrace : WordTrace (prefixWord ++ tailWord_2225337) baseStart_2225337 baseEnd_2225337 := by
    simpa [prefixWord, tailWord_2225337, baseEnd_2225337] using wordTrace_append hprefix tailTrace_2225337
  have hstable : (prefixWord ++ tailWord_2225337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225337).length < 2 ^ (prefixWord ++ tailWord_2225337).sum := by decide
  have hdescent : baseEnd_2225337 < baseStart_2225337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225352 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 2, 3]
def baseStart_2225352 : Nat := 118140960795 + 2225352 * 2 ^ 59
def prefixEnd_2225352 : Nat := 4983230072969 + 3 ^ 40 * 2225352 * 2
def baseEnd_2225352 : Nat := 761783467629521689177199

theorem tailTrace_2225352 : CollatzResearch.WordTrace tailWord_2225352 prefixEnd_2225352 761783467629521689177199 := by
  unfold tailWord_2225352
  simp only [CollatzResearch.WordTrace]
  refine ⟨40582627716968619354299155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54110170289291492472398873 40582627716968619354299155)
  ·
    refine ⟨60873941575452929031448733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40582627716968619354299155 60873941575452929031448733)
    ·
      refine ⟨22827728090794848386793275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60873941575452929031448733 22827728090794848386793275)
      ·
        refine ⟨34241592136192272580189913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22827728090794848386793275 34241592136192272580189913)
        ·
          refine ⟨25681194102144204435142435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34241592136192272580189913 25681194102144204435142435)
          ·
            refine ⟨38521791153216306652713653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25681194102144204435142435 38521791153216306652713653)
            ·
              refine ⟨3611417920614028748691905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38521791153216306652713653 3611417920614028748691905)
              ·
                refine ⟨2708563440460521561518929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611417920614028748691905 2708563440460521561518929)
                ·
                  refine ⟨2031422580345391171139197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2708563440460521561518929 2031422580345391171139197)
                  ·
                    refine ⟨761783467629521689177199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031422580345391171139197 761783467629521689177199)
                    ·
                      rfl

theorem cell22_2225352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_2225352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225352 prefixEnd_2225352 := by exact prefixLift 2225352
  have htrace : WordTrace (prefixWord ++ tailWord_2225352) baseStart_2225352 baseEnd_2225352 := by
    simpa [prefixWord, tailWord_2225352, baseEnd_2225352] using wordTrace_append hprefix tailTrace_2225352
  have hstable : (prefixWord ++ tailWord_2225352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225352).length < 2 ^ (prefixWord ++ tailWord_2225352).sum := by decide
  have hdescent : baseEnd_2225352 < baseStart_2225352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225423 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 10]
def baseStart_2225423 : Nat := 118140960795 + 2225423 * 2 ^ 59
def prefixEnd_2225423 : Nat := 4983230072969 + 3 ^ 40 * 2225423 * 2
def baseEnd_2225423 : Nat := 761807772380501170651981

theorem tailTrace_2225423 : CollatzResearch.WordTrace tailWord_2225423 prefixEnd_2225423 761807772380501170651981 := by
  unfold tailWord_2225423
  simp only [CollatzResearch.WordTrace]
  refine ⟨81167845016680017834432923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54111896677786678556288615 81167845016680017834432923)
  ·
    refine ⟨121751767525020026751649385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81167845016680017834432923 121751767525020026751649385)
    ·
      refine ⟨91313825643765020063737039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121751767525020026751649385 91313825643765020063737039)
      ·
        refine ⟨136970738465647530095605559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91313825643765020063737039 136970738465647530095605559)
        ·
          refine ⟨205456107698471295143408339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136970738465647530095605559 205456107698471295143408339)
          ·
            refine ⟨308184161547706942715112509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205456107698471295143408339 308184161547706942715112509)
            ·
              refine ⟨115569060580390103518167191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 308184161547706942715112509 115569060580390103518167191)
              ·
                refine ⟨173353590870585155277250787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115569060580390103518167191 173353590870585155277250787)
                ·
                  refine ⟨260030386305877732915876181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173353590870585155277250787 260030386305877732915876181)
                  ·
                    refine ⟨761807772380501170651981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 260030386305877732915876181 761807772380501170651981)
                    ·
                      rfl

theorem cell22_2225423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_2225423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225423 prefixEnd_2225423 := by exact prefixLift 2225423
  have htrace : WordTrace (prefixWord ++ tailWord_2225423) baseStart_2225423 baseEnd_2225423 := by
    simpa [prefixWord, tailWord_2225423, baseEnd_2225423] using wordTrace_append hprefix tailTrace_2225423
  have hstable : (prefixWord ++ tailWord_2225423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225423).length < 2 ^ (prefixWord ++ tailWord_2225423).sum := by decide
  have hdescent : baseEnd_2225423 < baseStart_2225423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225465 : List Nat := [1, 2, 1, 6, 3, 1, 2, 2, 1, 3]
def baseStart_2225465 : Nat := 118140960795 + 2225465 * 2 ^ 59
def prefixEnd_2225465 : Nat := 4983230072969 + 3 ^ 40 * 2225465 * 2
def baseEnd_2225465 : Nat := 761822149838827061101853

theorem tailTrace_2225465 : CollatzResearch.WordTrace tailWord_2225465 prefixEnd_2225465 761822149838827061101853 := by
  unfold tailWord_2225465
  simp only [CollatzResearch.WordTrace]
  refine ⟨81169376882527859007461849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54112917921685239338307899 81169376882527859007461849)
  ·
    refine ⟨60877032661895894255596387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81169376882527859007461849 60877032661895894255596387)
    ·
      refine ⟨91315548992843841383394581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60877032661895894255596387 91315548992843841383394581)
      ·
        refine ⟨4280416359039555064846621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91315548992843841383394581 4280416359039555064846621)
        ·
          refine ⟨1605156134639833149317483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4280416359039555064846621 1605156134639833149317483)
          ·
            refine ⟨2407734201959749723976225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605156134639833149317483 2407734201959749723976225)
            ·
              refine ⟨1805800651469812292982169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2407734201959749723976225 1805800651469812292982169)
              ·
                refine ⟨1354350488602359219736627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1805800651469812292982169 1354350488602359219736627)
                ·
                  refine ⟨2031525732903538829604941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354350488602359219736627 2031525732903538829604941)
                  ·
                    refine ⟨761822149838827061101853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031525732903538829604941 761822149838827061101853)
                    ·
                      rfl

theorem cell22_2225465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 3].length) (baseStart_2225465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225465 prefixEnd_2225465 := by exact prefixLift 2225465
  have htrace : WordTrace (prefixWord ++ tailWord_2225465) baseStart_2225465 baseEnd_2225465 := by
    simpa [prefixWord, tailWord_2225465, baseEnd_2225465] using wordTrace_append hprefix tailTrace_2225465
  have hstable : (prefixWord ++ tailWord_2225465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225465).length < 2 ^ (prefixWord ++ tailWord_2225465).sum := by decide
  have hdescent : baseEnd_2225465 < baseStart_2225465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225472 : List Nat := [2, 1, 1, 2, 2, 1, 5, 4, 4]
def baseStart_2225472 : Nat := 118140960795 + 2225472 * 2 ^ 59
def prefixEnd_2225472 : Nat := 4983230072969 + 3 ^ 40 * 2225472 * 2
def baseEnd_2225472 : Nat := 253941515360627125392277

theorem tailTrace_2225472 : CollatzResearch.WordTrace tailWord_2225472 prefixEnd_2225472 253941515360627125392277 := by
  unfold tailWord_2225472
  simp only [CollatzResearch.WordTrace]
  refine ⟨40584816096751249601483335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54113088129001666135311113 40584816096751249601483335)
  ·
    refine ⟨60877224145126874402225003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40584816096751249601483335 60877224145126874402225003)
    ·
      refine ⟨91315836217690311603337505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60877224145126874402225003 91315836217690311603337505)
      ·
        refine ⟨68486877163267733702503129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91315836217690311603337505 68486877163267733702503129)
        ·
          refine ⟨51365157872450800276877347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68486877163267733702503129 51365157872450800276877347)
          ·
            refine ⟨77047736808676200415316021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51365157872450800276877347 77047736808676200415316021)
            ·
              refine ⟨7223225325813393788935877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77047736808676200415316021 7223225325813393788935877)
              ·
                refine ⟨1354354748590011335425477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7223225325813393788935877 1354354748590011335425477)
                ·
                  refine ⟨253941515360627125392277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354354748590011335425477 253941515360627125392277)
                  ·
                    rfl

theorem cell22_2225472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_2225472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225472 prefixEnd_2225472 := by exact prefixLift 2225472
  have htrace : WordTrace (prefixWord ++ tailWord_2225472) baseStart_2225472 baseEnd_2225472 := by
    simpa [prefixWord, tailWord_2225472, baseEnd_2225472] using wordTrace_append hprefix tailTrace_2225472
  have hstable : (prefixWord ++ tailWord_2225472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225472).length < 2 ^ (prefixWord ++ tailWord_2225472).sum := by decide
  have hdescent : baseEnd_2225472 < baseStart_2225472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225626 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_2225626 : Nat := 118140960795 + 2225626 * 2 ^ 59
def prefixEnd_2225626 : Nat := 4983230072969 + 3 ^ 40 * 2225626 * 2
def baseEnd_2225626 : Nat := 761877263429076307826359

theorem tailTrace_2225626 : CollatzResearch.WordTrace tailWord_2225626 prefixEnd_2225626 761877263429076307826359 := by
  unfold tailWord_2225626
  simp only [CollatzResearch.WordTrace]
  refine ⟨20293812258736145876018183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54116832689963055669381821 20293812258736145876018183)
  ·
    refine ⟨30440718388104218814027275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20293812258736145876018183 30440718388104218814027275)
    ·
      refine ⟨45661077582156328221040913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30440718388104218814027275 45661077582156328221040913)
      ·
        refine ⟨34245808186617246165780685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45661077582156328221040913 34245808186617246165780685)
        ·
          refine ⟨12842178069981467312167757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34245808186617246165780685 12842178069981467312167757)
          ·
            refine ⟨4815816776243050242062909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12842178069981467312167757 4815816776243050242062909)
            ·
              refine ⟨1805931291091143840773591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4815816776243050242062909 1805931291091143840773591)
              ·
                refine ⟨2708896936636715761160387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805931291091143840773591 2708896936636715761160387)
                ·
                  refine ⟨4063345404955073641740581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708896936636715761160387 4063345404955073641740581)
                  ·
                    refine ⟨761877263429076307826359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063345404955073641740581 761877263429076307826359)
                    ·
                      rfl

theorem cell22_2225626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_2225626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225626 prefixEnd_2225626 := by exact prefixLift 2225626
  have htrace : WordTrace (prefixWord ++ tailWord_2225626) baseStart_2225626 baseEnd_2225626 := by
    simpa [prefixWord, tailWord_2225626, baseEnd_2225626] using wordTrace_append hprefix tailTrace_2225626
  have hstable : (prefixWord ++ tailWord_2225626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225626).length < 2 ^ (prefixWord ++ tailWord_2225626).sum := by decide
  have hdescent : baseEnd_2225626 < baseStart_2225626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225671 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2225671 : Nat := 118140960795 + 2225671 * 2 ^ 59
def prefixEnd_2225671 : Nat := 4983230072969 + 3 ^ 40 * 2225671 * 2
def baseEnd_2225671 : Nat := 761892667848711190451221

theorem tailTrace_2225671 : CollatzResearch.WordTrace tailWord_2225671 prefixEnd_2225671 761892667848711190451221 := by
  unfold tailWord_2225671
  simp only [CollatzResearch.WordTrace]
  refine ⟨81176890319781556189460867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54117926879854370792973911 81176890319781556189460867)
  ·
    refine ⟨121765335479672334284191301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81176890319781556189460867 121765335479672334284191301)
    ·
      refine ⟨22831000402438562678285869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121765335479672334284191301 22831000402438562678285869)
      ·
        refine ⟨8561625150914461004357201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22831000402438562678285869 8561625150914461004357201)
        ·
          refine ⟨6421218863185845753267901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8561625150914461004357201 6421218863185845753267901)
          ·
            refine ⟨2407957073694692157475463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6421218863185845753267901 2407957073694692157475463)
            ·
              refine ⟨3611935610542038236213195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407957073694692157475463 3611935610542038236213195)
              ·
                refine ⟨5417903415813057354319793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3611935610542038236213195 5417903415813057354319793)
                ·
                  refine ⟨4063427561859793015739845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5417903415813057354319793 4063427561859793015739845)
                  ·
                    refine ⟨761892667848711190451221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063427561859793015739845 761892667848711190451221)
                    ·
                      rfl

theorem cell22_2225671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2225671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225671 prefixEnd_2225671 := by exact prefixLift 2225671
  have htrace : WordTrace (prefixWord ++ tailWord_2225671) baseStart_2225671 baseEnd_2225671 := by
    simpa [prefixWord, tailWord_2225671, baseEnd_2225671] using wordTrace_append hprefix tailTrace_2225671
  have hstable : (prefixWord ++ tailWord_2225671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225671).length < 2 ^ (prefixWord ++ tailWord_2225671).sum := by decide
  have hdescent : baseEnd_2225671 < baseStart_2225671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225677 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2225677 : Nat := 118140960795 + 2225677 * 2 ^ 59
def prefixEnd_2225677 : Nat := 4983230072969 + 3 ^ 40 * 2225677 * 2
def baseEnd_2225677 : Nat := 761894721771329174801203

theorem tailTrace_2225677 : CollatzResearch.WordTrace tailWord_2225677 prefixEnd_2225677 761894721771329174801203 := by
  unfold tailWord_2225677
  simp only [CollatzResearch.WordTrace]
  refine ⟨81177109157759819214179285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54118072771839879476119523 81177109157759819214179285)
  ·
    refine ⟨1902588495884995762832327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 81177109157759819214179285 1902588495884995762832327)
    ·
      refine ⟨2853882743827493644248491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902588495884995762832327 2853882743827493644248491)
      ·
        refine ⟨4280824115741240466372737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853882743827493644248491 4280824115741240466372737)
        ·
          refine ⟨3210618086805930349779553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4280824115741240466372737 3210618086805930349779553)
          ·
            refine ⟨2407963565104447762334665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3210618086805930349779553 2407963565104447762334665)
            ·
              refine ⟨1805972673828335821750999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2407963565104447762334665 1805972673828335821750999)
              ·
                refine ⟨2708959010742503732626499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805972673828335821750999 2708959010742503732626499)
                ·
                  refine ⟨4063438516113755598939749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708959010742503732626499 4063438516113755598939749)
                  ·
                    refine ⟨761894721771329174801203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063438516113755598939749 761894721771329174801203)
                    ·
                      rfl

theorem cell22_2225677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2225677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225677 prefixEnd_2225677 := by exact prefixLift 2225677
  have htrace : WordTrace (prefixWord ++ tailWord_2225677) baseStart_2225677 baseEnd_2225677 := by
    simpa [prefixWord, tailWord_2225677, baseEnd_2225677] using wordTrace_append hprefix tailTrace_2225677
  have hstable : (prefixWord ++ tailWord_2225677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225677).length < 2 ^ (prefixWord ++ tailWord_2225677).sum := by decide
  have hdescent : baseEnd_2225677 < baseStart_2225677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225735 : List Nat := [1, 1, 4, 1, 5, 2, 1, 3, 1, 3]
def baseStart_2225735 : Nat := 118140960795 + 2225735 * 2 ^ 59
def prefixEnd_2225735 : Nat := 4983230072969 + 3 ^ 40 * 2225735 * 2
def baseEnd_2225735 : Nat := 761914576356636356851025

theorem tailTrace_2225735 : CollatzResearch.WordTrace tailWord_2225735 prefixEnd_2225735 761914576356636356851025 := by
  unfold tailWord_2225735
  simp only [CollatzResearch.WordTrace]
  refine ⟨81179224591549695119790659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54119483061033130079860439 81179224591549695119790659)
  ·
    refine ⟨121768836887324542679685989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81179224591549695119790659 121768836887324542679685989)
    ·
      refine ⟨22831656916373351752441123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121768836887324542679685989 22831656916373351752441123)
      ·
        refine ⟨34247485374560027628661685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22831656916373351752441123 34247485374560027628661685)
        ·
          refine ⟨3210701753865002590187033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34247485374560027628661685 3210701753865002590187033)
          ·
            refine ⟨2408026315398751942640275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3210701753865002590187033 2408026315398751942640275)
            ·
              refine ⟨3612039473098127913960413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408026315398751942640275 3612039473098127913960413)
              ·
                refine ⟨1354514802411797967735155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3612039473098127913960413 1354514802411797967735155)
                ·
                  refine ⟨2031772203617696951602733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354514802411797967735155 2031772203617696951602733)
                  ·
                    refine ⟨761914576356636356851025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031772203617696951602733 761914576356636356851025)
                    ·
                      rfl

theorem cell22_2225735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_2225735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225735 prefixEnd_2225735 := by exact prefixLift 2225735
  have htrace : WordTrace (prefixWord ++ tailWord_2225735) baseStart_2225735 baseEnd_2225735 := by
    simpa [prefixWord, tailWord_2225735, baseEnd_2225735] using wordTrace_append hprefix tailTrace_2225735
  have hstable : (prefixWord ++ tailWord_2225735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225735).length < 2 ^ (prefixWord ++ tailWord_2225735).sum := by decide
  have hdescent : baseEnd_2225735 < baseStart_2225735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225744 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_2225744 : Nat := 118140960795 + 2225744 * 2 ^ 59
def prefixEnd_2225744 : Nat := 4983230072969 + 3 ^ 40 * 2225744 * 2
def baseEnd_2225744 : Nat := 761917657240563333375997

theorem tailTrace_2225744 : CollatzResearch.WordTrace tailWord_2225744 prefixEnd_2225744 761917657240563333375997 := by
  unfold tailWord_2225744
  simp only [CollatzResearch.WordTrace]
  refine ⟨40589776424258544828434143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54119701899011393104578857 40589776424258544828434143)
  ·
    refine ⟨60884664636387817242651215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40589776424258544828434143 60884664636387817242651215)
    ·
      refine ⟨91326996954581725863976823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60884664636387817242651215 91326996954581725863976823)
      ·
        refine ⟨136990495431872588795965235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91326996954581725863976823 136990495431872588795965235)
        ·
          refine ⟨205485743147808883193947853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136990495431872588795965235 205485743147808883193947853)
          ·
            refine ⟨77057153680428331197730445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205485743147808883193947853 77057153680428331197730445)
            ·
              refine ⟨28896432630160624199148917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77057153680428331197730445 28896432630160624199148917)
              ·
                refine ⟨2709040559077558518670211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28896432630160624199148917 2709040559077558518670211)
                ·
                  refine ⟨4063560838616337778005317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709040559077558518670211 4063560838616337778005317)
                  ·
                    refine ⟨761917657240563333375997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063560838616337778005317 761917657240563333375997)
                    ·
                      rfl

theorem cell22_2225744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_2225744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225744 prefixEnd_2225744 := by exact prefixLift 2225744
  have htrace : WordTrace (prefixWord ++ tailWord_2225744) baseStart_2225744 baseEnd_2225744 := by
    simpa [prefixWord, tailWord_2225744, baseEnd_2225744] using wordTrace_append hprefix tailTrace_2225744
  have hstable : (prefixWord ++ tailWord_2225744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225744).length < 2 ^ (prefixWord ++ tailWord_2225744).sum := by decide
  have hdescent : baseEnd_2225744 < baseStart_2225744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225778 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_2225778 : Nat := 118140960795 + 2225778 * 2 ^ 59
def prefixEnd_2225778 : Nat := 4983230072969 + 3 ^ 40 * 2225778 * 2
def baseEnd_2225778 : Nat := 761929296135398578025893

theorem tailTrace_2225778 : CollatzResearch.WordTrace tailWord_2225778 prefixEnd_2225778 761929296135398578025893 := by
  unfold tailWord_2225778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20295198232598478365901497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54120528620262608975737325 20295198232598478365901497)
  ·
    refine ⟨15221398674448858774426123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20295198232598478365901497 15221398674448858774426123)
    ·
      refine ⟨22832098011673288161639185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15221398674448858774426123 22832098011673288161639185)
      ·
        refine ⟨17124073508754966121229389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22832098011673288161639185 17124073508754966121229389)
        ·
          refine ⟨6421527565783112295461021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17124073508754966121229389 6421527565783112295461021)
          ·
            refine ⟨2408072837168667110797883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6421527565783112295461021 2408072837168667110797883)
            ·
              refine ⟨3612109255753000666196825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408072837168667110797883 3612109255753000666196825)
              ·
                refine ⟨2709081941814750499647619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3612109255753000666196825 2709081941814750499647619)
                ·
                  refine ⟨4063622912722125749471429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709081941814750499647619 4063622912722125749471429)
                  ·
                    refine ⟨761929296135398578025893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063622912722125749471429 761929296135398578025893)
                    ·
                      rfl

theorem cell22_2225778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_2225778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225778 prefixEnd_2225778 := by exact prefixLift 2225778
  have htrace : WordTrace (prefixWord ++ tailWord_2225778) baseStart_2225778 baseEnd_2225778 := by
    simpa [prefixWord, tailWord_2225778, baseEnd_2225778] using wordTrace_append hprefix tailTrace_2225778
  have hstable : (prefixWord ++ tailWord_2225778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225778).length < 2 ^ (prefixWord ++ tailWord_2225778).sum := by decide
  have hdescent : baseEnd_2225778 < baseStart_2225778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225787 : List Nat := [1, 1, 1, 1, 1, 4, 3, 10]
def baseStart_2225787 : Nat := 118140960795 + 2225787 * 2 ^ 59
def prefixEnd_2225787 : Nat := 4983230072969 + 3 ^ 40 * 2225787 * 2
def baseEnd_2225787 : Nat := 84659153002147283838985

theorem tailTrace_2225787 : CollatzResearch.WordTrace tailWord_2225787 prefixEnd_2225787 84659153002147283838985 := by
  unfold tailWord_2225787
  simp only [CollatzResearch.WordTrace]
  refine ⟨81181121187361308000683615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54120747458240872000455743 81181121187361308000683615)
  ·
    refine ⟨121771681781041962001025423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81181121187361308000683615 121771681781041962001025423)
    ·
      refine ⟨182657522671562943001538135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121771681781041962001025423 182657522671562943001538135)
      ·
        refine ⟨273986284007344414502307203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182657522671562943001538135 273986284007344414502307203)
        ·
          refine ⟨410979426011016621753460805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273986284007344414502307203 410979426011016621753460805)
          ·
            refine ⟨77058642377065616578773901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 410979426011016621753460805 77058642377065616578773901)
            ·
              refine ⟨28896990891399606217040213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77058642377065616578773901 28896990891399606217040213)
              ·
                refine ⟨84659153002147283838985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28896990891399606217040213 84659153002147283838985)
                ·
                  rfl

theorem cell22_2225787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 10].length) (baseStart_2225787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225787 prefixEnd_2225787 := by exact prefixLift 2225787
  have htrace : WordTrace (prefixWord ++ tailWord_2225787) baseStart_2225787 baseEnd_2225787 := by
    simpa [prefixWord, tailWord_2225787, baseEnd_2225787] using wordTrace_append hprefix tailTrace_2225787
  have hstable : (prefixWord ++ tailWord_2225787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225787).length < 2 ^ (prefixWord ++ tailWord_2225787).sum := by decide
  have hdescent : baseEnd_2225787 < baseStart_2225787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225806 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2225806 : Nat := 118140960795 + 2225806 * 2 ^ 59
def prefixEnd_2225806 : Nat := 4983230072969 + 3 ^ 40 * 2225806 * 2
def baseEnd_2225806 : Nat := 761938881107615838325807

theorem tailTrace_2225806 : CollatzResearch.WordTrace tailWord_2225806 prefixEnd_2225806 761938881107615838325807 := by
  unfold tailWord_2225806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147726771786559280703159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54121209449528316163750181 10147726771786559280703159)
  ·
    refine ⟨15221590157679838921054739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10147726771786559280703159 15221590157679838921054739)
    ·
      refine ⟨22832385236519758381582109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15221590157679838921054739 22832385236519758381582109)
      ·
        refine ⟨8562144463694909393093291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22832385236519758381582109 8562144463694909393093291)
        ·
          refine ⟨12843216695542364089639937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8562144463694909393093291 12843216695542364089639937)
          ·
            refine ⟨9632412521656773067229953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12843216695542364089639937 9632412521656773067229953)
            ·
              refine ⟨7224309391242579800422465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9632412521656773067229953 7224309391242579800422465)
              ·
                refine ⟨5418232043431934850316849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7224309391242579800422465 5418232043431934850316849)
                ·
                  refine ⟨4063674032573951137737637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5418232043431934850316849 4063674032573951137737637)
                  ·
                    refine ⟨761938881107615838325807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4063674032573951137737637 761938881107615838325807)
                    ·
                      rfl

theorem cell22_2225806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2225806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225806 prefixEnd_2225806 := by exact prefixLift 2225806
  have htrace : WordTrace (prefixWord ++ tailWord_2225806) baseStart_2225806 baseEnd_2225806 := by
    simpa [prefixWord, tailWord_2225806, baseEnd_2225806] using wordTrace_append hprefix tailTrace_2225806
  have hstable : (prefixWord ++ tailWord_2225806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225806).length < 2 ^ (prefixWord ++ tailWord_2225806).sum := by decide
  have hdescent : baseEnd_2225806 < baseStart_2225806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225864 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2225864 : Nat := 118140960795 + 2225864 * 2 ^ 59
def prefixEnd_2225864 : Nat := 4983230072969 + 3 ^ 40 * 2225864 * 2
def baseEnd_2225864 : Nat := 761958735692923020375629

theorem tailTrace_2225864 : CollatzResearch.WordTrace tailWord_2225864 prefixEnd_2225864 761958735692923020375629 := by
  unfold tailWord_2225864
  simp only [CollatzResearch.WordTrace]
  refine ⟨40591964804041175075618323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54122619738721566767491097 40591964804041175075618323)
  ·
    refine ⟨60887947206061762613427485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40591964804041175075618323 60887947206061762613427485)
    ·
      refine ⟨22832980202273160980035307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60887947206061762613427485 22832980202273160980035307)
      ·
        refine ⟨34249470303409741470052961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22832980202273160980035307 34249470303409741470052961)
        ·
          refine ⟨25687102727557306102539721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34249470303409741470052961 25687102727557306102539721)
          ·
            refine ⟨19265327045667979576904791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25687102727557306102539721 19265327045667979576904791)
            ·
              refine ⟨28897990568501969365357187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19265327045667979576904791 28897990568501969365357187)
              ·
                refine ⟨43346985852752954048035781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28897990568501969365357187 43346985852752954048035781)
                ·
                  refine ⟨8127559847391178884006709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43346985852752954048035781 8127559847391178884006709)
                  ·
                    refine ⟨761958735692923020375629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8127559847391178884006709 761958735692923020375629)
                    ·
                      rfl

theorem cell22_2225864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2225864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225864 prefixEnd_2225864 := by exact prefixLift 2225864
  have htrace : WordTrace (prefixWord ++ tailWord_2225864) baseStart_2225864 baseEnd_2225864 := by
    simpa [prefixWord, tailWord_2225864, baseEnd_2225864] using wordTrace_append hprefix tailTrace_2225864
  have hstable : (prefixWord ++ tailWord_2225864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225864).length < 2 ^ (prefixWord ++ tailWord_2225864).sum := by decide
  have hdescent : baseEnd_2225864 < baseStart_2225864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225866 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_2225866 : Nat := 118140960795 + 2225866 * 2 ^ 59
def prefixEnd_2225866 : Nat := 4983230072969 + 3 ^ 40 * 2225866 * 2
def baseEnd_2225866 : Nat := 253986473444598560608541

theorem tailTrace_2225866 : CollatzResearch.WordTrace tailWord_2225866 prefixEnd_2225866 253986473444598560608541 := by
  unfold tailWord_2225866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20296000638518776123202363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54122668369383402995206301 20296000638518776123202363)
  ·
    refine ⟨30444000957778164184803545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20296000638518776123202363 30444000957778164184803545)
    ·
      refine ⟨22833000718333623138602659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30444000957778164184803545 22833000718333623138602659)
      ·
        refine ⟨34249501077500434707903989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22833000718333623138602659 34249501077500434707903989)
        ·
          refine ⟨3210890726015665753865999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34249501077500434707903989 3210890726015665753865999)
          ·
            refine ⟨4816336089023498630798999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3210890726015665753865999 4816336089023498630798999)
            ·
              refine ⟨7224504133535247946198499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4816336089023498630798999 7224504133535247946198499)
              ·
                refine ⟨10836756200302871919297749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7224504133535247946198499 10836756200302871919297749)
                ·
                  refine ⟨253986473444598560608541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10836756200302871919297749 253986473444598560608541)
                  ·
                    rfl

theorem cell22_2225866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_2225866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225866 prefixEnd_2225866 := by exact prefixLift 2225866
  have htrace : WordTrace (prefixWord ++ tailWord_2225866) baseStart_2225866 baseEnd_2225866 := by
    simpa [prefixWord, tailWord_2225866, baseEnd_2225866] using wordTrace_append hprefix tailTrace_2225866
  have hstable : (prefixWord ++ tailWord_2225866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225866).length < 2 ^ (prefixWord ++ tailWord_2225866).sum := by decide
  have hdescent : baseEnd_2225866 < baseStart_2225866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225956 : List Nat := [2, 3, 1, 3, 2, 1, 2, 8]
def baseStart_2225956 : Nat := 118140960795 + 2225956 * 2 ^ 59
def prefixEnd_2225956 : Nat := 4983230072969 + 3 ^ 40 * 2225956 * 2
def baseEnd_2225956 : Nat := 84665581019229494119483

theorem tailTrace_2225956 : CollatzResearch.WordTrace tailWord_2225956 prefixEnd_2225956 84665581019229494119483 := by
  unfold tailWord_2225956
  simp only [CollatzResearch.WordTrace]
  refine ⟨40593642561874524931792861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54124856749166033242390481 40593642561874524931792861)
  ·
    refine ⟨15222615960702946849422323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40593642561874524931792861 15222615960702946849422323)
    ·
      refine ⟨22833923941054420274133485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15222615960702946849422323 22833923941054420274133485)
      ·
        refine ⟨8562721477895407602800057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22833923941054420274133485 8562721477895407602800057)
        ·
          refine ⟨6422041108421555702100043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8562721477895407602800057 6422041108421555702100043)
          ·
            refine ⟨9633061662632333553150065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6422041108421555702100043 9633061662632333553150065)
            ·
              refine ⟨7224796246974250164862549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9633061662632333553150065 7224796246974250164862549)
              ·
                refine ⟨84665581019229494119483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7224796246974250164862549 84665581019229494119483)
                ·
                  rfl

theorem cell22_2225956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 8].length) (baseStart_2225956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225956 prefixEnd_2225956 := by exact prefixLift 2225956
  have htrace : WordTrace (prefixWord ++ tailWord_2225956) baseStart_2225956 baseEnd_2225956 := by
    simpa [prefixWord, tailWord_2225956, baseEnd_2225956] using wordTrace_append hprefix tailTrace_2225956
  have hstable : (prefixWord ++ tailWord_2225956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225956).length < 2 ^ (prefixWord ++ tailWord_2225956).sum := by decide
  have hdescent : baseEnd_2225956 < baseStart_2225956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225977 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 2, 3]
def baseStart_2225977 : Nat := 118140960795 + 2225977 * 2 ^ 59
def prefixEnd_2225977 : Nat := 4983230072969 + 3 ^ 40 * 2225977 * 2
def baseEnd_2225977 : Nat := 761997417902228392300283

theorem tailTrace_2225977 : CollatzResearch.WordTrace tailWord_2225977 prefixEnd_2225977 761997417902228392300283 := by
  unfold tailWord_2225977
  simp only [CollatzResearch.WordTrace]
  refine ⟨81188051056672970450100185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54125367371115313633400123 81188051056672970450100185)
  ·
    refine ⟨60891038292504727837575139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81188051056672970450100185 60891038292504727837575139)
    ·
      refine ⟨91336557438757091756362709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60891038292504727837575139 91336557438757091756362709)
      ·
        refine ⟨2140700564970869338039751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 91336557438757091756362709 2140700564970869338039751)
        ·
          refine ⟨3211050847456304007059627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140700564970869338039751 3211050847456304007059627)
          ·
            refine ⟨4816576271184456010589441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3211050847456304007059627 4816576271184456010589441)
            ·
              refine ⟨3612432203388342007942081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4816576271184456010589441 3612432203388342007942081)
              ·
                refine ⟨2709324152541256505956561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3612432203388342007942081 2709324152541256505956561)
                ·
                  refine ⟨2031993114405942379467421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2709324152541256505956561 2031993114405942379467421)
                  ·
                    refine ⟨761997417902228392300283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2031993114405942379467421 761997417902228392300283)
                    ·
                      rfl

theorem cell22_2225977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_2225977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225977 prefixEnd_2225977 := by exact prefixLift 2225977
  have htrace : WordTrace (prefixWord ++ tailWord_2225977) baseStart_2225977 baseEnd_2225977 := by
    simpa [prefixWord, tailWord_2225977, baseEnd_2225977] using wordTrace_append hprefix tailTrace_2225977
  have hstable : (prefixWord ++ tailWord_2225977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225977).length < 2 ^ (prefixWord ++ tailWord_2225977).sum := by decide
  have hdescent : baseEnd_2225977 < baseStart_2225977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225990 : List Nat := [6, 1, 1, 2, 1, 1, 3, 7]
def baseStart_2225990 : Nat := 118140960795 + 2225990 * 2 ^ 59
def prefixEnd_2225990 : Nat := 4983230072969 + 3 ^ 40 * 2225990 * 2
def baseEnd_2225990 : Nat := 84666874229766743525027

theorem tailTrace_2225990 : CollatzResearch.WordTrace tailWord_2225990 prefixEnd_2225990 84666874229766743525027 := by
  unfold tailWord_2225990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537141412675808552197607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54125683470417249113548949 2537141412675808552197607)
  ·
    refine ⟨3805712119013712828296411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2537141412675808552197607 3805712119013712828296411)
    ·
      refine ⟨5708568178520569242444617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3805712119013712828296411 5708568178520569242444617)
      ·
        refine ⟨4281426133890426931833463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5708568178520569242444617 4281426133890426931833463)
        ·
          refine ⟨6422139200835640397750195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4281426133890426931833463 6422139200835640397750195)
          ·
            refine ⟨9633208801253460596625293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6422139200835640397750195 9633208801253460596625293)
            ·
              refine ⟨3612453300470047723734485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9633208801253460596625293 3612453300470047723734485)
              ·
                refine ⟨84666874229766743525027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3612453300470047723734485 84666874229766743525027)
                ·
                  rfl

theorem cell22_2225990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_2225990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2225990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2225990 prefixEnd_2225990 := by exact prefixLift 2225990
  have htrace : WordTrace (prefixWord ++ tailWord_2225990) baseStart_2225990 baseEnd_2225990 := by
    simpa [prefixWord, tailWord_2225990, baseEnd_2225990] using wordTrace_append hprefix tailTrace_2225990
  have hstable : (prefixWord ++ tailWord_2225990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225990).length < 2 ^ (prefixWord ++ tailWord_2225990).sum := by decide
  have hdescent : baseEnd_2225990 < baseStart_2225990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226097 : List Nat := [1, 2, 2, 4, 2, 2, 3, 2, 4]
def baseStart_2226097 : Nat := 118140960795 + 2226097 * 2 ^ 59
def prefixEnd_2226097 : Nat := 4983230072969 + 3 ^ 40 * 2226097 * 2
def baseEnd_2226097 : Nat := 254012832118196026433305

theorem tailTrace_2226097 : CollatzResearch.WordTrace tailWord_2226097 prefixEnd_2226097 254012832118196026433305 := by
  unfold tailWord_2226097
  simp only [CollatzResearch.WordTrace]
  refine ⟨81192427816238230944468545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54128285210825487296312363 81192427816238230944468545)
  ·
    refine ⟨60894320862178673208351409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81192427816238230944468545 60894320862178673208351409)
    ·
      refine ⟨45670740646634004906263557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60894320862178673208351409 45670740646634004906263557)
      ·
        refine ⟨8563263871243875919924417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45670740646634004906263557 8563263871243875919924417)
        ·
          refine ⟨6422447903432906939943313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8563263871243875919924417 6422447903432906939943313)
          ·
            refine ⟨4816835927574680204957485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6422447903432906939943313 4816835927574680204957485)
            ·
              refine ⟨1806313472840505076859057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4816835927574680204957485 1806313472840505076859057)
              ·
                refine ⟨1354735104630378807644293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1806313472840505076859057 1354735104630378807644293)
                ·
                  refine ⟨254012832118196026433305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354735104630378807644293 254012832118196026433305)
                  ·
                    rfl

theorem cell22_2226097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_2226097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226097 prefixEnd_2226097 := by exact prefixLift 2226097
  have htrace : WordTrace (prefixWord ++ tailWord_2226097) baseStart_2226097 baseEnd_2226097 := by
    simpa [prefixWord, tailWord_2226097, baseEnd_2226097] using wordTrace_append hprefix tailTrace_2226097
  have hstable : (prefixWord ++ tailWord_2226097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226097).length < 2 ^ (prefixWord ++ tailWord_2226097).sum := by decide
  have hdescent : baseEnd_2226097 < baseStart_2226097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226106 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_2226106 : Nat := 118140960795 + 2226106 * 2 ^ 59
def prefixEnd_2226106 : Nat := 4983230072969 + 3 ^ 40 * 2226106 * 2
def baseEnd_2226106 : Nat := 762041577238515055824887

theorem tailTrace_2226106 : CollatzResearch.WordTrace tailWord_2226106 prefixEnd_2226106 762041577238515055824887 := by
  unfold tailWord_2226106
  simp only [CollatzResearch.WordTrace]
  refine ⟨20298189018301406370386543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54128504048803750321030781 20298189018301406370386543)
  ·
    refine ⟨30447283527452109555579815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20298189018301406370386543 30447283527452109555579815)
    ·
      refine ⟨45670925291178164333369723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30447283527452109555579815 45670925291178164333369723)
      ·
        refine ⟨68506387936767246500054585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45670925291178164333369723 68506387936767246500054585)
        ·
          refine ⟨51379790952575434875040939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68506387936767246500054585 51379790952575434875040939)
          ·
            refine ⟨77069686428863152312561409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51379790952575434875040939 77069686428863152312561409)
            ·
              refine ⟨57802264821647364234421057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77069686428863152312561409 57802264821647364234421057)
              ·
                refine ⟨43351698616235523175815793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57802264821647364234421057 43351698616235523175815793)
                ·
                  refine ⟨32513773962176642381861845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43351698616235523175815793 32513773962176642381861845)
                  ·
                    refine ⟨762041577238515055824887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32513773962176642381861845 762041577238515055824887)
                    ·
                      rfl

theorem cell22_2226106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_2226106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226106 prefixEnd_2226106 := by exact prefixLift 2226106
  have htrace : WordTrace (prefixWord ++ tailWord_2226106) baseStart_2226106 baseEnd_2226106 := by
    simpa [prefixWord, tailWord_2226106, baseEnd_2226106] using wordTrace_append hprefix tailTrace_2226106
  have hstable : (prefixWord ++ tailWord_2226106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226106).length < 2 ^ (prefixWord ++ tailWord_2226106).sum := by decide
  have hdescent : baseEnd_2226106 < baseStart_2226106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226121 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_2226121 : Nat := 118140960795 + 2226121 * 2 ^ 59
def prefixEnd_2226121 : Nat := 4983230072969 + 3 ^ 40 * 2226121 * 2
def baseEnd_2226121 : Nat := 762046712045060016699841

theorem tailTrace_2226121 : CollatzResearch.WordTrace tailWord_2226121 prefixEnd_2226121 762046712045060016699841 := by
  unfold tailWord_2226121
  simp only [CollatzResearch.WordTrace]
  refine ⟨81193303168151283043342217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54128868778767522028894811 81193303168151283043342217)
  ·
    refine ⟨60894977376113462282506663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81193303168151283043342217 60894977376113462282506663)
    ·
      refine ⟨91342466064170193423759995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60894977376113462282506663 91342466064170193423759995)
      ·
        refine ⟨137013699096255290135639993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91342466064170193423759995 137013699096255290135639993)
        ·
          refine ⟨102760274322191467601729995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137013699096255290135639993 102760274322191467601729995)
          ·
            refine ⟨154140411483287201402594993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102760274322191467601729995 154140411483287201402594993)
            ·
              refine ⟨115605308612465401051946245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154140411483287201402594993 115605308612465401051946245)
              ·
                refine ⟨21675995364837262697239921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115605308612465401051946245 21675995364837262697239921)
                ·
                  refine ⟨16256996523627947022929941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21675995364837262697239921 16256996523627947022929941)
                  ·
                    refine ⟨762046712045060016699841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16256996523627947022929941 762046712045060016699841)
                    ·
                      rfl

theorem cell22_2226121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_2226121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226121 prefixEnd_2226121 := by exact prefixLift 2226121
  have htrace : WordTrace (prefixWord ++ tailWord_2226121) baseStart_2226121 baseEnd_2226121 := by
    simpa [prefixWord, tailWord_2226121, baseEnd_2226121] using wordTrace_append hprefix tailTrace_2226121
  have hstable : (prefixWord ++ tailWord_2226121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226121).length < 2 ^ (prefixWord ++ tailWord_2226121).sum := by decide
  have hdescent : baseEnd_2226121 < baseStart_2226121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226123 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 5, 3]
def baseStart_2226123 : Nat := 118140960795 + 2226123 * 2 ^ 59
def prefixEnd_2226123 : Nat := 4983230072969 + 3 ^ 40 * 2226123 * 2
def baseEnd_2226123 : Nat := 762047396685932678149835

theorem tailTrace_2226123 : CollatzResearch.WordTrace tailWord_2226123 prefixEnd_2226123 762047396685932678149835 := by
  unfold tailWord_2226123
  simp only [CollatzResearch.WordTrace]
  refine ⟨81193376114144037384915023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54128917409429358256610015 81193376114144037384915023)
  ·
    refine ⟨121790064171216056077372535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81193376114144037384915023 121790064171216056077372535)
    ·
      refine ⟨182685096256824084116058803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121790064171216056077372535 182685096256824084116058803)
      ·
        refine ⟨274027644385236126174088205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182685096256824084116058803 274027644385236126174088205)
        ·
          refine ⟨102760366644463547315283077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274027644385236126174088205 102760366644463547315283077)
          ·
            refine ⟨19267568745836915121615577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102760366644463547315283077 19267568745836915121615577)
            ·
              refine ⟨14450676559377686341211683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19267568745836915121615577 14450676559377686341211683)
              ·
                refine ⟨21676014839066529511817525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14450676559377686341211683 21676014839066529511817525)
                ·
                  refine ⟨2032126391162487141732893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21676014839066529511817525 2032126391162487141732893)
                  ·
                    refine ⟨762047396685932678149835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032126391162487141732893 762047396685932678149835)
                    ·
                      rfl

theorem cell22_2226123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 3].length) (baseStart_2226123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226123 prefixEnd_2226123 := by exact prefixLift 2226123
  have htrace : WordTrace (prefixWord ++ tailWord_2226123) baseStart_2226123 baseEnd_2226123 := by
    simpa [prefixWord, tailWord_2226123, baseEnd_2226123] using wordTrace_append hprefix tailTrace_2226123
  have hstable : (prefixWord ++ tailWord_2226123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226123).length < 2 ^ (prefixWord ++ tailWord_2226123).sum := by decide
  have hdescent : baseEnd_2226123 < baseStart_2226123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226200 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_2226200 : Nat := 118140960795 + 2226200 * 2 ^ 59
def prefixEnd_2226200 : Nat := 4983230072969 + 3 ^ 40 * 2226200 * 2
def baseEnd_2226200 : Nat := 762073755359530143974599

theorem tailTrace_2226200 : CollatzResearch.WordTrace tailWord_2226200 prefixEnd_2226200 762073755359530143974599 := by
  unfold tailWord_2226200
  simp only [CollatzResearch.WordTrace]
  refine ⟨40598092267432539767734027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54130789689910053023645369 40598092267432539767734027)
  ·
    refine ⟨60897138401148809651601041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40598092267432539767734027 60897138401148809651601041)
    ·
      refine ⟨45672853800861607238700781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60897138401148809651601041 45672853800861607238700781)
      ·
        refine ⟨17127320175323102714512793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45672853800861607238700781 17127320175323102714512793)
        ·
          refine ⟨12845490131492327035884595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17127320175323102714512793 12845490131492327035884595)
          ·
            refine ⟨19268235197238490553826893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12845490131492327035884595 19268235197238490553826893)
            ·
              refine ⟨7225588198964433957685085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19268235197238490553826893 7225588198964433957685085)
              ·
                refine ⟨2709595574611662734131907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7225588198964433957685085 2709595574611662734131907)
                ·
                  refine ⟨4064393361917494101197861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709595574611662734131907 4064393361917494101197861)
                  ·
                    refine ⟨762073755359530143974599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4064393361917494101197861 762073755359530143974599)
                    ·
                      rfl

theorem cell22_2226200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_2226200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226200 prefixEnd_2226200 := by exact prefixLift 2226200
  have htrace : WordTrace (prefixWord ++ tailWord_2226200) baseStart_2226200 baseEnd_2226200 := by
    simpa [prefixWord, tailWord_2226200, baseEnd_2226200] using wordTrace_append hprefix tailTrace_2226200
  have hstable : (prefixWord ++ tailWord_2226200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226200).length < 2 ^ (prefixWord ++ tailWord_2226200).sum := by decide
  have hdescent : baseEnd_2226200 < baseStart_2226200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226273 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2226273 : Nat := 118140960795 + 2226273 * 2 ^ 59
def prefixEnd_2226273 : Nat := 4983230072969 + 3 ^ 40 * 2226273 * 2
def baseEnd_2226273 : Nat := 762098744751382286899375

theorem tailTrace_2226273 : CollatzResearch.WordTrace tailWord_2226273 prefixEnd_2226273 762098744751382286899375 := by
  unfold tailWord_2226273
  simp only [CollatzResearch.WordTrace]
  refine ⟨81198847063600613002875473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54132564709067075335250315 81198847063600613002875473)
  ·
    refine ⟨60899135297700459752156605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81198847063600613002875473 60899135297700459752156605)
    ·
      refine ⟨22837175736637672407058727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60899135297700459752156605 22837175736637672407058727)
      ·
        refine ⟨34255763604956508610588091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22837175736637672407058727 34255763604956508610588091)
        ·
          refine ⟨51383645407434762915882137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34255763604956508610588091 51383645407434762915882137)
          ·
            refine ⟨38537734055576072186911603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51383645407434762915882137 38537734055576072186911603)
            ·
              refine ⟨57806601083364108280367405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38537734055576072186911603 57806601083364108280367405)
              ·
                refine ⟨21677475406261540605137777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57806601083364108280367405 21677475406261540605137777)
                ·
                  refine ⟨16258106554696155453853333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21677475406261540605137777 16258106554696155453853333)
                  ·
                    refine ⟨762098744751382286899375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16258106554696155453853333 762098744751382286899375)
                    ·
                      rfl

theorem cell22_2226273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2226273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226273 prefixEnd_2226273 := by exact prefixLift 2226273
  have htrace : WordTrace (prefixWord ++ tailWord_2226273) baseStart_2226273 baseEnd_2226273 := by
    simpa [prefixWord, tailWord_2226273, baseEnd_2226273] using wordTrace_append hprefix tailTrace_2226273
  have hstable : (prefixWord ++ tailWord_2226273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226273).length < 2 ^ (prefixWord ++ tailWord_2226273).sum := by decide
  have hdescent : baseEnd_2226273 < baseStart_2226273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226322 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_2226322 : Nat := 118140960795 + 2226322 * 2 ^ 59
def prefixEnd_2226322 : Nat := 4983230072969 + 3 ^ 40 * 2226322 * 2
def baseEnd_2226322 : Nat := 254038506150920830808075

theorem tailTrace_2226322 : CollatzResearch.WordTrace tailWord_2226322 prefixEnd_2226322 254038506150920830808075 := by
  unfold tailWord_2226322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20300158560105773592852305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54133756160282062914272813 20300158560105773592852305)
  ·
    refine ⟨15225118920079330194639229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20300158560105773592852305 15225118920079330194639229)
    ·
      refine ⟨5709419595029748822989711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15225118920079330194639229 5709419595029748822989711)
      ·
        refine ⟨8564129392544623234484567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709419595029748822989711 8564129392544623234484567)
        ·
          refine ⟨12846194088816934851726851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8564129392544623234484567 12846194088816934851726851)
          ·
            refine ⟨19269291133225402277590277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12846194088816934851726851 19269291133225402277590277)
            ·
              refine ⟨3612992087479762927048177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19269291133225402277590277 3612992087479762927048177)
              ·
                refine ⟨2709744065609822195286133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3612992087479762927048177 2709744065609822195286133)
                ·
                  refine ⟨254038506150920830808075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2709744065609822195286133 254038506150920830808075)
                  ·
                    rfl

theorem cell22_2226322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_2226322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226322 prefixEnd_2226322 := by exact prefixLift 2226322
  have htrace : WordTrace (prefixWord ++ tailWord_2226322) baseStart_2226322 baseEnd_2226322 := by
    simpa [prefixWord, tailWord_2226322, baseEnd_2226322] using wordTrace_append hprefix tailTrace_2226322
  have hstable : (prefixWord ++ tailWord_2226322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226322).length < 2 ^ (prefixWord ++ tailWord_2226322).sum := by decide
  have hdescent : baseEnd_2226322 < baseStart_2226322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226397 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2226397 : Nat := 118140960795 + 2226397 * 2 ^ 59
def prefixEnd_2226397 : Nat := 4983230072969 + 3 ^ 40 * 2226397 * 2
def baseEnd_2226397 : Nat := 762141192485487296798995

theorem tailTrace_2226397 : CollatzResearch.WordTrace tailWord_2226397 prefixEnd_2226397 762141192485487296798995 := by
  unfold tailWord_2226397
  simp only [CollatzResearch.WordTrace]
  refine ⟨81203369715151382180389445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54135579810100921453592963 81203369715151382180389445)
  ·
    refine ⟨15225631821590884158823021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81203369715151382180389445 15225631821590884158823021)
    ·
      refine ⟨5709611933096581559558633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15225631821590884158823021 5709611933096581559558633)
      ·
        refine ⟨4282208949822436169668975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5709611933096581559558633 4282208949822436169668975)
        ·
          refine ⟨6423313424733654254503463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282208949822436169668975 6423313424733654254503463)
          ·
            refine ⟨9634970137100481381755195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6423313424733654254503463 9634970137100481381755195)
            ·
              refine ⟨14452455205650722072632793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9634970137100481381755195 14452455205650722072632793)
              ·
                refine ⟨10839341404238041554474595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14452455205650722072632793 10839341404238041554474595)
                ·
                  refine ⟨16259012106357062331711893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10839341404238041554474595 16259012106357062331711893)
                  ·
                    refine ⟨762141192485487296798995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16259012106357062331711893 762141192485487296798995)
                    ·
                      rfl

theorem cell22_2226397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2226397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226397 prefixEnd_2226397 := by exact prefixLift 2226397
  have htrace : WordTrace (prefixWord ++ tailWord_2226397) baseStart_2226397 baseEnd_2226397 := by
    simpa [prefixWord, tailWord_2226397, baseEnd_2226397] using wordTrace_append hprefix tailTrace_2226397
  have hstable : (prefixWord ++ tailWord_2226397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226397).length < 2 ^ (prefixWord ++ tailWord_2226397).sum := by decide
  have hdescent : baseEnd_2226397 < baseStart_2226397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226410 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2226410 : Nat := 118140960795 + 2226410 * 2 ^ 59
def prefixEnd_2226410 : Nat := 4983230072969 + 3 ^ 40 * 2226410 * 2
def baseEnd_2226410 : Nat := 762145642651159596223955

theorem tailTrace_2226410 : CollatzResearch.WordTrace tailWord_2226410 prefixEnd_2226410 762145642651159596223955 := by
  unfold tailWord_2226410
  simp only [CollatzResearch.WordTrace]
  refine ⟨20300960966026071350153171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54135895909402856933741789 20300960966026071350153171)
  ·
    refine ⟨30451441449039107025229757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20300960966026071350153171 30451441449039107025229757)
    ·
      refine ⟨11419290543389665134461159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30451441449039107025229757 11419290543389665134461159)
      ·
        refine ⟨17128935815084497701691739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11419290543389665134461159 17128935815084497701691739)
        ·
          refine ⟨25693403722626746552537609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17128935815084497701691739 25693403722626746552537609)
          ·
            refine ⟨19270052791970059914403207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25693403722626746552537609 19270052791970059914403207)
            ·
              refine ⟨28905079187955089871604811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19270052791970059914403207 28905079187955089871604811)
              ·
                refine ⟨43357618781932634807407217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28905079187955089871604811 43357618781932634807407217)
                ·
                  refine ⟨32518214086449476105555413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43357618781932634807407217 32518214086449476105555413)
                  ·
                    refine ⟨762145642651159596223955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32518214086449476105555413 762145642651159596223955)
                    ·
                      rfl

theorem cell22_2226410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2226410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226410 prefixEnd_2226410 := by exact prefixLift 2226410
  have htrace : WordTrace (prefixWord ++ tailWord_2226410) baseStart_2226410 baseEnd_2226410 := by
    simpa [prefixWord, tailWord_2226410, baseEnd_2226410] using wordTrace_append hprefix tailTrace_2226410
  have hstable : (prefixWord ++ tailWord_2226410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226410).length < 2 ^ (prefixWord ++ tailWord_2226410).sum := by decide
  have hdescent : baseEnd_2226410 < baseStart_2226410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226487 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2226487 : Nat := 118140960795 + 2226487 * 2 ^ 59
def prefixEnd_2226487 : Nat := 4983230072969 + 3 ^ 40 * 2226487 * 2
def baseEnd_2226487 : Nat := 762172001324757062048719

theorem tailTrace_2226487 : CollatzResearch.WordTrace tailWord_2226487 prefixEnd_2226487 762172001324757062048719 := by
  unfold tailWord_2226487
  simp only [CollatzResearch.WordTrace]
  refine ⟨81206652284825327551165715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54137768189883551700777143 81206652284825327551165715)
  ·
    refine ⟨121809978427237991326748573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81206652284825327551165715 121809978427237991326748573)
    ·
      refine ⟨45678741910214246747530715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121809978427237991326748573 45678741910214246747530715)
      ·
        refine ⟨68518112865321370121296073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45678741910214246747530715 68518112865321370121296073)
        ·
          refine ⟨51388584648991027590972055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68518112865321370121296073 51388584648991027590972055)
          ·
            refine ⟨77082876973486541386458083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51388584648991027590972055 77082876973486541386458083)
            ·
              refine ⟨115624315460229812079687125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77082876973486541386458083 115624315460229812079687125)
              ·
                refine ⟨2709944893599136220617667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 115624315460229812079687125 2709944893599136220617667)
                ·
                  refine ⟨4064917340398704330926501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709944893599136220617667 4064917340398704330926501)
                  ·
                    refine ⟨762172001324757062048719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4064917340398704330926501 762172001324757062048719)
                    ·
                      rfl

theorem cell22_2226487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2226487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226487 prefixEnd_2226487 := by exact prefixLift 2226487
  have htrace : WordTrace (prefixWord ++ tailWord_2226487) baseStart_2226487 baseEnd_2226487 := by
    simpa [prefixWord, tailWord_2226487, baseEnd_2226487] using wordTrace_append hprefix tailTrace_2226487
  have hstable : (prefixWord ++ tailWord_2226487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226487).length < 2 ^ (prefixWord ++ tailWord_2226487).sum := by decide
  have hdescent : baseEnd_2226487 < baseStart_2226487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226532 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2226532 : Nat := 118140960795 + 2226532 * 2 ^ 59
def prefixEnd_2226532 : Nat := 4983230072969 + 3 ^ 40 * 2226532 * 2
def baseEnd_2226532 : Nat := 762187405744391944673581

theorem tailTrace_2226532 : CollatzResearch.WordTrace tailWord_2226532 prefixEnd_2226532 762187405744391944673581 := by
  unfold tailWord_2226532
  simp only [CollatzResearch.WordTrace]
  refine ⟨40604146784831150118276925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54138862379774866824369233 40604146784831150118276925)
  ·
    refine ⟨15226555044311681294353847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40604146784831150118276925 15226555044311681294353847)
    ·
      refine ⟨22839832566467521941530771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15226555044311681294353847 22839832566467521941530771)
      ·
        refine ⟨34259748849701282912296157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22839832566467521941530771 34259748849701282912296157)
        ·
          refine ⟨12847405818637981092111059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34259748849701282912296157 12847405818637981092111059)
          ·
            refine ⟨19271108727956971638166589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12847405818637981092111059 19271108727956971638166589)
            ·
              refine ⟨7226665772983864364312471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19271108727956971638166589 7226665772983864364312471)
              ·
                refine ⟨10839998659475796546468707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7226665772983864364312471 10839998659475796546468707)
                ·
                  refine ⟨16259997989213694819703061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10839998659475796546468707 16259997989213694819703061)
                  ·
                    refine ⟨762187405744391944673581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16259997989213694819703061 762187405744391944673581)
                    ·
                      rfl

theorem cell22_2226532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2226532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226532 prefixEnd_2226532 := by exact prefixLift 2226532
  have htrace : WordTrace (prefixWord ++ tailWord_2226532) baseStart_2226532 baseEnd_2226532 := by
    simpa [prefixWord, tailWord_2226532, baseEnd_2226532] using wordTrace_append hprefix tailTrace_2226532
  have hstable : (prefixWord ++ tailWord_2226532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226532).length < 2 ^ (prefixWord ++ tailWord_2226532).sum := by decide
  have hdescent : baseEnd_2226532 < baseStart_2226532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226536 : List Nat := [2, 1, 4, 2, 2, 2, 2, 3, 4]
def baseStart_2226536 : Nat := 118140960795 + 2226536 * 2 ^ 59
def prefixEnd_2226536 : Nat := 4983230072969 + 3 ^ 40 * 2226536 * 2
def baseEnd_2226536 : Nat := 254062925008712422524523

theorem tailTrace_2226536 : CollatzResearch.WordTrace tailWord_2226536 prefixEnd_2226536 254062925008712422524523 := by
  unfold tailWord_2226536
  simp only [CollatzResearch.WordTrace]
  refine ⟨40604219730823904459849731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54138959641098539279799641 40604219730823904459849731)
  ·
    refine ⟨60906329596235856689774597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40604219730823904459849731 60906329596235856689774597)
    ·
      refine ⟨11419936799294223129332737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60906329596235856689774597 11419936799294223129332737)
      ·
        refine ⟨8564952599470667346999553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11419936799294223129332737 8564952599470667346999553)
        ·
          refine ⟨6423714449603000510249665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8564952599470667346999553 6423714449603000510249665)
          ·
            refine ⟨4817785837202250382687249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6423714449603000510249665 4817785837202250382687249)
            ·
              refine ⟨3613339377901687787015437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4817785837202250382687249 3613339377901687787015437)
              ·
                refine ⟨1355002266713132920130789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3613339377901687787015437 1355002266713132920130789)
                ·
                  refine ⟨254062925008712422524523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1355002266713132920130789 254062925008712422524523)
                  ·
                    rfl

theorem cell22_2226536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_2226536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226536 prefixEnd_2226536 := by exact prefixLift 2226536
  have htrace : WordTrace (prefixWord ++ tailWord_2226536) baseStart_2226536 baseEnd_2226536 := by
    simpa [prefixWord, tailWord_2226536, baseEnd_2226536] using wordTrace_append hprefix tailTrace_2226536
  have hstable : (prefixWord ++ tailWord_2226536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226536).length < 2 ^ (prefixWord ++ tailWord_2226536).sum := by decide
  have hdescent : baseEnd_2226536 < baseStart_2226536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226538 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_2226538 : Nat := 118140960795 + 2226538 * 2 ^ 59
def prefixEnd_2226538 : Nat := 4983230072969 + 3 ^ 40 * 2226538 * 2
def baseEnd_2226538 : Nat := 762189459667009929023563

theorem tailTrace_2226538 : CollatzResearch.WordTrace tailWord_2226538 prefixEnd_2226538 762189459667009929023563 := by
  unfold tailWord_2226538
  simp only [CollatzResearch.WordTrace]
  refine ⟨20302128101910140815318067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54139008271760375507514845 20302128101910140815318067)
  ·
    refine ⟨30453192152865211222977101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20302128101910140815318067 30453192152865211222977101)
    ·
      refine ⟨11419947057324454208616413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30453192152865211222977101 11419947057324454208616413)
      ·
        refine ⟨4282480146496670328231155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11419947057324454208616413 4282480146496670328231155)
        ·
          refine ⟨6423720219745005492346733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282480146496670328231155 6423720219745005492346733)
          ·
            refine ⟨2408895082404377059630025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6423720219745005492346733 2408895082404377059630025)
            ·
              refine ⟨1806671311803282794722519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408895082404377059630025 1806671311803282794722519)
              ·
                refine ⟨2710006967704924192083779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806671311803282794722519 2710006967704924192083779)
                ·
                  refine ⟨4065010451557386288125669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710006967704924192083779 4065010451557386288125669)
                  ·
                    refine ⟨762189459667009929023563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065010451557386288125669 762189459667009929023563)
                    ·
                      rfl

theorem cell22_2226538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_2226538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226538 prefixEnd_2226538 := by exact prefixLift 2226538
  have htrace : WordTrace (prefixWord ++ tailWord_2226538) baseStart_2226538 baseEnd_2226538 := by
    simpa [prefixWord, tailWord_2226538, baseEnd_2226538] using wordTrace_append hprefix tailTrace_2226538
  have hstable : (prefixWord ++ tailWord_2226538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226538).length < 2 ^ (prefixWord ++ tailWord_2226538).sum := by decide
  have hdescent : baseEnd_2226538 < baseStart_2226538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226592 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 7]
def baseStart_2226592 : Nat := 118140960795 + 2226592 * 2 ^ 59
def prefixEnd_2226592 : Nat := 4983230072969 + 3 ^ 40 * 2226592 * 2
def baseEnd_2226592 : Nat := 254069314990190596057799

theorem tailTrace_2226592 : CollatzResearch.WordTrace tailWord_2226592 prefixEnd_2226592 254069314990190596057799 := by
  unfold tailWord_2226592
  simp only [CollatzResearch.WordTrace]
  refine ⟨40605240974722465241869015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54140321299629953655825353 40605240974722465241869015)
  ·
    refine ⟨60907861462083697862803523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40605240974722465241869015 60907861462083697862803523)
    ·
      refine ⟨91361792193125546794205285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60907861462083697862803523 91361792193125546794205285)
      ·
        refine ⟨17130336036211040023913491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91361792193125546794205285 17130336036211040023913491)
        ·
          refine ⟨25695504054316560035870237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17130336036211040023913491 25695504054316560035870237)
          ·
            refine ⟨9635814020368710013451339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25695504054316560035870237 9635814020368710013451339)
            ·
              refine ⟨14453721030553065020177009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9635814020368710013451339 14453721030553065020177009)
              ·
                refine ⟨10840290772914798765132757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14453721030553065020177009 10840290772914798765132757)
                ·
                  refine ⟨254069314990190596057799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10840290772914798765132757 254069314990190596057799)
                  ·
                    rfl

theorem cell22_2226592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_2226592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226592 prefixEnd_2226592 := by exact prefixLift 2226592
  have htrace : WordTrace (prefixWord ++ tailWord_2226592) baseStart_2226592 baseEnd_2226592 := by
    simpa [prefixWord, tailWord_2226592, baseEnd_2226592] using wordTrace_append hprefix tailTrace_2226592
  have hstable : (prefixWord ++ tailWord_2226592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226592).length < 2 ^ (prefixWord ++ tailWord_2226592).sum := by decide
  have hdescent : baseEnd_2226592 < baseStart_2226592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226613 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2226613 : Nat := 118140960795 + 2226613 * 2 ^ 59
def prefixEnd_2226613 : Nat := 4983230072969 + 3 ^ 40 * 2226613 * 2
def baseEnd_2226613 : Nat := 762215133699734733398333

theorem tailTrace_2226613 : CollatzResearch.WordTrace tailWord_2226613 prefixEnd_2226613 762215133699734733398333 := by
  unfold tailWord_2226613
  simp only [CollatzResearch.WordTrace]
  refine ⟨81211247882368851070252493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54140831921579234046834995 81211247882368851070252493)
  ·
    refine ⟨30454217955888319151344685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81211247882368851070252493 30454217955888319151344685)
    ·
      refine ⟨11420331733458119681754257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30454217955888319151344685 11420331733458119681754257)
      ·
        refine ⟨8565248800093589761315693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11420331733458119681754257 8565248800093589761315693)
        ·
          refine ⟨3211968300035096160493385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8565248800093589761315693 3211968300035096160493385)
          ·
            refine ⟨2408976225026322120370039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3211968300035096160493385 2408976225026322120370039)
            ·
              refine ⟨3613464337539483180555059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408976225026322120370039 3613464337539483180555059)
              ·
                refine ⟨5420196506309224770832589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613464337539483180555059 5420196506309224770832589)
                ·
                  refine ⟨2032573689865959289062221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5420196506309224770832589 2032573689865959289062221)
                  ·
                    refine ⟨762215133699734733398333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032573689865959289062221 762215133699734733398333)
                    ·
                      rfl

theorem cell22_2226613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2226613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226613 prefixEnd_2226613 := by exact prefixLift 2226613
  have htrace : WordTrace (prefixWord ++ tailWord_2226613) baseStart_2226613 baseEnd_2226613 := by
    simpa [prefixWord, tailWord_2226613, baseEnd_2226613] using wordTrace_append hprefix tailTrace_2226613
  have hstable : (prefixWord ++ tailWord_2226613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226613).length < 2 ^ (prefixWord ++ tailWord_2226613).sum := by decide
  have hdescent : baseEnd_2226613 < baseStart_2226613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226656 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 1, 4]
def baseStart_2226656 : Nat := 118140960795 + 2226656 * 2 ^ 59
def prefixEnd_2226656 : Nat := 4983230072969 + 3 ^ 40 * 2226656 * 2
def baseEnd_2226656 : Nat := 762229853478496954573201

theorem tailTrace_2226656 : CollatzResearch.WordTrace tailWord_2226656 prefixEnd_2226656 762229853478496954573201 := by
  unfold tailWord_2226656
  simp only [CollatzResearch.WordTrace]
  refine ⟨40606408110606534707033911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54141877480808712942711881 40606408110606534707033911)
  ·
    refine ⟨60909612165909802060550867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40606408110606534707033911 60909612165909802060550867)
    ·
      refine ⟨91364418248864703090826301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60909612165909802060550867 91364418248864703090826301)
      ·
        refine ⟨34261656843324263659059863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91364418248864703090826301 34261656843324263659059863)
        ·
          refine ⟨51392485264986395488589795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34261656843324263659059863 51392485264986395488589795)
          ·
            refine ⟨77088727897479593232884693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51392485264986395488589795 77088727897479593232884693)
            ·
              refine ⟨1806767060097177966395735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 77088727897479593232884693 1806767060097177966395735)
              ·
                refine ⟨2710150590145766949593603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806767060097177966395735 2710150590145766949593603)
                ·
                  refine ⟨4065225885218650424390405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710150590145766949593603 4065225885218650424390405)
                  ·
                    refine ⟨762229853478496954573201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065225885218650424390405 762229853478496954573201)
                    ·
                      rfl

theorem cell22_2226656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_2226656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226656 prefixEnd_2226656 := by exact prefixLift 2226656
  have htrace : WordTrace (prefixWord ++ tailWord_2226656) baseStart_2226656 baseEnd_2226656 := by
    simpa [prefixWord, tailWord_2226656, baseEnd_2226656] using wordTrace_append hprefix tailTrace_2226656
  have hstable : (prefixWord ++ tailWord_2226656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226656).length < 2 ^ (prefixWord ++ tailWord_2226656).sum := by decide
  have hdescent : baseEnd_2226656 < baseStart_2226656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226682 : List Nat := [3, 1, 1, 1, 1, 2, 2, 11]
def baseStart_2226682 : Nat := 118140960795 + 2226682 * 2 ^ 59
def prefixEnd_2226682 : Nat := 4983230072969 + 3 ^ 40 * 2226682 * 2
def baseEnd_2226682 : Nat := 84693194867760172602569

theorem tailTrace_2226682 : CollatzResearch.WordTrace tailWord_2226682 prefixEnd_2226682 84693194867760172602569 := by
  unfold tailWord_2226682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303441129779718963628575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54142509679412583903009533 20303441129779718963628575)
  ·
    refine ⟨30455161694669578445442863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20303441129779718963628575 30455161694669578445442863)
    ·
      refine ⟨45682742542004367668164295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30455161694669578445442863 45682742542004367668164295)
      ·
        refine ⟨68524113813006551502246443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45682742542004367668164295 68524113813006551502246443)
        ·
          refine ⟨102786170719509827253369665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68524113813006551502246443 102786170719509827253369665)
          ·
            refine ⟨77089628039632370440027249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102786170719509827253369665 77089628039632370440027249)
            ·
              refine ⟨57817221029724277830020437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77089628039632370440027249 57817221029724277830020437)
              ·
                refine ⟨84693194867760172602569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 57817221029724277830020437 84693194867760172602569)
                ·
                  rfl

theorem cell22_2226682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_2226682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226682 prefixEnd_2226682 := by exact prefixLift 2226682
  have htrace : WordTrace (prefixWord ++ tailWord_2226682) baseStart_2226682 baseEnd_2226682 := by
    simpa [prefixWord, tailWord_2226682, baseEnd_2226682] using wordTrace_append hprefix tailTrace_2226682
  have hstable : (prefixWord ++ tailWord_2226682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226682).length < 2 ^ (prefixWord ++ tailWord_2226682).sum := by decide
  have hdescent : baseEnd_2226682 < baseStart_2226682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226697 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_2226697 : Nat := 118140960795 + 2226697 * 2 ^ 59
def prefixEnd_2226697 : Nat := 4983230072969 + 3 ^ 40 * 2226697 * 2
def baseEnd_2226697 : Nat := 762243888616386514298075

theorem tailTrace_2226697 : CollatzResearch.WordTrace tailWord_2226697 prefixEnd_2226697 762243888616386514298075 := by
  unfold tailWord_2226697
  simp only [CollatzResearch.WordTrace]
  refine ⟨81214311614064533416310345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54142874409376355610873563 81214311614064533416310345)
  ·
    refine ⟨60910733710548400062232759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81214311614064533416310345 60910733710548400062232759)
    ·
      refine ⟨91366100565822600093349139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60910733710548400062232759 91366100565822600093349139)
      ·
        refine ⟨137049150848733900140023709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91366100565822600093349139 137049150848733900140023709)
        ·
          refine ⟨51393431568275212552508891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137049150848733900140023709 51393431568275212552508891)
          ·
            refine ⟨77090147352412818828763337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51393431568275212552508891 77090147352412818828763337)
            ·
              refine ⟨57817610514309614121572503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77090147352412818828763337 57817610514309614121572503)
              ·
                refine ⟨86726415771464421182358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57817610514309614121572503 86726415771464421182358755)
                ·
                  refine ⟨130089623657196631773538133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86726415771464421182358755 130089623657196631773538133)
                  ·
                    refine ⟨762243888616386514298075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130089623657196631773538133 762243888616386514298075)
                    ·
                      rfl

theorem cell22_2226697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_2226697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226697 prefixEnd_2226697 := by exact prefixLift 2226697
  have htrace : WordTrace (prefixWord ++ tailWord_2226697) baseStart_2226697 baseEnd_2226697 := by
    simpa [prefixWord, tailWord_2226697, baseEnd_2226697] using wordTrace_append hprefix tailTrace_2226697
  have hstable : (prefixWord ++ tailWord_2226697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226697).length < 2 ^ (prefixWord ++ tailWord_2226697).sum := by decide
  have hdescent : baseEnd_2226697 < baseStart_2226697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226720 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 2, 3]
def baseStart_2226720 : Nat := 118140960795 + 2226720 * 2 ^ 59
def prefixEnd_2226720 : Nat := 4983230072969 + 3 ^ 40 * 2226720 * 2
def baseEnd_2226720 : Nat := 762251761986422120973005

theorem tailTrace_2226720 : CollatzResearch.WordTrace tailWord_2226720 prefixEnd_2226720 762251761986422120973005 := by
  unfold tailWord_2226720
  simp only [CollatzResearch.WordTrace]
  refine ⟨40607575246490604172198807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54143433661987472229598409 40607575246490604172198807)
  ·
    refine ⟨60911362869735906258298211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40607575246490604172198807 60911362869735906258298211)
    ·
      refine ⟨91367044304603859387447317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60911362869735906258298211 91367044304603859387447317)
      ·
        refine ⟨4282830201778305908786593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91367044304603859387447317 4282830201778305908786593)
        ·
          refine ⟨3212122651333729431589945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4282830201778305908786593 3212122651333729431589945)
          ·
            refine ⟨2409091988500297073692459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3212122651333729431589945 2409091988500297073692459)
            ·
              refine ⟨3613637982750445610538689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409091988500297073692459 3613637982750445610538689)
              ·
                refine ⟨2710228487062834207904017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3613637982750445610538689 2710228487062834207904017)
                ·
                  refine ⟨2032671365297125655928013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710228487062834207904017 2032671365297125655928013)
                  ·
                    refine ⟨762251761986422120973005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032671365297125655928013 762251761986422120973005)
                    ·
                      rfl

theorem cell22_2226720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_2226720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226720 prefixEnd_2226720 := by exact prefixLift 2226720
  have htrace : WordTrace (prefixWord ++ tailWord_2226720) baseStart_2226720 baseEnd_2226720 := by
    simpa [prefixWord, tailWord_2226720, baseEnd_2226720] using wordTrace_append hprefix tailTrace_2226720
  have hstable : (prefixWord ++ tailWord_2226720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226720).length < 2 ^ (prefixWord ++ tailWord_2226720).sum := by decide
  have hdescent : baseEnd_2226720 < baseStart_2226720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226750 : List Nat := [4, 2, 1, 4, 1, 2, 2, 6]
def baseStart_2226750 : Nat := 118140960795 + 2226750 * 2 ^ 59
def prefixEnd_2226750 : Nat := 4983230072969 + 3 ^ 40 * 2226750 * 2
def baseEnd_2226750 : Nat := 84695781288834671413657

theorem tailTrace_2226750 : CollatzResearch.WordTrace tailWord_2226750 prefixEnd_2226750 84695781288834671413657 := by
  unfold tailWord_2226750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10152030585359065433498713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54144163121915015645326469 10152030585359065433498713)
  ·
    refine ⟨7614022939019299075124035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10152030585359065433498713 7614022939019299075124035)
    ·
      refine ⟨11421034408528948612686053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7614022939019299075124035 11421034408528948612686053)
      ·
        refine ⟨2141443951599177864878635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11421034408528948612686053 2141443951599177864878635)
        ·
          refine ⟨3212165927398766797317953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141443951599177864878635 3212165927398766797317953)
          ·
            refine ⟨2409124445549075097988465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3212165927398766797317953 2409124445549075097988465)
            ·
              refine ⟨1806843334161806323491349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2409124445549075097988465 1806843334161806323491349)
              ·
                refine ⟨84695781288834671413657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1806843334161806323491349 84695781288834671413657)
                ·
                  rfl

theorem cell22_2226750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_2226750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226750 prefixEnd_2226750 := by exact prefixLift 2226750
  have htrace : WordTrace (prefixWord ++ tailWord_2226750) baseStart_2226750 baseEnd_2226750 := by
    simpa [prefixWord, tailWord_2226750, baseEnd_2226750] using wordTrace_append hprefix tailTrace_2226750
  have hstable : (prefixWord ++ tailWord_2226750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226750).length < 2 ^ (prefixWord ++ tailWord_2226750).sum := by decide
  have hdescent : baseEnd_2226750 < baseStart_2226750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226819 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 1, 6]
def baseStart_2226819 : Nat := 118140960795 + 2226819 * 2 ^ 59
def prefixEnd_2226819 : Nat := 4983230072969 + 3 ^ 40 * 2226819 * 2
def baseEnd_2226819 : Nat := 762285651709618862747701

theorem tailTrace_2226819 : CollatzResearch.WordTrace tailWord_2226819 prefixEnd_2226819 762285651709618862747701 := by
  unfold tailWord_2226819
  simp only [CollatzResearch.WordTrace]
  refine ⟨81218761319622548252251511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54145840879748365501501007 81218761319622548252251511)
  ·
    refine ⟨121828141979433822378377267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81218761319622548252251511 121828141979433822378377267)
    ·
      refine ⟨182742212969150733567565901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121828141979433822378377267 182742212969150733567565901)
      ·
        refine ⟨68528329863431525087837213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182742212969150733567565901 68528329863431525087837213)
        ·
          refine ⟨25698123698786821907938955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68528329863431525087837213 25698123698786821907938955)
          ·
            refine ⟨38547185548180232861908433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25698123698786821907938955 38547185548180232861908433)
            ·
              refine ⟨28910389161135174646431325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38547185548180232861908433 28910389161135174646431325)
              ·
                refine ⟨10841395935425690492411747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28910389161135174646431325 10841395935425690492411747)
                ·
                  refine ⟨16262093903138535738617621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10841395935425690492411747 16262093903138535738617621)
                  ·
                    refine ⟨762285651709618862747701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16262093903138535738617621 762285651709618862747701)
                    ·
                      rfl

theorem cell22_2226819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_2226819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226819 prefixEnd_2226819 := by exact prefixLift 2226819
  have htrace : WordTrace (prefixWord ++ tailWord_2226819) baseStart_2226819 baseEnd_2226819 := by
    simpa [prefixWord, tailWord_2226819, baseEnd_2226819] using wordTrace_append hprefix tailTrace_2226819
  have hstable : (prefixWord ++ tailWord_2226819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226819).length < 2 ^ (prefixWord ++ tailWord_2226819).sum := by decide
  have hdescent : baseEnd_2226819 < baseStart_2226819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226821 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_2226821 : Nat := 118140960795 + 2226821 * 2 ^ 59
def prefixEnd_2226821 : Nat := 4983230072969 + 3 ^ 40 * 2226821 * 2
def baseEnd_2226821 : Nat := 762286336350491524197695

theorem tailTrace_2226821 : CollatzResearch.WordTrace tailWord_2226821 prefixEnd_2226821 762286336350491524197695 := by
  unfold tailWord_2226821
  simp only [CollatzResearch.WordTrace]
  refine ⟨81218834265615302593824317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54145889510410201729216211 81218834265615302593824317)
  ·
    refine ⟨30457062849605738472684119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81218834265615302593824317 30457062849605738472684119)
    ·
      refine ⟨45685594274408607709026179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30457062849605738472684119 45685594274408607709026179)
      ·
        refine ⟨68528391411612911563539269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45685594274408607709026179 68528391411612911563539269)
        ·
          refine ⟨12849073389677420918163613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68528391411612911563539269 12849073389677420918163613)
          ·
            refine ⟨4818402521129032844311355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12849073389677420918163613 4818402521129032844311355)
            ·
              refine ⟨7227603781693549266467033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818402521129032844311355 7227603781693549266467033)
              ·
                refine ⟨5420702836270161949850275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7227603781693549266467033 5420702836270161949850275)
                ·
                  refine ⟨8131054254405242924775413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5420702836270161949850275 8131054254405242924775413)
                  ·
                    refine ⟨762286336350491524197695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8131054254405242924775413 762286336350491524197695)
                    ·
                      rfl

theorem cell22_2226821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_2226821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226821 prefixEnd_2226821 := by exact prefixLift 2226821
  have htrace : WordTrace (prefixWord ++ tailWord_2226821) baseStart_2226821 baseEnd_2226821 := by
    simpa [prefixWord, tailWord_2226821, baseEnd_2226821] using wordTrace_append hprefix tailTrace_2226821
  have hstable : (prefixWord ++ tailWord_2226821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226821).length < 2 ^ (prefixWord ++ tailWord_2226821).sum := by decide
  have hdescent : baseEnd_2226821 < baseStart_2226821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226855 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2226855 : Nat := 118140960795 + 2226855 * 2 ^ 59
def prefixEnd_2226855 : Nat := 4983230072969 + 3 ^ 40 * 2226855 * 2
def baseEnd_2226855 : Nat := 762297975245326768847591

theorem tailTrace_2226855 : CollatzResearch.WordTrace tailWord_2226855 prefixEnd_2226855 762297975245326768847591 := by
  unfold tailWord_2226855
  simp only [CollatzResearch.WordTrace]
  refine ⟨81220074347492126400562019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54146716231661417600374679 81220074347492126400562019)
  ·
    refine ⟨121830111521238189600843029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81220074347492126400562019 121830111521238189600843029)
    ·
      refine ⟨5710786477558040137539517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121830111521238189600843029 5710786477558040137539517)
      ·
        refine ⟨2141544929084265051577319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5710786477558040137539517 2141544929084265051577319)
        ·
          refine ⟨3212317393626397577365979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141544929084265051577319 3212317393626397577365979)
          ·
            refine ⟨4818476090439596366048969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212317393626397577365979 4818476090439596366048969)
            ·
              refine ⟨3613857067829697274536727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4818476090439596366048969 3613857067829697274536727)
              ·
                refine ⟨5420785601744545911805091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613857067829697274536727 5420785601744545911805091)
                ·
                  refine ⟨8131178402616818867707637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5420785601744545911805091 8131178402616818867707637)
                  ·
                    refine ⟨762297975245326768847591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8131178402616818867707637 762297975245326768847591)
                    ·
                      rfl

theorem cell22_2226855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2226855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226855 prefixEnd_2226855 := by exact prefixLift 2226855
  have htrace : WordTrace (prefixWord ++ tailWord_2226855) baseStart_2226855 baseEnd_2226855 := by
    simpa [prefixWord, tailWord_2226855, baseEnd_2226855] using wordTrace_append hprefix tailTrace_2226855
  have hstable : (prefixWord ++ tailWord_2226855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226855).length < 2 ^ (prefixWord ++ tailWord_2226855).sum := by decide
  have hdescent : baseEnd_2226855 < baseStart_2226855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226864 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_2226864 : Nat := 118140960795 + 2226864 * 2 ^ 59
def prefixEnd_2226864 : Nat := 4983230072969 + 3 ^ 40 * 2226864 * 2
def baseEnd_2226864 : Nat := 762301056129253745372563

theorem tailTrace_2226864 : CollatzResearch.WordTrace tailWord_2226864 prefixEnd_2226864 762301056129253745372563 := by
  unfold tailWord_2226864
  simp only [CollatzResearch.WordTrace]
  refine ⟨40610201302229760468819823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54146935069639680625093097 40610201302229760468819823)
  ·
    refine ⟨60915301953344640703229735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40610201302229760468819823 60915301953344640703229735)
    ·
      refine ⟨91372952930016961054844603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60915301953344640703229735 91372952930016961054844603)
      ·
        refine ⟨137059429395025441582266905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91372952930016961054844603 137059429395025441582266905)
        ·
          refine ⟨102794572046269081186700179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137059429395025441582266905 102794572046269081186700179)
          ·
            refine ⟨154191858069403621780050269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102794572046269081186700179 154191858069403621780050269)
            ·
              refine ⟨57821946776026358167518851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154191858069403621780050269 57821946776026358167518851)
              ·
                refine ⟨86732920164039537251278277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57821946776026358167518851 86732920164039537251278277)
                ·
                  refine ⟨16262422530757413234614677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86732920164039537251278277 16262422530757413234614677)
                  ·
                    refine ⟨762301056129253745372563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16262422530757413234614677 762301056129253745372563)
                    ·
                      rfl

theorem cell22_2226864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_2226864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226864 prefixEnd_2226864 := by exact prefixLift 2226864
  have htrace : WordTrace (prefixWord ++ tailWord_2226864) baseStart_2226864 baseEnd_2226864 := by
    simpa [prefixWord, tailWord_2226864, baseEnd_2226864] using wordTrace_append hprefix tailTrace_2226864
  have hstable : (prefixWord ++ tailWord_2226864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226864).length < 2 ^ (prefixWord ++ tailWord_2226864).sum := by decide
  have hdescent : baseEnd_2226864 < baseStart_2226864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226870 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2226870 : Nat := 118140960795 + 2226870 * 2 ^ 59
def prefixEnd_2226870 : Nat := 4983230072969 + 3 ^ 40 * 2226870 * 2
def baseEnd_2226870 : Nat := 762303110051871729722545

theorem tailTrace_2226870 : CollatzResearch.WordTrace tailWord_2226870 prefixEnd_2226870 762303110051871729722545 := by
  unfold tailWord_2226870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5076288840152361497647379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54147080961625189308238709 5076288840152361497647379)
  ·
    refine ⟨7614433260228542246471069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5076288840152361497647379 7614433260228542246471069)
    ·
      refine ⟨2855412472585703342426651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7614433260228542246471069 2855412472585703342426651)
      ·
        refine ⟨4283118708878555013639977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855412472585703342426651 4283118708878555013639977)
        ·
          refine ⟨3212339031658916260229983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4283118708878555013639977 3212339031658916260229983)
          ·
            refine ⟨4818508547488374390344975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212339031658916260229983 4818508547488374390344975)
            ·
              refine ⟨7227762821232561585517463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818508547488374390344975 7227762821232561585517463)
              ·
                refine ⟨10841644231848842378276195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7227762821232561585517463 10841644231848842378276195)
                ·
                  refine ⟨16262466347773263567414293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10841644231848842378276195 16262466347773263567414293)
                  ·
                    refine ⟨762303110051871729722545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16262466347773263567414293 762303110051871729722545)
                    ·
                      rfl

theorem cell22_2226870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2226870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226870 prefixEnd_2226870 := by exact prefixLift 2226870
  have htrace : WordTrace (prefixWord ++ tailWord_2226870) baseStart_2226870 baseEnd_2226870 := by
    simpa [prefixWord, tailWord_2226870, baseEnd_2226870] using wordTrace_append hprefix tailTrace_2226870
  have hstable : (prefixWord ++ tailWord_2226870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226870).length < 2 ^ (prefixWord ++ tailWord_2226870).sum := by decide
  have hdescent : baseEnd_2226870 < baseStart_2226870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226911 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 2, 5]
def baseStart_2226911 : Nat := 118140960795 + 2226911 * 2 ^ 59
def prefixEnd_2226911 : Nat := 4983230072969 + 3 ^ 40 * 2226911 * 2
def baseEnd_2226911 : Nat := 762317145189761289447419

theorem tailTrace_2226911 : CollatzResearch.WordTrace tailWord_2226911 prefixEnd_2226911 762317145189761289447419 := by
  unfold tailWord_2226911
  simp only [CollatzResearch.WordTrace]
  refine ⟨81222116835289247964600587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54148077890192831976400391 81222116835289247964600587)
  ·
    refine ⟨121833175252933871946900881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81222116835289247964600587 121833175252933871946900881)
    ·
      refine ⟨91374881439700403960175661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121833175252933871946900881 91374881439700403960175661)
      ·
        refine ⟨34265580539887651485065873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91374881439700403960175661 34265580539887651485065873)
        ·
          refine ⟨25699185404915738613799405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34265580539887651485065873 25699185404915738613799405)
          ·
            refine ⟨9637194526843401980174777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25699185404915738613799405 9637194526843401980174777)
            ·
              refine ⟨7227895895132551485131083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9637194526843401980174777 7227895895132551485131083)
              ·
                refine ⟨10841843842698827227696625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7227895895132551485131083 10841843842698827227696625)
                ·
                  refine ⟨8131382882024120420772469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10841843842698827227696625 8131382882024120420772469)
                  ·
                    refine ⟨762317145189761289447419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8131382882024120420772469 762317145189761289447419)
                    ·
                      rfl

theorem cell22_2226911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_2226911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226911 prefixEnd_2226911 := by exact prefixLift 2226911
  have htrace : WordTrace (prefixWord ++ tailWord_2226911) baseStart_2226911 baseEnd_2226911 := by
    simpa [prefixWord, tailWord_2226911, baseEnd_2226911] using wordTrace_append hprefix tailTrace_2226911
  have hstable : (prefixWord ++ tailWord_2226911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226911).length < 2 ^ (prefixWord ++ tailWord_2226911).sum := by decide
  have hdescent : baseEnd_2226911 < baseStart_2226911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226988 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_2226988 : Nat := 118140960795 + 2226988 * 2 ^ 59
def prefixEnd_2226988 : Nat := 4983230072969 + 3 ^ 40 * 2226988 * 2
def baseEnd_2226988 : Nat := 762343503863358755272183

theorem tailTrace_2226988 : CollatzResearch.WordTrace tailWord_2226988 prefixEnd_2226988 762343503863358755272183 := by
  unfold tailWord_2226988
  simp only [CollatzResearch.WordTrace]
  refine ⟨40612462628005145057576809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54149950170673526743435745 40612462628005145057576809)
  ·
    refine ⟨30459346971003858793182607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40612462628005145057576809 30459346971003858793182607)
    ·
      refine ⟨45689020456505788189773911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30459346971003858793182607 45689020456505788189773911)
      ·
        refine ⟨68533530684758682284660867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45689020456505788189773911 68533530684758682284660867)
        ·
          refine ⟨102800296027138023426991301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68533530684758682284660867 102800296027138023426991301)
          ·
            refine ⟨19275055505088379392560869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102800296027138023426991301 19275055505088379392560869)
            ·
              refine ⟨3614072907204071136105163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19275055505088379392560869 3614072907204071136105163)
              ·
                refine ⟨5421109360806106704157745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3614072907204071136105163 5421109360806106704157745)
                ·
                  refine ⟨4065832020604580028118309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5421109360806106704157745 4065832020604580028118309)
                  ·
                    refine ⟨762343503863358755272183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4065832020604580028118309 762343503863358755272183)
                    ·
                      rfl

theorem cell22_2226988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_2226988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226988 prefixEnd_2226988 := by exact prefixLift 2226988
  have htrace : WordTrace (prefixWord ++ tailWord_2226988) baseStart_2226988 baseEnd_2226988 := by
    simpa [prefixWord, tailWord_2226988, baseEnd_2226988] using wordTrace_append hprefix tailTrace_2226988
  have hstable : (prefixWord ++ tailWord_2226988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226988).length < 2 ^ (prefixWord ++ tailWord_2226988).sum := by decide
  have hdescent : baseEnd_2226988 < baseStart_2226988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2226990 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2226990 : Nat := 118140960795 + 2226990 * 2 ^ 59
def prefixEnd_2226990 : Nat := 4983230072969 + 3 ^ 40 * 2226990 * 2
def baseEnd_2226990 : Nat := 762344188504231416722177

theorem tailTrace_2226990 : CollatzResearch.WordTrace tailWord_2226990 prefixEnd_2226990 762344188504231416722177 := by
  unfold tailWord_2226990
  simp only [CollatzResearch.WordTrace]
  refine ⟨10153124775250380557090803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54149998801335362971150949 10153124775250380557090803)
  ·
    refine ⟨15229687162875570835636205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10153124775250380557090803 15229687162875570835636205)
    ·
      refine ⟨5711132686078339063363577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15229687162875570835636205 5711132686078339063363577)
      ·
        refine ⟨4283349514558754297522683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5711132686078339063363577 4283349514558754297522683)
        ·
          refine ⟨6425024271838131446284025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283349514558754297522683 6425024271838131446284025)
          ·
            refine ⟨4818768203878598584713019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6425024271838131446284025 4818768203878598584713019)
            ·
              refine ⟨7228152305817897877069529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818768203878598584713019 7228152305817897877069529)
              ·
                refine ⟨5421114229363423407802147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7228152305817897877069529 5421114229363423407802147)
                ·
                  refine ⟨8131671344045135111703221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421114229363423407802147 8131671344045135111703221)
                  ·
                    refine ⟨762344188504231416722177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8131671344045135111703221 762344188504231416722177)
                    ·
                      rfl

theorem cell22_2226990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2226990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2226990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2226990 prefixEnd_2226990 := by exact prefixLift 2226990
  have htrace : WordTrace (prefixWord ++ tailWord_2226990) baseStart_2226990 baseEnd_2226990 := by
    simpa [prefixWord, tailWord_2226990, baseEnd_2226990] using wordTrace_append hprefix tailTrace_2226990
  have hstable : (prefixWord ++ tailWord_2226990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2226990).length < 2 ^ (prefixWord ++ tailWord_2226990).sum := by decide
  have hdescent : baseEnd_2226990 < baseStart_2226990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2226990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227016 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2227016 : Nat := 118140960795 + 2227016 * 2 ^ 59
def prefixEnd_2227016 : Nat := 4983230072969 + 3 ^ 40 * 2227016 * 2
def baseEnd_2227016 : Nat := 762353088835576015572097

theorem tailTrace_2227016 : CollatzResearch.WordTrace tailWord_2227016 prefixEnd_2227016 762353088835576015572097 := by
  unfold tailWord_2227016
  simp only [CollatzResearch.WordTrace]
  refine ⟨40612973249954425448586451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54150630999939233931448601 40612973249954425448586451)
  ·
    refine ⟨60919459874931638172879677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40612973249954425448586451 60919459874931638172879677)
    ·
      refine ⟨22844797453099364314829879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60919459874931638172879677 22844797453099364314829879)
      ·
        refine ⟨34267196179649046472244819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22844797453099364314829879 34267196179649046472244819)
        ·
          refine ⟨51400794269473569708367229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34267196179649046472244819 51400794269473569708367229)
          ·
            refine ⟨19275297851052588640637711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51400794269473569708367229 19275297851052588640637711)
            ·
              refine ⟨28912946776578882960956567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19275297851052588640637711 28912946776578882960956567)
              ·
                refine ⟨43369420164868324441434851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28912946776578882960956567 43369420164868324441434851)
                ·
                  refine ⟨65054130247302486662152277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43369420164868324441434851 65054130247302486662152277)
                  ·
                    refine ⟨762353088835576015572097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65054130247302486662152277 762353088835576015572097)
                    ·
                      rfl

theorem cell22_2227016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2227016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227016 prefixEnd_2227016 := by exact prefixLift 2227016
  have htrace : WordTrace (prefixWord ++ tailWord_2227016) baseStart_2227016 baseEnd_2227016 := by
    simpa [prefixWord, tailWord_2227016, baseEnd_2227016] using wordTrace_append hprefix tailTrace_2227016
  have hstable : (prefixWord ++ tailWord_2227016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227016).length < 2 ^ (prefixWord ++ tailWord_2227016).sum := by decide
  have hdescent : baseEnd_2227016 < baseStart_2227016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227052 : List Nat := [2, 2, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_2227052 : Nat := 118140960795 + 2227052 * 2 ^ 59
def prefixEnd_2227052 : Nat := 4983230072969 + 3 ^ 40 * 2227052 * 2
def baseEnd_2227052 : Nat := 762365412371283921671987

theorem tailTrace_2227052 : CollatzResearch.WordTrace tailWord_2227052 prefixEnd_2227052 762365412371283921671987 := by
  unfold tailWord_2227052
  simp only [CollatzResearch.WordTrace]
  refine ⟨40613629763889214522741705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54151506351852286030322273 40613629763889214522741705)
  ·
    refine ⟨30460222322916910892056279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40613629763889214522741705 30460222322916910892056279)
    ·
      refine ⟨45690333484375366338084419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30460222322916910892056279 45690333484375366338084419)
      ·
        refine ⟨68535500226563049507126629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45690333484375366338084419 68535500226563049507126629)
        ·
          refine ⟨12850406292480571782586243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68535500226563049507126629 12850406292480571782586243)
          ·
            refine ⟨19275609438720857673879365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12850406292480571782586243 19275609438720857673879365)
            ·
              refine ⟨3614176769760160813852381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19275609438720857673879365 3614176769760160813852381)
              ·
                refine ⟨1355316288660060305194643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3614176769760160813852381 1355316288660060305194643)
                ·
                  refine ⟨2032974432990090457791965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355316288660060305194643 2032974432990090457791965)
                  ·
                    refine ⟨762365412371283921671987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032974432990090457791965 762365412371283921671987)
                    ·
                      rfl

theorem cell22_2227052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_2227052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227052 prefixEnd_2227052 := by exact prefixLift 2227052
  have htrace : WordTrace (prefixWord ++ tailWord_2227052) baseStart_2227052 baseEnd_2227052 := by
    simpa [prefixWord, tailWord_2227052, baseEnd_2227052] using wordTrace_append hprefix tailTrace_2227052
  have hstable : (prefixWord ++ tailWord_2227052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227052).length < 2 ^ (prefixWord ++ tailWord_2227052).sum := by decide
  have hdescent : baseEnd_2227052 < baseStart_2227052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227065 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 5]
def baseStart_2227065 : Nat := 118140960795 + 2227065 * 2 ^ 59
def prefixEnd_2227065 : Nat := 4983230072969 + 3 ^ 40 * 2227065 * 2
def baseEnd_2227065 : Nat := 254123287512318740365649

theorem tailTrace_2227065 : CollatzResearch.WordTrace tailWord_2227065 prefixEnd_2227065 254123287512318740365649 := by
  unfold tailWord_2227065
  simp only [CollatzResearch.WordTrace]
  refine ⟨81227733676731332265706649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54151822451154221510471099 81227733676731332265706649)
  ·
    refine ⟨60920800257548499199279987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81227733676731332265706649 60920800257548499199279987)
    ·
      refine ⟨91381200386322748798919981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60920800257548499199279987 91381200386322748798919981)
      ·
        refine ⟨34267950144871030799594993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91381200386322748798919981 34267950144871030799594993)
        ·
          refine ⟨25700962608653273099696245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34267950144871030799594993 25700962608653273099696245)
          ·
            refine ⟨2409465244561244353096523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25700962608653273099696245 2409465244561244353096523)
            ·
              refine ⟨3614197866841866529644785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409465244561244353096523 3614197866841866529644785)
              ·
                refine ⟨2710648400131399897233589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3614197866841866529644785 2710648400131399897233589)
                ·
                  refine ⟨254123287512318740365649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2710648400131399897233589 254123287512318740365649)
                  ·
                    rfl

theorem cell22_2227065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_2227065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227065 prefixEnd_2227065 := by exact prefixLift 2227065
  have htrace : WordTrace (prefixWord ++ tailWord_2227065) baseStart_2227065 baseEnd_2227065 := by
    simpa [prefixWord, tailWord_2227065, baseEnd_2227065] using wordTrace_append hprefix tailTrace_2227065
  have hstable : (prefixWord ++ tailWord_2227065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227065).length < 2 ^ (prefixWord ++ tailWord_2227065).sum := by decide
  have hdescent : baseEnd_2227065 < baseStart_2227065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227082 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_2227082 : Nat := 118140960795 + 2227082 * 2 ^ 59
def prefixEnd_2227082 : Nat := 4983230072969 + 3 ^ 40 * 2227082 * 2
def baseEnd_2227082 : Nat := 254125227328124614473965

theorem tailTrace_2227082 : CollatzResearch.WordTrace tailWord_2227082 prefixEnd_2227082 254125227328124614473965 := by
  unfold tailWord_2227082
  simp only [CollatzResearch.WordTrace]
  refine ⟨20307088429417436042268875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54152235811779829446050333 20307088429417436042268875)
  ·
    refine ⟨30460632644126154063403313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20307088429417436042268875 30460632644126154063403313)
    ·
      refine ⟨22845474483094615547552485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30460632644126154063403313 22845474483094615547552485)
      ·
        refine ⟨4283526465580240415166091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22845474483094615547552485 4283526465580240415166091)
        ·
          refine ⟨6425289698370360622749137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283526465580240415166091 6425289698370360622749137)
          ·
            refine ⟨4818967273777770467061853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6425289698370360622749137 4818967273777770467061853)
            ·
              refine ⟨1807112727666663925148195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4818967273777770467061853 1807112727666663925148195)
              ·
                refine ⟨2710669091499995887722293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807112727666663925148195 2710669091499995887722293)
                ·
                  refine ⟨254125227328124614473965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2710669091499995887722293 254125227328124614473965)
                  ·
                    rfl

theorem cell22_2227082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_2227082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227082 prefixEnd_2227082 := by exact prefixLift 2227082
  have htrace : WordTrace (prefixWord ++ tailWord_2227082) baseStart_2227082 baseEnd_2227082 := by
    simpa [prefixWord, tailWord_2227082, baseEnd_2227082] using wordTrace_append hprefix tailTrace_2227082
  have hstable : (prefixWord ++ tailWord_2227082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227082).length < 2 ^ (prefixWord ++ tailWord_2227082).sum := by decide
  have hdescent : baseEnd_2227082 < baseStart_2227082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227093 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 6]
def baseStart_2227093 : Nat := 118140960795 + 2227093 * 2 ^ 59
def prefixEnd_2227093 : Nat := 4983230072969 + 3 ^ 40 * 2227093 * 2
def baseEnd_2227093 : Nat := 254126482503057827132287

theorem tailTrace_2227093 : CollatzResearch.WordTrace tailWord_2227093 prefixEnd_2227093 254126482503057827132287 := by
  unfold tailWord_2227093
  simp only [CollatzResearch.WordTrace]
  refine ⟨81228754920629893047725933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54152503280419928698483955 81228754920629893047725933)
  ·
    refine ⟨30460783095236209892897225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81228754920629893047725933 30460783095236209892897225)
    ·
      refine ⟨22845587321427157419672919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30460783095236209892897225 22845587321427157419672919)
      ·
        refine ⟨34268380982140736129509379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22845587321427157419672919 34268380982140736129509379)
        ·
          refine ⟨51402571473211104194264069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34268380982140736129509379 51402571473211104194264069)
          ·
            refine ⟨9637982151227082036424513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51402571473211104194264069 9637982151227082036424513)
            ·
              refine ⟨7228486613420311527318385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9637982151227082036424513 7228486613420311527318385)
              ·
                refine ⟨5421364960065233645488789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7228486613420311527318385 5421364960065233645488789)
                ·
                  refine ⟨254126482503057827132287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5421364960065233645488789 254126482503057827132287)
                  ·
                    rfl

theorem cell22_2227093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_2227093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227093 prefixEnd_2227093 := by exact prefixLift 2227093
  have htrace : WordTrace (prefixWord ++ tailWord_2227093) baseStart_2227093 baseEnd_2227093 := by
    simpa [prefixWord, tailWord_2227093, baseEnd_2227093] using wordTrace_append hprefix tailTrace_2227093
  have hstable : (prefixWord ++ tailWord_2227093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227093).length < 2 ^ (prefixWord ++ tailWord_2227093).sum := by decide
  have hdescent : baseEnd_2227093 < baseStart_2227093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227095 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 1, 4]
def baseStart_2227095 : Nat := 118140960795 + 2227095 * 2 ^ 59
def prefixEnd_2227095 : Nat := 4983230072969 + 3 ^ 40 * 2227095 * 2
def baseEnd_2227095 : Nat := 762380132150046142846855

theorem tailTrace_2227095 : CollatzResearch.WordTrace tailWord_2227095 prefixEnd_2227095 762380132150046142846855 := by
  unfold tailWord_2227095
  simp only [CollatzResearch.WordTrace]
  refine ⟨81228827866622647389298739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54152551911081764926199159 81228827866622647389298739)
  ·
    refine ⟨121843241799933971083948109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81228827866622647389298739 121843241799933971083948109)
    ·
      refine ⟨45691215674975239156480541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121843241799933971083948109 45691215674975239156480541)
      ·
        refine ⟨17134205878115714683680203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45691215674975239156480541 17134205878115714683680203)
        ·
          refine ⟨25701308817173572025520305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17134205878115714683680203 25701308817173572025520305)
          ·
            refine ⟨19275981612880179019140229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25701308817173572025520305 19275981612880179019140229)
            ·
              refine ⟨3614246552415033566088793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19275981612880179019140229 3614246552415033566088793)
              ·
                refine ⟨2710684914311275174566595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3614246552415033566088793 2710684914311275174566595)
                ·
                  refine ⟨4066027371466912761849893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2710684914311275174566595 4066027371466912761849893)
                  ·
                    refine ⟨762380132150046142846855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4066027371466912761849893 762380132150046142846855)
                    ·
                      rfl

theorem cell22_2227095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_2227095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227095 prefixEnd_2227095 := by exact prefixLift 2227095
  have htrace : WordTrace (prefixWord ++ tailWord_2227095) baseStart_2227095 baseEnd_2227095 := by
    simpa [prefixWord, tailWord_2227095, baseEnd_2227095] using wordTrace_append hprefix tailTrace_2227095
  have hstable : (prefixWord ++ tailWord_2227095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227095).length < 2 ^ (prefixWord ++ tailWord_2227095).sum := by decide
  have hdescent : baseEnd_2227095 < baseStart_2227095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227108 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2227108 : Nat := 118140960795 + 2227108 * 2 ^ 59
def prefixEnd_2227108 : Nat := 4983230072969 + 3 ^ 40 * 2227108 * 2
def baseEnd_2227108 : Nat := 762384582315718442271815

theorem tailTrace_2227108 : CollatzResearch.WordTrace tailWord_2227108 prefixEnd_2227108 762384582315718442271815 := by
  unfold tailWord_2227108
  simp only [CollatzResearch.WordTrace]
  refine ⟨40614651007787775304760989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54152868010383700406347985 40614651007787775304760989)
  ·
    refine ⟨15230494127920415739285371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40614651007787775304760989 15230494127920415739285371)
    ·
      refine ⟨22845741191880623608928057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15230494127920415739285371 22845741191880623608928057)
      ·
        refine ⟨17134305893910467706696043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22845741191880623608928057 17134305893910467706696043)
        ·
          refine ⟨25701458840865701560044065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17134305893910467706696043 25701458840865701560044065)
          ·
            refine ⟨19276094130649276170033049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25701458840865701560044065 19276094130649276170033049)
            ·
              refine ⟨14457070597986957127524787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19276094130649276170033049 14457070597986957127524787)
              ·
                refine ⟨21685605896980435691287181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14457070597986957127524787 21685605896980435691287181)
                ·
                  refine ⟨8132102211367663384232693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21685605896980435691287181 8132102211367663384232693)
                  ·
                    refine ⟨762384582315718442271815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8132102211367663384232693 762384582315718442271815)
                    ·
                      rfl

theorem cell22_2227108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2227108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227108 prefixEnd_2227108 := by exact prefixLift 2227108
  have htrace : WordTrace (prefixWord ++ tailWord_2227108) baseStart_2227108 baseEnd_2227108 := by
    simpa [prefixWord, tailWord_2227108, baseEnd_2227108] using wordTrace_append hprefix tailTrace_2227108
  have hstable : (prefixWord ++ tailWord_2227108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227108).length < 2 ^ (prefixWord ++ tailWord_2227108).sum := by decide
  have hdescent : baseEnd_2227108 < baseStart_2227108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227125 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_2227125 : Nat := 118140960795 + 2227125 * 2 ^ 59
def prefixEnd_2227125 : Nat := 4983230072969 + 3 ^ 40 * 2227125 * 2
def baseEnd_2227125 : Nat := 762390401763136064596763

theorem tailTrace_2227125 : CollatzResearch.WordTrace tailWord_2227125 prefixEnd_2227125 762390401763136064596763 := by
  unfold tailWord_2227125
  simp only [CollatzResearch.WordTrace]
  refine ⟨81229922056513962512890829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54153281371009308341927219 81229922056513962512890829)
  ·
    refine ⟨30461220771192735942334061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81229922056513962512890829 30461220771192735942334061)
    ·
      refine ⟨11422957789197275978375273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30461220771192735942334061 11422957789197275978375273)
      ·
        refine ⟨8567218341897956983781455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11422957789197275978375273 8567218341897956983781455)
        ·
          refine ⟨12850827512846935475672183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8567218341897956983781455 12850827512846935475672183)
          ·
            refine ⟨19276241269270403213508275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12850827512846935475672183 19276241269270403213508275)
            ·
              refine ⟨28914361903905604820262413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19276241269270403213508275 28914361903905604820262413)
              ·
                refine ⟨10842885713964601807598405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28914361903905604820262413 10842885713964601807598405)
                ·
                  refine ⟨2033041071368362838924701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10842885713964601807598405 2033041071368362838924701)
                  ·
                    refine ⟨762390401763136064596763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2033041071368362838924701 762390401763136064596763)
                    ·
                      rfl

theorem cell22_2227125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_2227125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227125 prefixEnd_2227125 := by exact prefixLift 2227125
  have htrace : WordTrace (prefixWord ++ tailWord_2227125) baseStart_2227125 baseEnd_2227125 := by
    simpa [prefixWord, tailWord_2227125, baseEnd_2227125] using wordTrace_append hprefix tailTrace_2227125
  have hstable : (prefixWord ++ tailWord_2227125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227125).length < 2 ^ (prefixWord ++ tailWord_2227125).sum := by decide
  have hdescent : baseEnd_2227125 < baseStart_2227125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227157 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_2227157 : Nat := 118140960795 + 2227157 * 2 ^ 59
def prefixEnd_2227157 : Nat := 4983230072969 + 3 ^ 40 * 2227157 * 2
def baseEnd_2227157 : Nat := 762401356017098647796665

theorem tailTrace_2227157 : CollatzResearch.WordTrace tailWord_2227157 prefixEnd_2227157 762401356017098647796665 := by
  unfold tailWord_2227157
  simp only [CollatzResearch.WordTrace]
  refine ⟨81231089192398031978055725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54154059461598687985370483 81231089192398031978055725)
  ·
    refine ⟨30461658447149261991770897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81231089192398031978055725 30461658447149261991770897)
    ·
      refine ⟨22846243835361946493828173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30461658447149261991770897 22846243835361946493828173)
      ·
        refine ⟨8567341438260729935185565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22846243835361946493828173 8567341438260729935185565)
        ·
          refine ⟨3212753039347773725694587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8567341438260729935185565 3212753039347773725694587)
          ·
            refine ⟨4819129559021660588541881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212753039347773725694587 4819129559021660588541881)
            ·
              refine ⟨3614347169266245441406411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4819129559021660588541881 3614347169266245441406411)
              ·
                refine ⟨5421520753899368162109617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3614347169266245441406411 5421520753899368162109617)
                ·
                  refine ⟨4066140565424526121582213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5421520753899368162109617 4066140565424526121582213)
                  ·
                    refine ⟨762401356017098647796665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4066140565424526121582213 762401356017098647796665)
                    ·
                      rfl

theorem cell22_2227157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_2227157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227157 prefixEnd_2227157 := by exact prefixLift 2227157
  have htrace : WordTrace (prefixWord ++ tailWord_2227157) baseStart_2227157 baseEnd_2227157 := by
    simpa [prefixWord, tailWord_2227157, baseEnd_2227157] using wordTrace_append hprefix tailTrace_2227157
  have hstable : (prefixWord ++ tailWord_2227157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227157).length < 2 ^ (prefixWord ++ tailWord_2227157).sum := by decide
  have hdescent : baseEnd_2227157 < baseStart_2227157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227189 : List Nat := [1, 3, 5, 2, 1, 2, 1, 7]
def baseStart_2227189 : Nat := 118140960795 + 2227189 * 2 ^ 59
def prefixEnd_2227189 : Nat := 4983230072969 + 3 ^ 40 * 2227189 * 2
def baseEnd_2227189 : Nat := 84712478919006803444063

theorem tailTrace_2227189 : CollatzResearch.WordTrace tailWord_2227189 prefixEnd_2227189 84712478919006803444063 := by
  unfold tailWord_2227189
  simp only [CollatzResearch.WordTrace]
  refine ⟨81232256328282101443220621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54154837552188067628813747 81232256328282101443220621)
  ·
    refine ⟨30462096123105788041207733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81232256328282101443220621 30462096123105788041207733)
    ·
      refine ⟨2855821511541167628863225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30462096123105788041207733 2855821511541167628863225)
      ·
        refine ⟨2141866133655875721647419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2855821511541167628863225 2141866133655875721647419)
        ·
          refine ⟨3212799200483813582471129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141866133655875721647419 3212799200483813582471129)
          ·
            refine ⟨2409599400362860186853347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3212799200483813582471129 2409599400362860186853347)
            ·
              refine ⟨3614399100544290280280021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409599400362860186853347 3614399100544290280280021)
              ·
                refine ⟨84712478919006803444063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3614399100544290280280021 84712478919006803444063)
                ·
                  rfl

theorem cell22_2227189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 7].length) (baseStart_2227189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227189 prefixEnd_2227189 := by exact prefixLift 2227189
  have htrace : WordTrace (prefixWord ++ tailWord_2227189) baseStart_2227189 baseEnd_2227189 := by
    simpa [prefixWord, tailWord_2227189, baseEnd_2227189] using wordTrace_append hprefix tailTrace_2227189
  have hstable : (prefixWord ++ tailWord_2227189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227189).length < 2 ^ (prefixWord ++ tailWord_2227189).sum := by decide
  have hdescent : baseEnd_2227189 < baseStart_2227189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227262 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2227262 : Nat := 118140960795 + 2227262 * 2 ^ 59
def prefixEnd_2227262 : Nat := 4983230072969 + 3 ^ 40 * 2227262 * 2
def baseEnd_2227262 : Nat := 254145766554304457973781

theorem tailTrace_2227262 : CollatzResearch.WordTrace tailWord_2227262 prefixEnd_2227262 254145766554304457973781 := by
  unfold tailWord_2227262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10154364857127204363828505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54156612571345089940418693 10154364857127204363828505)
  ·
    refine ⟨7615773642845403272871379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10154364857127204363828505 7615773642845403272871379)
    ·
      refine ⟨11423660464268104909307069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7615773642845403272871379 11423660464268104909307069)
      ·
        refine ⟨4283872674100539340990151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11423660464268104909307069 4283872674100539340990151)
        ·
          refine ⟨6425809011150809011485227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283872674100539340990151 6425809011150809011485227)
          ·
            refine ⟨9638713516726213517227841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6425809011150809011485227 9638713516726213517227841)
            ·
              refine ⟨7229035137544660137920881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9638713516726213517227841 7229035137544660137920881)
              ·
                refine ⟨5421776353158495103440661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7229035137544660137920881 5421776353158495103440661)
                ·
                  refine ⟨254145766554304457973781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5421776353158495103440661 254145766554304457973781)
                  ·
                    rfl

theorem cell22_2227262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2227262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227262 prefixEnd_2227262 := by exact prefixLift 2227262
  have htrace : WordTrace (prefixWord ++ tailWord_2227262) baseStart_2227262 baseEnd_2227262 := by
    simpa [prefixWord, tailWord_2227262, baseEnd_2227262] using wordTrace_append hprefix tailTrace_2227262
  have hstable : (prefixWord ++ tailWord_2227262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227262).length < 2 ^ (prefixWord ++ tailWord_2227262).sum := by decide
  have hdescent : baseEnd_2227262 < baseStart_2227262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227292 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2227292 : Nat := 118140960795 + 2227292 * 2 ^ 59
def prefixEnd_2227292 : Nat := 4983230072969 + 3 ^ 40 * 2227292 * 2
def baseEnd_2227292 : Nat := 762447569276003295671251

theorem tailTrace_2227292 : CollatzResearch.WordTrace tailWord_2227292 prefixEnd_2227292 762447569276003295671251 := by
  unfold tailWord_2227292
  simp only [CollatzResearch.WordTrace]
  refine ⟨40618006523454475017110065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54157342031272633356146753 40618006523454475017110065)
  ·
    refine ⟨30463504892590856262832549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40618006523454475017110065 30463504892590856262832549)
    ·
      refine ⟨5711907167360785549281103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30463504892590856262832549 5711907167360785549281103)
      ·
        refine ⟨8567860751041178323921655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5711907167360785549281103 8567860751041178323921655)
        ·
          refine ⟨12851791126561767485882483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8567860751041178323921655 12851791126561767485882483)
          ·
            refine ⟨19277686689842651228823725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12851791126561767485882483 19277686689842651228823725)
            ·
              refine ⟨7229132508690994210808897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19277686689842651228823725 7229132508690994210808897)
              ·
                refine ⟨5421849381518245658106673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7229132508690994210808897 5421849381518245658106673)
                ·
                  refine ⟨4066387036138684243580005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5421849381518245658106673 4066387036138684243580005)
                  ·
                    refine ⟨762447569276003295671251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4066387036138684243580005 762447569276003295671251)
                    ·
                      rfl

theorem cell22_2227292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2227292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227292 prefixEnd_2227292 := by exact prefixLift 2227292
  have htrace : WordTrace (prefixWord ++ tailWord_2227292) baseStart_2227292 baseEnd_2227292 := by
    simpa [prefixWord, tailWord_2227292, baseEnd_2227292] using wordTrace_append hprefix tailTrace_2227292
  have hstable : (prefixWord ++ tailWord_2227292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227292).length < 2 ^ (prefixWord ++ tailWord_2227292).sum := by decide
  have hdescent : baseEnd_2227292 < baseStart_2227292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227352 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 5]
def baseStart_2227352 : Nat := 118140960795 + 2227352 * 2 ^ 59
def prefixEnd_2227352 : Nat := 4983230072969 + 3 ^ 40 * 2227352 * 2
def baseEnd_2227352 : Nat := 254156036167394379723689

theorem tailTrace_2227352 : CollatzResearch.WordTrace tailWord_2227352 prefixEnd_2227352 254156036167394379723689 := by
  unfold tailWord_2227352
  simp only [CollatzResearch.WordTrace]
  refine ⟨40619100713345790140702155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54158800951127720187602873 40619100713345790140702155)
  ·
    refine ⟨60928651070018685211053233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40619100713345790140702155 60928651070018685211053233)
    ·
      refine ⟨45696488302514013908289925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60928651070018685211053233 45696488302514013908289925)
      ·
        refine ⟨8568091556721377607804361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45696488302514013908289925 8568091556721377607804361)
        ·
          refine ⟨6426068667541033205853271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8568091556721377607804361 6426068667541033205853271)
          ·
            refine ⟨9639103001311549808779907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6426068667541033205853271 9639103001311549808779907)
            ·
              refine ⟨14458654501967324713169861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9639103001311549808779907 14458654501967324713169861)
              ·
                refine ⟨2710997719118873383719349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14458654501967324713169861 2710997719118873383719349)
                ·
                  refine ⟨254156036167394379723689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2710997719118873383719349 254156036167394379723689)
                  ·
                    rfl

theorem cell22_2227352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_2227352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227352 prefixEnd_2227352 := by exact prefixLift 2227352
  have htrace : WordTrace (prefixWord ++ tailWord_2227352) baseStart_2227352 baseEnd_2227352 := by
    simpa [prefixWord, tailWord_2227352, baseEnd_2227352] using wordTrace_append hprefix tailTrace_2227352
  have hstable : (prefixWord ++ tailWord_2227352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227352).length < 2 ^ (prefixWord ++ tailWord_2227352).sum := by decide
  have hdescent : baseEnd_2227352 < baseStart_2227352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227356 : List Nat := [2, 2, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2227356 : Nat := 118140960795 + 2227356 * 2 ^ 59
def prefixEnd_2227356 : Nat := 4983230072969 + 3 ^ 40 * 2227356 * 2
def baseEnd_2227356 : Nat := 762469477783928462071055

theorem tailTrace_2227356 : CollatzResearch.WordTrace tailWord_2227356 prefixEnd_2227356 762469477783928462071055 := by
  unfold tailWord_2227356
  simp only [CollatzResearch.WordTrace]
  refine ⟨40619173659338544482274961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54158898212451392643033281 40619173659338544482274961)
  ·
    refine ⟨30464380244503908361706221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40619173659338544482274961 30464380244503908361706221)
    ·
      refine ⟨11424142591688965635639833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30464380244503908361706221 11424142591688965635639833)
      ·
        refine ⟨8568106943766724226729875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11424142591688965635639833 8568106943766724226729875)
        ·
          refine ⟨12852160415650086340094813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568106943766724226729875 12852160415650086340094813)
          ·
            refine ⟨4819560155868782377535555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12852160415650086340094813 4819560155868782377535555)
            ·
              refine ⟨7229340233803173566303333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819560155868782377535555 7229340233803173566303333)
              ·
                refine ⟨1355501293838095043681875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7229340233803173566303333 1355501293838095043681875)
                ·
                  refine ⟨2033251940757142565522813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355501293838095043681875 2033251940757142565522813)
                  ·
                    refine ⟨762469477783928462071055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2033251940757142565522813 762469477783928462071055)
                    ·
                      rfl

theorem cell22_2227356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2227356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227356 prefixEnd_2227356 := by exact prefixLift 2227356
  have htrace : WordTrace (prefixWord ++ tailWord_2227356) baseStart_2227356 baseEnd_2227356 := by
    simpa [prefixWord, tailWord_2227356, baseEnd_2227356] using wordTrace_append hprefix tailTrace_2227356
  have hstable : (prefixWord ++ tailWord_2227356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227356).length < 2 ^ (prefixWord ++ tailWord_2227356).sum := by decide
  have hdescent : baseEnd_2227356 < baseStart_2227356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227367 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2227367 : Nat := 118140960795 + 2227367 * 2 ^ 59
def prefixEnd_2227367 : Nat := 4983230072969 + 3 ^ 40 * 2227367 * 2
def baseEnd_2227367 : Nat := 762473243308728100046021

theorem tailTrace_2227367 : CollatzResearch.WordTrace tailWord_2227367 prefixEnd_2227367 762473243308728100046021 := by
  unfold tailWord_2227367
  simp only [CollatzResearch.WordTrace]
  refine ⟨81238748521637237843200355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54159165681091491895466903 81238748521637237843200355)
  ·
    refine ⟨121858122782455856764800533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81238748521637237843200355 121858122782455856764800533)
    ·
      refine ⟨5712099505427618285850025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121858122782455856764800533 5712099505427618285850025)
      ·
        refine ⟨4284074629070713714387519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5712099505427618285850025 4284074629070713714387519)
        ·
          refine ⟨6426111943606070571581279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4284074629070713714387519 6426111943606070571581279)
          ·
            refine ⟨9639167915409105857371919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6426111943606070571581279 9639167915409105857371919)
            ·
              refine ⟨14458751873113658786057879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9639167915409105857371919 14458751873113658786057879)
              ·
                refine ⟨21688127809670488179086819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14458751873113658786057879 21688127809670488179086819)
                ·
                  refine ⟨32532191714505732268630229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21688127809670488179086819 32532191714505732268630229)
                  ·
                    refine ⟨762473243308728100046021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32532191714505732268630229 762473243308728100046021)
                    ·
                      rfl

theorem cell22_2227367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2227367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227367 prefixEnd_2227367 := by exact prefixLift 2227367
  have htrace : WordTrace (prefixWord ++ tailWord_2227367) baseStart_2227367 baseEnd_2227367 := by
    simpa [prefixWord, tailWord_2227367, baseEnd_2227367] using wordTrace_append hprefix tailTrace_2227367
  have hstable : (prefixWord ++ tailWord_2227367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227367).length < 2 ^ (prefixWord ++ tailWord_2227367).sum := by decide
  have hdescent : baseEnd_2227367 < baseStart_2227367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227395 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 3, 5]
def baseStart_2227395 : Nat := 118140960795 + 2227395 * 2 ^ 59
def prefixEnd_2227395 : Nat := 4983230072969 + 3 ^ 40 * 2227395 * 2
def baseEnd_2227395 : Nat := 762482828280945360345935

theorem tailTrace_2227395 : CollatzResearch.WordTrace tailWord_2227395 prefixEnd_2227395 762482828280945360345935 := by
  unfold tailWord_2227395
  simp only [CollatzResearch.WordTrace]
  refine ⟨81239769765535798625219639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54159846510357199083479759 81239769765535798625219639)
  ·
    refine ⟨121859654648303697937829459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81239769765535798625219639 121859654648303697937829459)
    ·
      refine ⟨182789481972455546906744189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121859654648303697937829459 182789481972455546906744189)
      ·
        refine ⟨68546055739670830090029071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182789481972455546906744189 68546055739670830090029071)
        ·
          refine ⟨102819083609506245135043607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68546055739670830090029071 102819083609506245135043607)
          ·
            refine ⟨154228625414259367702565411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102819083609506245135043607 154228625414259367702565411)
            ·
              refine ⟨231342938121389051553848117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154228625414259367702565411 231342938121389051553848117)
              ·
                refine ⟨21688400448880223583173261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231342938121389051553848117 21688400448880223583173261)
                ·
                  refine ⟨8133150168330083843689973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21688400448880223583173261 8133150168330083843689973)
                  ·
                    refine ⟨762482828280945360345935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8133150168330083843689973 762482828280945360345935)
                    ·
                      rfl

theorem cell22_2227395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_2227395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227395 prefixEnd_2227395 := by exact prefixLift 2227395
  have htrace : WordTrace (prefixWord ++ tailWord_2227395) baseStart_2227395 baseEnd_2227395 := by
    simpa [prefixWord, tailWord_2227395, baseEnd_2227395] using wordTrace_append hprefix tailTrace_2227395
  have hstable : (prefixWord ++ tailWord_2227395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227395).length < 2 ^ (prefixWord ++ tailWord_2227395).sum := by decide
  have hdescent : baseEnd_2227395 < baseStart_2227395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227508 : List Nat := [2, 5, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2227508 : Nat := 118140960795 + 2227508 * 2 ^ 59
def prefixEnd_2227508 : Nat := 4983230072969 + 3 ^ 40 * 2227508 * 2
def baseEnd_2227508 : Nat := 762521510490250732270589

theorem tailTrace_2227508 : CollatzResearch.WordTrace tailWord_2227508 prefixEnd_2227508 762521510490250732270589 := by
  unfold tailWord_2227508
  simp only [CollatzResearch.WordTrace]
  refine ⟨40621945607063209462041589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54162594142750945949388785 40621945607063209462041589)
  ·
    refine ⟨3808307400662175887066399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40621945607063209462041589 3808307400662175887066399)
    ·
      refine ⟨5712461100993263830599599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3808307400662175887066399 5712461100993263830599599)
      ·
        refine ⟨8568691651489895745899399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5712461100993263830599599 8568691651489895745899399)
        ·
          refine ⟨12853037477234843618849099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568691651489895745899399 12853037477234843618849099)
          ·
            refine ⟨19279556215852265428273649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12853037477234843618849099 19279556215852265428273649)
            ·
              refine ⟨14459667161889199071205237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19279556215852265428273649 14459667161889199071205237)
              ·
                refine ⟨1355593796427112412925491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14459667161889199071205237 1355593796427112412925491)
                ·
                  refine ⟨2033390694640668619388237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355593796427112412925491 2033390694640668619388237)
                  ·
                    refine ⟨762521510490250732270589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2033390694640668619388237 762521510490250732270589)
                    ·
                      rfl

theorem cell22_2227508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2227508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227508 prefixEnd_2227508 := by exact prefixLift 2227508
  have htrace : WordTrace (prefixWord ++ tailWord_2227508) baseStart_2227508 baseEnd_2227508 := by
    simpa [prefixWord, tailWord_2227508, baseEnd_2227508] using wordTrace_append hprefix tailTrace_2227508
  have hstable : (prefixWord ++ tailWord_2227508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227508).length < 2 ^ (prefixWord ++ tailWord_2227508).sum := by decide
  have hdescent : baseEnd_2227508 < baseStart_2227508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227521 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 5]
def baseStart_2227521 : Nat := 118140960795 + 2227521 * 2 ^ 59
def prefixEnd_2227521 : Nat := 4983230072969 + 3 ^ 40 * 2227521 * 2
def baseEnd_2227521 : Nat := 254175320218641010565183

theorem tailTrace_2227521 : CollatzResearch.WordTrace tailWord_2227521 prefixEnd_2227521 254175320218641010565183 := by
  unfold tailWord_2227521
  simp only [CollatzResearch.WordTrace]
  refine ⟨81244365363079322144306417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54162910242052881429537611 81244365363079322144306417)
  ·
    refine ⟨60933274022309491608229813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81244365363079322144306417 60933274022309491608229813)
    ·
      refine ⟨5712494439591514838271545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60933274022309491608229813 5712494439591514838271545)
      ·
        refine ⟨4284370829693636128703659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5712494439591514838271545 4284370829693636128703659)
        ·
          refine ⟨6426556244540454193055489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4284370829693636128703659 6426556244540454193055489)
          ·
            refine ⟨4819917183405340644791617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6426556244540454193055489 4819917183405340644791617)
            ·
              refine ⟨3614937887554005483593713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4819917183405340644791617 3614937887554005483593713)
              ·
                refine ⟨2711203415665504112695285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3614937887554005483593713 2711203415665504112695285)
                ·
                  refine ⟨254175320218641010565183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2711203415665504112695285 254175320218641010565183)
                  ·
                    rfl

theorem cell22_2227521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_2227521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227521 prefixEnd_2227521 := by exact prefixLift 2227521
  have htrace : WordTrace (prefixWord ++ tailWord_2227521) baseStart_2227521 baseEnd_2227521 := by
    simpa [prefixWord, tailWord_2227521, baseEnd_2227521] using wordTrace_append hprefix tailTrace_2227521
  have hstable : (prefixWord ++ tailWord_2227521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227521).length < 2 ^ (prefixWord ++ tailWord_2227521).sum := by decide
  have hdescent : baseEnd_2227521 < baseStart_2227521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227542 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2227542 : Nat := 118140960795 + 2227542 * 2 ^ 59
def prefixEnd_2227542 : Nat := 4983230072969 + 3 ^ 40 * 2227542 * 2
def baseEnd_2227542 : Nat := 762533149385085976920485

theorem tailTrace_2227542 : CollatzResearch.WordTrace tailWord_2227542 prefixEnd_2227542 762533149385085976920485 := by
  unfold tailWord_2227542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077820706000202670676305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54163420864002161820547253 5077820706000202670676305)
  ·
    refine ⟨3808365529500152003007229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5077820706000202670676305 3808365529500152003007229)
    ·
      refine ⟨1428137073562557001127711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3808365529500152003007229 1428137073562557001127711)
      ·
        refine ⟨2142205610343835501691567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428137073562557001127711 2142205610343835501691567)
        ·
          refine ⟨3213308415515753252537351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142205610343835501691567 3213308415515753252537351)
          ·
            refine ⟨4819962623273629878806027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3213308415515753252537351 4819962623273629878806027)
            ·
              refine ⟨7229943934910444818209041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4819962623273629878806027 7229943934910444818209041)
              ·
                refine ⟨5422457951182833613656781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7229943934910444818209041 5422457951182833613656781)
                ·
                  refine ⟨2033421731693562605121293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5422457951182833613656781 2033421731693562605121293)
                  ·
                    refine ⟨762533149385085976920485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2033421731693562605121293 762533149385085976920485)
                    ·
                      rfl

theorem cell22_2227542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2227542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227542 prefixEnd_2227542 := by exact prefixLift 2227542
  have htrace : WordTrace (prefixWord ++ tailWord_2227542) baseStart_2227542 baseEnd_2227542 := by
    simpa [prefixWord, tailWord_2227542, baseEnd_2227542] using wordTrace_append hprefix tailTrace_2227542
  have hstable : (prefixWord ++ tailWord_2227542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227542).length < 2 ^ (prefixWord ++ tailWord_2227542).sum := by decide
  have hdescent : baseEnd_2227542 < baseStart_2227542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227564 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_2227564 : Nat := 118140960795 + 2227564 * 2 ^ 59
def prefixEnd_2227564 : Nat := 4983230072969 + 3 ^ 40 * 2227564 * 2
def baseEnd_2227564 : Nat := 762540680434685252870417

theorem tailTrace_2227564 : CollatzResearch.WordTrace tailWord_2227564 prefixEnd_2227564 762540680434685252870417 := by
  unfold tailWord_2227564
  simp only [CollatzResearch.WordTrace]
  refine ⟨40622966850961770244060873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54163955801282360325414497 40622966850961770244060873)
  ·
    refine ⟨30467225138221327683045655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40622966850961770244060873 30467225138221327683045655)
    ·
      refine ⟨45700837707331991524568483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30467225138221327683045655 45700837707331991524568483)
      ·
        refine ⟨68551256560997987286852725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45700837707331991524568483 68551256560997987286852725)
        ·
          refine ⟨6426680302593561308142443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68551256560997987286852725 6426680302593561308142443)
          ·
            refine ⟨9640020453890341962213665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6426680302593561308142443 9640020453890341962213665)
            ·
              refine ⟨7230015340417756471660249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9640020453890341962213665 7230015340417756471660249)
              ·
                refine ⟨5422511505313317353745187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7230015340417756471660249 5422511505313317353745187)
                ·
                  refine ⟨8133767257969976030617781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5422511505313317353745187 8133767257969976030617781)
                  ·
                    refine ⟨762540680434685252870417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8133767257969976030617781 762540680434685252870417)
                    ·
                      rfl

theorem cell22_2227564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_2227564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227564 prefixEnd_2227564 := by exact prefixLift 2227564
  have htrace : WordTrace (prefixWord ++ tailWord_2227564) baseStart_2227564 baseEnd_2227564 := by
    simpa [prefixWord, tailWord_2227564, baseEnd_2227564] using wordTrace_append hprefix tailTrace_2227564
  have hstable : (prefixWord ++ tailWord_2227564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227564).length < 2 ^ (prefixWord ++ tailWord_2227564).sum := by decide
  have hdescent : baseEnd_2227564 < baseStart_2227564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227598 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_2227598 : Nat := 118140960795 + 2227598 * 2 ^ 59
def prefixEnd_2227598 : Nat := 4983230072969 + 3 ^ 40 * 2227598 * 2
def baseEnd_2227598 : Nat := 762552319329520497520313

theorem tailTrace_2227598 : CollatzResearch.WordTrace tailWord_2227598 prefixEnd_2227598 762552319329520497520313 := by
  unfold tailWord_2227598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10155896722975045536857431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54164782522533576196572965 10155896722975045536857431)
  ·
    refine ⟨15233845084462568305286147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10155896722975045536857431 15233845084462568305286147)
    ·
      refine ⟨22850767626693852457929221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15233845084462568305286147 22850767626693852457929221)
      ·
        refine ⟨4284518930005097335861729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22850767626693852457929221 4284518930005097335861729)
        ·
          refine ⟨3213389197503823001896297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4284518930005097335861729 3213389197503823001896297)
          ·
            refine ⟨2410041898127867251422223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3213389197503823001896297 2410041898127867251422223)
            ·
              refine ⟨3615062847191800877133335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410041898127867251422223 3615062847191800877133335)
              ·
                refine ⟨5422594270787701315700003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615062847191800877133335 5422594270787701315700003)
                ·
                  refine ⟨8133891406181551973550005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5422594270787701315700003 8133891406181551973550005)
                  ·
                    refine ⟨762552319329520497520313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8133891406181551973550005 762552319329520497520313)
                    ·
                      rfl

theorem cell22_2227598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_2227598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227598 prefixEnd_2227598 := by exact prefixLift 2227598
  have htrace : WordTrace (prefixWord ++ tailWord_2227598) baseStart_2227598 baseEnd_2227598 := by
    simpa [prefixWord, tailWord_2227598, baseEnd_2227598] using wordTrace_append hprefix tailTrace_2227598
  have hstable : (prefixWord ++ tailWord_2227598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227598).length < 2 ^ (prefixWord ++ tailWord_2227598).sum := by decide
  have hdescent : baseEnd_2227598 < baseStart_2227598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227639 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 5]
def baseStart_2227639 : Nat := 118140960795 + 2227639 * 2 ^ 59
def prefixEnd_2227639 : Nat := 4983230072969 + 3 ^ 40 * 2227639 * 2
def baseEnd_2227639 : Nat := 254188784822470019081729

theorem tailTrace_2227639 : CollatzResearch.WordTrace tailWord_2227639 prefixEnd_2227639 254188784822470019081729 := by
  unfold tailWord_2227639
  simp only [CollatzResearch.WordTrace]
  refine ⟨81248669176651828297101971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54165779451101218864734647 81248669176651828297101971)
  ·
    refine ⟨121873003764977742445652957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81248669176651828297101971 121873003764977742445652957)
    ·
      refine ⟨45702376411866653417119859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121873003764977742445652957 45702376411866653417119859)
      ·
        refine ⟨68553564617799980125679789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45702376411866653417119859 68553564617799980125679789)
        ·
          refine ⟨25707586731674992547129921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68553564617799980125679789 25707586731674992547129921)
          ·
            refine ⟨19280690048756244410347441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25707586731674992547129921 19280690048756244410347441)
            ·
              refine ⟨14460517536567183307760581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19280690048756244410347441 14460517536567183307760581)
              ·
                refine ⟨2711347038106346870205109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14460517536567183307760581 2711347038106346870205109)
                ·
                  refine ⟨254188784822470019081729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2711347038106346870205109 254188784822470019081729)
                  ·
                    rfl

theorem cell22_2227639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 5].length) (baseStart_2227639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227639 prefixEnd_2227639 := by exact prefixLift 2227639
  have htrace : WordTrace (prefixWord ++ tailWord_2227639) baseStart_2227639 baseEnd_2227639 := by
    simpa [prefixWord, tailWord_2227639, baseEnd_2227639] using wordTrace_append hprefix tailTrace_2227639
  have hstable : (prefixWord ++ tailWord_2227639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227639).length < 2 ^ (prefixWord ++ tailWord_2227639).sum := by decide
  have hdescent : baseEnd_2227639 < baseStart_2227639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227731 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 2, 4]
def baseStart_2227731 : Nat := 118140960795 + 2227731 * 2 ^ 59
def prefixEnd_2227731 : Nat := 4983230072969 + 3 ^ 40 * 2227731 * 2
def baseEnd_2227731 : Nat := 762597847947552483944905

theorem tailTrace_2227731 : CollatzResearch.WordTrace tailWord_2227731 prefixEnd_2227731 762597847947552483944905 := by
  unfold tailWord_2227731
  simp only [CollatzResearch.WordTrace]
  refine ⟨81252024692318528009451047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54168016461545685339634031 81252024692318528009451047)
  ·
    refine ⟨121878037038477792014176571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81252024692318528009451047 121878037038477792014176571)
    ·
      refine ⟨182817055557716688021264857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121878037038477792014176571 182817055557716688021264857)
      ·
        refine ⟨137112791668287516015948643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182817055557716688021264857 137112791668287516015948643)
        ·
          refine ⟨205669187502431274023922965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137112791668287516015948643 205669187502431274023922965)
          ·
            refine ⟨9640743164176465969871389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 205669187502431274023922965 9640743164176465969871389)
            ·
              refine ⟨3615278686566174738701771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9640743164176465969871389 3615278686566174738701771)
              ·
                refine ⟨5422918029849262108052657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615278686566174738701771 5422918029849262108052657)
                ·
                  refine ⟨4067188522386946581039493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5422918029849262108052657 4067188522386946581039493)
                  ·
                    refine ⟨762597847947552483944905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4067188522386946581039493 762597847947552483944905)
                    ·
                      rfl

theorem cell22_2227731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4].length) (baseStart_2227731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227731 prefixEnd_2227731 := by exact prefixLift 2227731
  have htrace : WordTrace (prefixWord ++ tailWord_2227731) baseStart_2227731 baseEnd_2227731 := by
    simpa [prefixWord, tailWord_2227731, baseEnd_2227731] using wordTrace_append hprefix tailTrace_2227731
  have hstable : (prefixWord ++ tailWord_2227731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227731).length < 2 ^ (prefixWord ++ tailWord_2227731).sum := by decide
  have hdescent : baseEnd_2227731 < baseStart_2227731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227812 : List Nat := [2, 3, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_2227812 : Nat := 118140960795 + 2227812 * 2 ^ 59
def prefixEnd_2227812 : Nat := 4983230072969 + 3 ^ 40 * 2227812 * 2
def baseEnd_2227812 : Nat := 762625575902895272669657

theorem tailTrace_2227812 : CollatzResearch.WordTrace tailWord_2227812 prefixEnd_2227812 762625575902895272669657 := by
  unfold tailWord_2227812
  simp only [CollatzResearch.WordTrace]
  refine ⟨40627489502512539421574845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54169986003350052562099793 40627489502512539421574845)
  ·
    refine ⟨15235308563442202283090567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40627489502512539421574845 15235308563442202283090567)
    ·
      refine ⟨22852962845163303424635851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15235308563442202283090567 22852962845163303424635851)
      ·
        refine ⟨34279444267744955136953777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22852962845163303424635851 34279444267744955136953777)
        ·
          refine ⟨25709583200808716352715333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34279444267744955136953777 25709583200808716352715333)
          ·
            refine ⟨4820546850151634316134125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25709583200808716352715333 4820546850151634316134125)
            ·
              refine ⟨1807705068806862868550297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4820546850151634316134125 1807705068806862868550297)
              ·
                refine ⟨1355778801605147151412723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1807705068806862868550297 1355778801605147151412723)
                ·
                  refine ⟨2033668202407720727119085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1355778801605147151412723 2033668202407720727119085)
                  ·
                    refine ⟨762625575902895272669657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2033668202407720727119085 762625575902895272669657)
                    ·
                      rfl

theorem cell22_2227812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_2227812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227812 prefixEnd_2227812 := by exact prefixLift 2227812
  have htrace : WordTrace (prefixWord ++ tailWord_2227812) baseStart_2227812 baseEnd_2227812 := by
    simpa [prefixWord, tailWord_2227812, baseEnd_2227812] using wordTrace_append hprefix tailTrace_2227812
  have hstable : (prefixWord ++ tailWord_2227812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227812).length < 2 ^ (prefixWord ++ tailWord_2227812).sum := by decide
  have hdescent : baseEnd_2227812 < baseStart_2227812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227851 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 1, 5]
def baseStart_2227851 : Nat := 118140960795 + 2227851 * 2 ^ 59
def prefixEnd_2227851 : Nat := 4983230072969 + 3 ^ 40 * 2227851 * 2
def baseEnd_2227851 : Nat := 762638926399912170944537

theorem tailTrace_2227851 : CollatzResearch.WordTrace tailWord_2227851 prefixEnd_2227851 762638926399912170944537 := by
  unfold tailWord_2227851
  simp only [CollatzResearch.WordTrace]
  refine ⟨81256401451883788503819407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54170934301255859002546271 81256401451883788503819407)
  ·
    refine ⟨121884602177825682755729111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81256401451883788503819407 121884602177825682755729111)
    ·
      refine ⟨182826903266738524133593667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121884602177825682755729111 182826903266738524133593667)
      ·
        refine ⟨274240354900107786200390501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182826903266738524133593667 274240354900107786200390501)
        ·
          refine ⟨51420066543770209912573219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 274240354900107786200390501 51420066543770209912573219)
          ·
            refine ⟨77130099815655314868859829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51420066543770209912573219 77130099815655314868859829)
            ·
              refine ⟨7230946857717685768955609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77130099815655314868859829 7230946857717685768955609)
              ·
                refine ⟨5423210143288264326716707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7230946857717685768955609 5423210143288264326716707)
                ·
                  refine ⟨8134815214932396490075061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5423210143288264326716707 8134815214932396490075061)
                  ·
                    refine ⟨762638926399912170944537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8134815214932396490075061 762638926399912170944537)
                    ·
                      rfl

theorem cell22_2227851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_2227851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227851 prefixEnd_2227851 := by exact prefixLift 2227851
  have htrace : WordTrace (prefixWord ++ tailWord_2227851) baseStart_2227851 baseEnd_2227851 := by
    simpa [prefixWord, tailWord_2227851, baseEnd_2227851] using wordTrace_append hprefix tailTrace_2227851
  have hstable : (prefixWord ++ tailWord_2227851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227851).length < 2 ^ (prefixWord ++ tailWord_2227851).sum := by decide
  have hdescent : baseEnd_2227851 < baseStart_2227851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227885 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2227885 : Nat := 118140960795 + 2227885 * 2 ^ 59
def prefixEnd_2227885 : Nat := 4983230072969 + 3 ^ 40 * 2227885 * 2
def baseEnd_2227885 : Nat := 762650565294747415594433

theorem tailTrace_2227885 : CollatzResearch.WordTrace tailWord_2227885 prefixEnd_2227885 762650565294747415594433 := by
  unfold tailWord_2227885
  simp only [CollatzResearch.WordTrace]
  refine ⟨81257641533760612310557109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54171761022507074873704739 81257641533760612310557109)
  ·
    refine ⟨7617903893790057404114729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81257641533760612310557109 7617903893790057404114729)
    ·
      refine ⟨5713427920342543053086047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7617903893790057404114729 5713427920342543053086047)
      ·
        refine ⟨8570141880513814579629071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5713427920342543053086047 8570141880513814579629071)
        ·
          refine ⟨12855212820770721869443607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8570141880513814579629071 12855212820770721869443607)
          ·
            refine ⟨19282819231156082804165411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12855212820770721869443607 19282819231156082804165411)
            ·
              refine ⟨28924228846734124206248117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19282819231156082804165411 28924228846734124206248117)
              ·
                refine ⟨2711646454381324144335761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28924228846734124206248117 2711646454381324144335761)
                ·
                  refine ⟨2033734840785993108251821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2711646454381324144335761 2033734840785993108251821)
                  ·
                    refine ⟨762650565294747415594433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2033734840785993108251821 762650565294747415594433)
                    ·
                      rfl

theorem cell22_2227885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2227885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227885 prefixEnd_2227885 := by exact prefixLift 2227885
  have htrace : WordTrace (prefixWord ++ tailWord_2227885) baseStart_2227885 baseEnd_2227885 := by
    simpa [prefixWord, tailWord_2227885, baseEnd_2227885] using wordTrace_append hprefix tailTrace_2227885
  have hstable : (prefixWord ++ tailWord_2227885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227885).length < 2 ^ (prefixWord ++ tailWord_2227885).sum := by decide
  have hdescent : baseEnd_2227885 < baseStart_2227885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227898 : List Nat := [3, 1, 1, 1, 2, 5, 3, 6]
def baseStart_2227898 : Nat := 118140960795 + 2227898 * 2 ^ 59
def prefixEnd_2227898 : Nat := 4983230072969 + 3 ^ 40 * 2227898 * 2
def baseEnd_2227898 : Nat := 84739446162268857224377

theorem tailTrace_2227898 : CollatzResearch.WordTrace tailWord_2227898 prefixEnd_2227898 84739446162268857224377 := by
  unfold tailWord_2227898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20314528920678378882695087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54172077121809010353853565 20314528920678378882695087)
  ·
    refine ⟨30471793381017568324042631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20314528920678378882695087 30471793381017568324042631)
    ·
      refine ⟨45707690071526352486063947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30471793381017568324042631 45707690071526352486063947)
      ·
        refine ⟨68561535107289528729095921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45707690071526352486063947 68561535107289528729095921)
        ·
          refine ⟨51421151330467146546821941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68561535107289528729095921 51421151330467146546821941)
          ·
            refine ⟨4820732937231294988764557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51421151330467146546821941 4820732937231294988764557)
            ·
              refine ⟨1807774851461735620786709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4820732937231294988764557 1807774851461735620786709)
              ·
                refine ⟨84739446162268857224377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1807774851461735620786709 84739446162268857224377)
                ·
                  rfl

theorem cell22_2227898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_2227898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227898 prefixEnd_2227898 := by exact prefixLift 2227898
  have htrace : WordTrace (prefixWord ++ tailWord_2227898) baseStart_2227898 baseEnd_2227898 := by
    simpa [prefixWord, tailWord_2227898, baseEnd_2227898] using wordTrace_append hprefix tailTrace_2227898
  have hstable : (prefixWord ++ tailWord_2227898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227898).length < 2 ^ (prefixWord ++ tailWord_2227898).sum := by decide
  have hdescent : baseEnd_2227898 < baseStart_2227898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227900 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_2227900 : Nat := 118140960795 + 2227900 * 2 ^ 59
def prefixEnd_2227900 : Nat := 4983230072969 + 3 ^ 40 * 2227900 * 2
def baseEnd_2227900 : Nat := 762655700101292376469387

theorem tailTrace_2227900 : CollatzResearch.WordTrace tailWord_2227900 prefixEnd_2227900 762655700101292376469387 := by
  unfold tailWord_2227900
  simp only [CollatzResearch.WordTrace]
  refine ⟨40629094314353134936176577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54172125752470846581568769 40629094314353134936176577)
  ·
    refine ⟨30471820735764851202132433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40629094314353134936176577 30471820735764851202132433)
    ·
      refine ⟨22853865551823638401599325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30471820735764851202132433 22853865551823638401599325)
      ·
        refine ⟨8570199581933864400599747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22853865551823638401599325 8570199581933864400599747)
        ·
          refine ⟨12855299372900796600899621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8570199581933864400599747 12855299372900796600899621)
          ·
            refine ⟨2410368632418899362668679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12855299372900796600899621 2410368632418899362668679)
            ·
              refine ⟨3615552948628349044003019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410368632418899362668679 3615552948628349044003019)
              ·
                refine ⟨5423329422942523566004529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615552948628349044003019 5423329422942523566004529)
                ·
                  refine ⟨4067497067206892674503397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5423329422942523566004529 4067497067206892674503397)
                  ·
                    refine ⟨762655700101292376469387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4067497067206892674503397 762655700101292376469387)
                    ·
                      rfl

theorem cell22_2227900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_2227900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227900 prefixEnd_2227900 := by exact prefixLift 2227900
  have htrace : WordTrace (prefixWord ++ tailWord_2227900) baseStart_2227900 baseEnd_2227900 := by
    simpa [prefixWord, tailWord_2227900, baseEnd_2227900] using wordTrace_append hprefix tailTrace_2227900
  have hstable : (prefixWord ++ tailWord_2227900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227900).length < 2 ^ (prefixWord ++ tailWord_2227900).sum := by decide
  have hdescent : baseEnd_2227900 < baseStart_2227900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227930 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_2227930 : Nat := 118140960795 + 2227930 * 2 ^ 59
def prefixEnd_2227930 : Nat := 4983230072969 + 3 ^ 40 * 2227930 * 2
def baseEnd_2227930 : Nat := 762665969714382298219295

theorem tailTrace_2227930 : CollatzResearch.WordTrace tailWord_2227930 prefixEnd_2227930 762665969714382298219295 := by
  unfold tailWord_2227930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20314820704649396248986311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54172855212398389997296829 20314820704649396248986311)
  ·
    refine ⟨30472231056974094373479467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20314820704649396248986311 30472231056974094373479467)
    ·
      refine ⟨45708346585461141560219201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30472231056974094373479467 45708346585461141560219201)
      ·
        refine ⟨34281259939095856170164401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45708346585461141560219201 34281259939095856170164401)
        ·
          refine ⟨25710944954321892127623301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34281259939095856170164401 25710944954321892127623301)
          ·
            refine ⟨4820802178935354773929369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25710944954321892127623301 4820802178935354773929369)
            ·
              refine ⟨3615601634201516080447027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4820802178935354773929369 3615601634201516080447027)
              ·
                refine ⟨5423402451302274120670541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615601634201516080447027 5423402451302274120670541)
                ·
                  refine ⟨2033775919238352795251453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5423402451302274120670541 2033775919238352795251453)
                  ·
                    refine ⟨762665969714382298219295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2033775919238352795251453 762665969714382298219295)
                    ·
                      rfl

theorem cell22_2227930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_2227930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227930 prefixEnd_2227930 := by exact prefixLift 2227930
  have htrace : WordTrace (prefixWord ++ tailWord_2227930) baseStart_2227930 baseEnd_2227930 := by
    simpa [prefixWord, tailWord_2227930, baseEnd_2227930] using wordTrace_append hprefix tailTrace_2227930
  have hstable : (prefixWord ++ tailWord_2227930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227930).length < 2 ^ (prefixWord ++ tailWord_2227930).sum := by decide
  have hdescent : baseEnd_2227930 < baseStart_2227930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2227971 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 8]
def baseStart_2227971 : Nat := 118140960795 + 2227971 * 2 ^ 59
def prefixEnd_2227971 : Nat := 4983230072969 + 3 ^ 40 * 2227971 * 2
def baseEnd_2227971 : Nat := 254226668284090619314723

theorem tailTrace_2227971 : CollatzResearch.WordTrace tailWord_2227971 prefixEnd_2227971 254226668284090619314723 := by
  unfold tailWord_2227971
  simp only [CollatzResearch.WordTrace]
  refine ⟨81260778211449048998187767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54173852140966032665458511 81260778211449048998187767)
  ·
    refine ⟨121891167317173573497281651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81260778211449048998187767 121891167317173573497281651)
    ·
      refine ⟨182836750975760360245922477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121891167317173573497281651 182836750975760360245922477)
      ·
        refine ⟨68563781615910135092220929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182836750975760360245922477 68563781615910135092220929)
        ·
          refine ⟨51422836211932601319165697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68563781615910135092220929 51422836211932601319165697)
          ·
            refine ⟨38567127158949450989374273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51422836211932601319165697 38567127158949450989374273)
            ·
              refine ⟨28925345369212088242030705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38567127158949450989374273 28925345369212088242030705)
              ·
                refine ⟨21694009026909066181523029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28925345369212088242030705 21694009026909066181523029)
                ·
                  refine ⟨254226668284090619314723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21694009026909066181523029 254226668284090619314723)
                  ·
                    rfl

theorem cell22_2227971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_2227971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2227971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2227971 prefixEnd_2227971 := by exact prefixLift 2227971
  have htrace : WordTrace (prefixWord ++ tailWord_2227971) baseStart_2227971 baseEnd_2227971 := by
    simpa [prefixWord, tailWord_2227971, baseEnd_2227971] using wordTrace_append hprefix tailTrace_2227971
  have hstable : (prefixWord ++ tailWord_2227971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2227971).length < 2 ^ (prefixWord ++ tailWord_2227971).sum := by decide
  have hdescent : baseEnd_2227971 < baseStart_2227971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2227971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228020 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2228020 : Nat := 118140960795 + 2228020 * 2 ^ 59
def prefixEnd_2228020 : Nat := 4983230072969 + 3 ^ 40 * 2228020 * 2
def baseEnd_2228020 : Nat := 762696778553652063469019

theorem tailTrace_2228020 : CollatzResearch.WordTrace tailWord_2228020 prefixEnd_2228020 762696778553652063469019 := by
  unfold tailWord_2228020
  simp only [CollatzResearch.WordTrace]
  refine ⟨40631282694135765183360757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54175043592181020244481009 40631282694135765183360757)
  ·
    refine ⟨3809182752575227985940071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40631282694135765183360757 3809182752575227985940071)
    ·
      refine ⟨5713774128862841978910107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3809182752575227985940071 5713774128862841978910107)
      ·
        refine ⟨8570661193294262968365161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5713774128862841978910107 8570661193294262968365161)
        ·
          refine ⟨6427995894970697226273871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8570661193294262968365161 6427995894970697226273871)
          ·
            refine ⟨9641993842456045839410807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6427995894970697226273871 9641993842456045839410807)
            ·
              refine ⟨14462990763684068759116211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9641993842456045839410807 14462990763684068759116211)
              ·
                refine ⟨21694486145526103138674317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14462990763684068759116211 21694486145526103138674317)
                ·
                  refine ⟨8135432304572288677002869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21694486145526103138674317 8135432304572288677002869)
                  ·
                    refine ⟨762696778553652063469019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8135432304572288677002869 762696778553652063469019)
                    ·
                      rfl

theorem cell22_2228020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2228020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228020 prefixEnd_2228020 := by exact prefixLift 2228020
  have htrace : WordTrace (prefixWord ++ tailWord_2228020) baseStart_2228020 baseEnd_2228020 := by
    simpa [prefixWord, tailWord_2228020, baseEnd_2228020] using wordTrace_append hprefix tailTrace_2228020
  have hstable : (prefixWord ++ tailWord_2228020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228020).length < 2 ^ (prefixWord ++ tailWord_2228020).sum := by decide
  have hdescent : baseEnd_2228020 < baseStart_2228020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228050 : List Nat := [3, 2, 2, 1, 1, 5, 1, 7]
def baseStart_2228050 : Nat := 118140960795 + 2228050 * 2 ^ 59
def prefixEnd_2228050 : Nat := 4983230072969 + 3 ^ 40 * 2228050 * 2
def baseEnd_2228050 : Nat := 84745227574082442802103

theorem tailTrace_2228050 : CollatzResearch.WordTrace tailWord_2228050 prefixEnd_2228050 84745227574082442802103 := by
  unfold tailWord_2228050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315914894540711372578401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54175773052108563660209069 20315914894540711372578401)
  ·
    refine ⟨15236936170905533529433801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20315914894540711372578401 15236936170905533529433801)
    ·
      refine ⟨11427702128179150147075351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15236936170905533529433801 11427702128179150147075351)
      ·
        refine ⟨17141553192268725220613027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11427702128179150147075351 17141553192268725220613027)
        ·
          refine ⟨25712329788403087830919541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17141553192268725220613027 25712329788403087830919541)
          ·
            refine ⟨2410530917662789484148707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25712329788403087830919541 2410530917662789484148707)
            ·
              refine ⟨3615796376494184226223061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410530917662789484148707 3615796376494184226223061)
              ·
                refine ⟨84745227574082442802103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3615796376494184226223061 84745227574082442802103)
                ·
                  rfl

theorem cell22_2228050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_2228050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228050 prefixEnd_2228050 := by exact prefixLift 2228050
  have htrace : WordTrace (prefixWord ++ tailWord_2228050) baseStart_2228050 baseEnd_2228050 := by
    simpa [prefixWord, tailWord_2228050, baseEnd_2228050] using wordTrace_append hprefix tailTrace_2228050
  have hstable : (prefixWord ++ tailWord_2228050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228050).length < 2 ^ (prefixWord ++ tailWord_2228050).sum := by decide
  have hdescent : baseEnd_2228050 < baseStart_2228050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228065 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 3, 3]
def baseStart_2228065 : Nat := 118140960795 + 2228065 * 2 ^ 59
def prefixEnd_2228065 : Nat := 4983230072969 + 3 ^ 40 * 2228065 * 2
def baseEnd_2228065 : Nat := 762712182973286946093881

theorem tailTrace_2228065 : CollatzResearch.WordTrace tailWord_2228065 prefixEnd_2228065 762712182973286946093881 := by
  unfold tailWord_2228065
  simp only [CollatzResearch.WordTrace]
  refine ⟨81264206673108503052109649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54176137782072335368073099 81264206673108503052109649)
  ·
    refine ⟨60948155004831377289082237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81264206673108503052109649 60948155004831377289082237)
    ·
      refine ⟨22855558126811766483405839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60948155004831377289082237 22855558126811766483405839)
      ·
        refine ⟨34283337190217649725108759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22855558126811766483405839 34283337190217649725108759)
        ·
          refine ⟨51425005785326474587663139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34283337190217649725108759 51425005785326474587663139)
          ·
            refine ⟨77137508677989711881494709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51425005785326474587663139 77137508677989711881494709)
            ·
              refine ⟨7231641438561535488890129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77137508677989711881494709 7231641438561535488890129)
              ·
                refine ⟨5423731078921151616667597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7231641438561535488890129 5423731078921151616667597)
                ·
                  refine ⟨2033899154595431856250349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5423731078921151616667597 2033899154595431856250349)
                  ·
                    refine ⟨762712182973286946093881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2033899154595431856250349 762712182973286946093881)
                    ·
                      rfl

theorem cell22_2228065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_2228065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228065 prefixEnd_2228065 := by exact prefixLift 2228065
  have htrace : WordTrace (prefixWord ++ tailWord_2228065) baseStart_2228065 baseEnd_2228065 := by
    simpa [prefixWord, tailWord_2228065, baseEnd_2228065] using wordTrace_append hprefix tailTrace_2228065
  have hstable : (prefixWord ++ tailWord_2228065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228065).length < 2 ^ (prefixWord ++ tailWord_2228065).sum := by decide
  have hdescent : baseEnd_2228065 < baseStart_2228065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228118 : List Nat := [5, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2228118 : Nat := 118140960795 + 2228118 * 2 ^ 59
def prefixEnd_2228118 : Nat := 4983230072969 + 3 ^ 40 * 2228118 * 2
def baseEnd_2228118 : Nat := 84747813995156941613191

theorem tailTrace_2228118 : CollatzResearch.WordTrace tailWord_2228118 prefixEnd_2228118 84747813995156941613191 := by
  unfold tailWord_2228118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5079133733869780818986813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54177426494610995402526005 5079133733869780818986813)
  ·
    refine ⟨1904675150201167807120055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5079133733869780818986813 1904675150201167807120055)
    ·
      refine ⟨2857012725301751710680083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1904675150201167807120055 2857012725301751710680083)
      ·
        refine ⟨4285519087952627566020125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857012725301751710680083 4285519087952627566020125)
        ·
          refine ⟨1607069657982235337257547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4285519087952627566020125 1607069657982235337257547)
          ·
            refine ⟨2410604486973353005886321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607069657982235337257547 2410604486973353005886321)
            ·
              refine ⟨1807953365230014754414741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410604486973353005886321 1807953365230014754414741)
              ·
                refine ⟨84747813995156941613191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1807953365230014754414741 84747813995156941613191)
                ·
                  rfl

theorem cell22_2228118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2228118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228118 prefixEnd_2228118 := by exact prefixLift 2228118
  have htrace : WordTrace (prefixWord ++ tailWord_2228118) baseStart_2228118 baseEnd_2228118 := by
    simpa [prefixWord, tailWord_2228118, baseEnd_2228118] using wordTrace_append hprefix tailTrace_2228118
  have hstable : (prefixWord ++ tailWord_2228118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228118).length < 2 ^ (prefixWord ++ tailWord_2228118).sum := by decide
  have hdescent : baseEnd_2228118 < baseStart_2228118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228157 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2228157 : Nat := 118140960795 + 2228157 * 2 ^ 59
def prefixEnd_2228157 : Nat := 4983230072969 + 3 ^ 40 * 2228157 * 2
def baseEnd_2228157 : Nat := 254247892151143124264533

theorem tailTrace_2228157 : CollatzResearch.WordTrace tailWord_2228157 prefixEnd_2228157 254247892151143124264533 := by
  unfold tailWord_2228157
  simp only [CollatzResearch.WordTrace]
  refine ⟨81267562188775202764458725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54178374792516801842972483 81267562188775202764458725)
  ·
    refine ⟨15237667910395350518336011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81267562188775202764458725 15237667910395350518336011)
    ·
      refine ⟨22856501865593025777504017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15237667910395350518336011 22856501865593025777504017)
      ·
        refine ⟨17142376399194769333128013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22856501865593025777504017 17142376399194769333128013)
        ·
          refine ⟨6428391149698038499923005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17142376399194769333128013 6428391149698038499923005)
          ·
            refine ⟨2410646681136764437471127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6428391149698038499923005 2410646681136764437471127)
            ·
              refine ⟨3615970021705146656206691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410646681136764437471127 3615970021705146656206691)
              ·
                refine ⟨5423955032557719984310037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615970021705146656206691 5423955032557719984310037)
                ·
                  refine ⟨254247892151143124264533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5423955032557719984310037 254247892151143124264533)
                  ·
                    rfl

theorem cell22_2228157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2228157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228157 prefixEnd_2228157 := by exact prefixLift 2228157
  have htrace : WordTrace (prefixWord ++ tailWord_2228157) baseStart_2228157 baseEnd_2228157 := by
    simpa [prefixWord, tailWord_2228157, baseEnd_2228157] using wordTrace_append hprefix tailTrace_2228157
  have hstable : (prefixWord ++ tailWord_2228157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228157).length < 2 ^ (prefixWord ++ tailWord_2228157).sum := by decide
  have hdescent : baseEnd_2228157 < baseStart_2228157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228234 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_2228234 : Nat := 118140960795 + 2228234 * 2 ^ 59
def prefixEnd_2228234 : Nat := 4983230072969 + 3 ^ 40 * 2228234 * 2
def baseEnd_2228234 : Nat := 762770035127026838618363

theorem tailTrace_2228234 : CollatzResearch.WordTrace tailWord_2228234 prefixEnd_2228234 762770035127026838618363 := by
  unfold tailWord_2228234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20317592652374061228752939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54180247072997496610007837 20317592652374061228752939)
  ·
    refine ⟨30476388978561091843129409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20317592652374061228752939 30476388978561091843129409)
    ·
      refine ⟨22857291733920818882347057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30476388978561091843129409 22857291733920818882347057)
      ·
        refine ⟨17142968800440614161760293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22857291733920818882347057 17142968800440614161760293)
        ·
          refine ⟨3214306650082615155330055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17142968800440614161760293 3214306650082615155330055)
          ·
            refine ⟨4821459975123922732995083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214306650082615155330055 4821459975123922732995083)
            ·
              refine ⟨7232189962685884099492625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821459975123922732995083 7232189962685884099492625)
              ·
                refine ⟨5424142472014413074619469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7232189962685884099492625 5424142472014413074619469)
                ·
                  refine ⟨2034053427005404902982301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5424142472014413074619469 2034053427005404902982301)
                  ·
                    refine ⟨762770035127026838618363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034053427005404902982301 762770035127026838618363)
                    ·
                      rfl

theorem cell22_2228234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_2228234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228234 prefixEnd_2228234 := by exact prefixLift 2228234
  have htrace : WordTrace (prefixWord ++ tailWord_2228234) baseStart_2228234 baseEnd_2228234 := by
    simpa [prefixWord, tailWord_2228234, baseEnd_2228234] using wordTrace_append hprefix tailTrace_2228234
  have hstable : (prefixWord ++ tailWord_2228234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228234).length < 2 ^ (prefixWord ++ tailWord_2228234).sum := by decide
  have hdescent : baseEnd_2228234 < baseStart_2228234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228264 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 7]
def baseStart_2228264 : Nat := 118140960795 + 2228264 * 2 ^ 59
def prefixEnd_2228264 : Nat := 4983230072969 + 3 ^ 40 * 2228264 * 2
def baseEnd_2228264 : Nat := 254260101580038920122757

theorem tailTrace_2228264 : CollatzResearch.WordTrace tailWord_2228264 prefixEnd_2228264 254260101580038920122757 := by
  unfold tailWord_2228264
  simp only [CollatzResearch.WordTrace]
  refine ⟨40635732399693780019301923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54180976532925040025735897 40635732399693780019301923)
  ·
    refine ⟨60953598599540670028952885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40635732399693780019301923 60953598599540670028952885)
    ·
      refine ⟨5714399868706937815214333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60953598599540670028952885 5714399868706937815214333)
      ·
        refine ⟨2142899950765101680705375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5714399868706937815214333 2142899950765101680705375)
        ·
          refine ⟨3214349926147652521058063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142899950765101680705375 3214349926147652521058063)
          ·
            refine ⟨4821524889221478781587095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214349926147652521058063 4821524889221478781587095)
            ·
              refine ⟨7232287333832218172380643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821524889221478781587095 7232287333832218172380643)
              ·
                refine ⟨10848431000748327258570965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7232287333832218172380643 10848431000748327258570965)
                ·
                  refine ⟨254260101580038920122757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10848431000748327258570965 254260101580038920122757)
                  ·
                    rfl

theorem cell22_2228264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_2228264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228264 prefixEnd_2228264 := by exact prefixLift 2228264
  have htrace : WordTrace (prefixWord ++ tailWord_2228264) baseStart_2228264 baseEnd_2228264 := by
    simpa [prefixWord, tailWord_2228264, baseEnd_2228264] using wordTrace_append hprefix tailTrace_2228264
  have hstable : (prefixWord ++ tailWord_2228264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228264).length < 2 ^ (prefixWord ++ tailWord_2228264).sum := by decide
  have hdescent : baseEnd_2228264 < baseStart_2228264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228275 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 6]
def baseStart_2228275 : Nat := 118140960795 + 2228275 * 2 ^ 59
def prefixEnd_2228275 : Nat := 4983230072969 + 3 ^ 40 * 2228275 * 2
def baseEnd_2228275 : Nat := 254261356754972132781079

theorem tailTrace_2228275 : CollatzResearch.WordTrace tailWord_2228275 prefixEnd_2228275 254261356754972132781079 := by
  unfold tailWord_2228275
  simp only [CollatzResearch.WordTrace]
  refine ⟨81271866002347708917254279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54181244001565139278169519 81271866002347708917254279)
  ·
    refine ⟨121907799003521563375881419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81271866002347708917254279 121907799003521563375881419)
    ·
      refine ⟨182861698505282345063822129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121907799003521563375881419 182861698505282345063822129)
      ·
        refine ⟨137146273878961758797866597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182861698505282345063822129 137146273878961758797866597)
        ·
          refine ⟨25714926352305329774599987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137146273878961758797866597 25714926352305329774599987)
          ·
            refine ⟨38572389528457994661899981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25714926352305329774599987 38572389528457994661899981)
            ·
              refine ⟨14464646073171747998212493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38572389528457994661899981 14464646073171747998212493)
              ·
                refine ⟨5424242277439405499329685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14464646073171747998212493 5424242277439405499329685)
                ·
                  refine ⟨254261356754972132781079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5424242277439405499329685 254261356754972132781079)
                  ·
                    rfl

theorem cell22_2228275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 6].length) (baseStart_2228275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228275 prefixEnd_2228275 := by exact prefixLift 2228275
  have htrace : WordTrace (prefixWord ++ tailWord_2228275) baseStart_2228275 baseEnd_2228275 := by
    simpa [prefixWord, tailWord_2228275, baseEnd_2228275] using wordTrace_append hprefix tailTrace_2228275
  have hstable : (prefixWord ++ tailWord_2228275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228275).length < 2 ^ (prefixWord ++ tailWord_2228275).sum := by decide
  have hdescent : baseEnd_2228275 < baseStart_2228275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228309 : List Nat := [1, 3, 2, 2, 1, 3, 3, 3, 4]
def baseStart_2228309 : Nat := 118140960795 + 2228309 * 2 ^ 59
def prefixEnd_2228309 : Nat := 4983230072969 + 3 ^ 40 * 2228309 * 2
def baseEnd_2228309 : Nat := 254265236386583880997711

theorem tailTrace_2228309 : CollatzResearch.WordTrace tailWord_2228309 prefixEnd_2228309 254265236386583880997711 := by
  unfold tailWord_2228309
  simp only [CollatzResearch.WordTrace]
  refine ⟨81273106084224532723991981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54182070722816355149327987 81273106084224532723991981)
  ·
    refine ⟨30477414781584199771496993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81273106084224532723991981 30477414781584199771496993)
    ·
      refine ⟨22858061086188149828622745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30477414781584199771496993 22858061086188149828622745)
      ·
        refine ⟨17143545814641112371467059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22858061086188149828622745 17143545814641112371467059)
        ·
          refine ⟨25715318721961668557200589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17143545814641112371467059 25715318721961668557200589)
          ·
            refine ⟨9643244520735625708950221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25715318721961668557200589 9643244520735625708950221)
            ·
              refine ⟨3616216695275859640856333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9643244520735625708950221 3616216695275859640856333)
              ·
                refine ⟨1356081260728447365321125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3616216695275859640856333 1356081260728447365321125)
                ·
                  refine ⟨254265236386583880997711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356081260728447365321125 254265236386583880997711)
                  ·
                    rfl

theorem cell22_2228309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_2228309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228309 prefixEnd_2228309 := by exact prefixLift 2228309
  have htrace : WordTrace (prefixWord ++ tailWord_2228309) baseStart_2228309 baseEnd_2228309 := by
    simpa [prefixWord, tailWord_2228309, baseEnd_2228309] using wordTrace_append hprefix tailTrace_2228309
  have hstable : (prefixWord ++ tailWord_2228309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228309).length < 2 ^ (prefixWord ++ tailWord_2228309).sum := by decide
  have hdescent : baseEnd_2228309 < baseStart_2228309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228320 : List Nat := [2, 1, 1, 3, 2, 3, 10]
def baseStart_2228320 : Nat := 118140960795 + 2228320 * 2 ^ 59
def prefixEnd_2228320 : Nat := 4983230072969 + 3 ^ 40 * 2228320 * 2
def baseEnd_2228320 : Nat := 28251832395724121517337

theorem tailTrace_2228320 : CollatzResearch.WordTrace tailWord_2228320 prefixEnd_2228320 28251832395724121517337 := by
  unfold tailWord_2228320
  simp only [CollatzResearch.WordTrace]
  refine ⟨40636753643592340801321207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54182338191456454401761609 40636753643592340801321207)
  ·
    refine ⟨60955130465388511201981811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40636753643592340801321207 60955130465388511201981811)
    ·
      refine ⟨91432695698082766802972717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60955130465388511201981811 91432695698082766802972717)
      ·
        refine ⟨34287260886781037551114769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91432695698082766802972717 34287260886781037551114769)
        ·
          refine ⟨25715445665085778163336077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34287260886781037551114769 25715445665085778163336077)
          ·
            refine ⟨9643292124407166811251029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25715445665085778163336077 9643292124407166811251029)
            ·
              refine ⟨28251832395724121517337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9643292124407166811251029 28251832395724121517337)
              ·
                rfl

theorem cell22_2228320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 10].length) (baseStart_2228320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228320 prefixEnd_2228320 := by exact prefixLift 2228320
  have htrace : WordTrace (prefixWord ++ tailWord_2228320) baseStart_2228320 baseEnd_2228320 := by
    simpa [prefixWord, tailWord_2228320, baseEnd_2228320] using wordTrace_append hprefix tailTrace_2228320
  have hstable : (prefixWord ++ tailWord_2228320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228320).length < 2 ^ (prefixWord ++ tailWord_2228320).sum := by decide
  have hdescent : baseEnd_2228320 < baseStart_2228320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228352 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 5, 3]
def baseStart_2228352 : Nat := 118140960795 + 2228352 * 2 ^ 59
def prefixEnd_2228352 : Nat := 4983230072969 + 3 ^ 40 * 2228352 * 2
def baseEnd_2228352 : Nat := 762810428938513864168001

theorem tailTrace_2228352 : CollatzResearch.WordTrace tailWord_2228352 prefixEnd_2228352 762810428938513864168001 := by
  unfold tailWord_2228352
  simp only [CollatzResearch.WordTrace]
  refine ⟨40637337211534375533903655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54183116282045834045204873 40637337211534375533903655)
  ·
    refine ⟨60956005817301563300855483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40637337211534375533903655 60956005817301563300855483)
    ·
      refine ⟨91434008725952344951283225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60956005817301563300855483 91434008725952344951283225)
      ·
        refine ⟨68575506544464258713462419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91434008725952344951283225 68575506544464258713462419)
        ·
          refine ⟨102863259816696388070193629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68575506544464258713462419 102863259816696388070193629)
          ·
            refine ⟨38573722431261145526322611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102863259816696388070193629 38573722431261145526322611)
            ·
              refine ⟨57860583646891718289483917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38573722431261145526322611 57860583646891718289483917)
              ·
                refine ⟨21697718867584394358556469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57860583646891718289483917 21697718867584394358556469)
                ·
                  refine ⟨2034161143836036971114669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21697718867584394358556469 2034161143836036971114669)
                  ·
                    refine ⟨762810428938513864168001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034161143836036971114669 762810428938513864168001)
                    ·
                      rfl

theorem cell22_2228352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_2228352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228352 prefixEnd_2228352 := by exact prefixLift 2228352
  have htrace : WordTrace (prefixWord ++ tailWord_2228352) baseStart_2228352 baseEnd_2228352 := by
    simpa [prefixWord, tailWord_2228352, baseEnd_2228352] using wordTrace_append hprefix tailTrace_2228352
  have hstable : (prefixWord ++ tailWord_2228352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228352).length < 2 ^ (prefixWord ++ tailWord_2228352).sum := by decide
  have hdescent : baseEnd_2228352 < baseStart_2228352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228442 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_2228442 : Nat := 118140960795 + 2228442 * 2 ^ 59
def prefixEnd_2228442 : Nat := 4983230072969 + 3 ^ 40 * 2228442 * 2
def baseEnd_2228442 : Nat := 762841237777783629417725

theorem tailTrace_2228442 : CollatzResearch.WordTrace tailWord_2228442 prefixEnd_2228442 762841237777783629417725 := by
  unfold tailWord_2228442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20319489248185674109645895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54185304661828464292389053 20319489248185674109645895)
  ·
    refine ⟨30479233872278511164468843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20319489248185674109645895 30479233872278511164468843)
    ·
      refine ⟨45718850808417766746703265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30479233872278511164468843 45718850808417766746703265)
      ·
        refine ⟨34289138106313325060027449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45718850808417766746703265 34289138106313325060027449)
        ·
          refine ⟨25716853579734993795020587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34289138106313325060027449 25716853579734993795020587)
          ·
            refine ⟨38575280369602490692530881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25716853579734993795020587 38575280369602490692530881)
            ·
              refine ⟨28931460277201868019398161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38575280369602490692530881 28931460277201868019398161)
              ·
                refine ⟨21698595207901401014548621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28931460277201868019398161 21698595207901401014548621)
                ·
                  refine ⟨8136973202963025380455733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21698595207901401014548621 8136973202963025380455733)
                  ·
                    refine ⟨762841237777783629417725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8136973202963025380455733 762841237777783629417725)
                    ·
                      rfl

theorem cell22_2228442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_2228442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228442 prefixEnd_2228442 := by exact prefixLift 2228442
  have htrace : WordTrace (prefixWord ++ tailWord_2228442) baseStart_2228442 baseEnd_2228442 := by
    simpa [prefixWord, tailWord_2228442, baseEnd_2228442] using wordTrace_append hprefix tailTrace_2228442
  have hstable : (prefixWord ++ tailWord_2228442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228442).length < 2 ^ (prefixWord ++ tailWord_2228442).sum := by decide
  have hdescent : baseEnd_2228442 < baseStart_2228442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228457 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_2228457 : Nat := 118140960795 + 2228457 * 2 ^ 59
def prefixEnd_2228457 : Nat := 4983230072969 + 3 ^ 40 * 2228457 * 2
def baseEnd_2228457 : Nat := 762846372584328590292679

theorem tailTrace_2228457 : CollatzResearch.WordTrace tailWord_2228457 prefixEnd_2228457 762846372584328590292679 := by
  unfold tailWord_2228457
  simp only [CollatzResearch.WordTrace]
  refine ⟨81278504087688354000379625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54185669391792236000253083 81278504087688354000379625)
  ·
    refine ⟨60958878065766265500284719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81278504087688354000379625 60958878065766265500284719)
    ·
      refine ⟨91438317098649398250427079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60958878065766265500284719 91438317098649398250427079)
      ·
        refine ⟨137157475647974097375640619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91438317098649398250427079 137157475647974097375640619)
        ·
          refine ⟨205736213471961146063460929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137157475647974097375640619 205736213471961146063460929)
          ·
            refine ⟨154302160103970859547595697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205736213471961146063460929 154302160103970859547595697)
            ·
              refine ⟨115726620077978144660696773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154302160103970859547595697 115726620077978144660696773)
              ·
                refine ⟨21698741264620902123880645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115726620077978144660696773 21698741264620902123880645)
                ·
                  refine ⟨4068513987116419148227621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21698741264620902123880645 4068513987116419148227621)
                  ·
                    refine ⟨762846372584328590292679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4068513987116419148227621 762846372584328590292679)
                    ·
                      rfl

theorem cell22_2228457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_2228457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228457 prefixEnd_2228457 := by exact prefixLift 2228457
  have htrace : WordTrace (prefixWord ++ tailWord_2228457) baseStart_2228457 baseEnd_2228457 := by
    simpa [prefixWord, tailWord_2228457, baseEnd_2228457] using wordTrace_append hprefix tailTrace_2228457
  have hstable : (prefixWord ++ tailWord_2228457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228457).length < 2 ^ (prefixWord ++ tailWord_2228457).sum := by decide
  have hdescent : baseEnd_2228457 < baseStart_2228457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228510 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2228510 : Nat := 118140960795 + 2228510 * 2 ^ 59
def prefixEnd_2228510 : Nat := 4983230072969 + 3 ^ 40 * 2228510 * 2
def baseEnd_2228510 : Nat := 762864515567454118717517

theorem tailTrace_2228510 : CollatzResearch.WordTrace tailWord_2228510 prefixEnd_2228510 762864515567454118717517 := by
  unfold tailWord_2228510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10160054644562043006507373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54186958104330896034705989 10160054644562043006507373)
  ·
    refine ⟨3810020491710766127440265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10160054644562043006507373 3810020491710766127440265)
    ·
      refine ⟨2857515368783074595580199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3810020491710766127440265 2857515368783074595580199)
      ·
        refine ⟨4286273053174611893370299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857515368783074595580199 4286273053174611893370299)
        ·
          refine ⟨6429409579761917840055449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4286273053174611893370299 6429409579761917840055449)
          ·
            refine ⟨4822057184821438380041587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6429409579761917840055449 4822057184821438380041587)
            ·
              refine ⟨7233085777232157570062381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4822057184821438380041587 7233085777232157570062381)
              ·
                refine ⟨2712407166462059088773393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7233085777232157570062381 2712407166462059088773393)
                ·
                  refine ⟨2034305374846544316580045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2712407166462059088773393 2034305374846544316580045)
                  ·
                    refine ⟨762864515567454118717517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034305374846544316580045 762864515567454118717517)
                    ·
                      rfl

theorem cell22_2228510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2228510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228510 prefixEnd_2228510 := by exact prefixLift 2228510
  have htrace : WordTrace (prefixWord ++ tailWord_2228510) baseStart_2228510 baseEnd_2228510 := by
    simpa [prefixWord, tailWord_2228510, baseEnd_2228510] using wordTrace_append hprefix tailTrace_2228510
  have hstable : (prefixWord ++ tailWord_2228510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228510).length < 2 ^ (prefixWord ++ tailWord_2228510).sum := by decide
  have hdescent : baseEnd_2228510 < baseStart_2228510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228579 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 6]
def baseStart_2228579 : Nat := 118140960795 + 2228579 * 2 ^ 59
def prefixEnd_2228579 : Nat := 4983230072969 + 3 ^ 40 * 2228579 * 2
def baseEnd_2228579 : Nat := 254296045225853646247435

theorem tailTrace_2228579 : CollatzResearch.WordTrace tailWord_2228579 prefixEnd_2228579 254296045225853646247435 := by
  unfold tailWord_2228579
  simp only [CollatzResearch.WordTrace]
  refine ⟨81282953793246368836320791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54188635862164245890880527 81282953793246368836320791)
  ·
    refine ⟨121924430689869553254481187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81282953793246368836320791 121924430689869553254481187)
    ·
      refine ⟨182886646034804329881721781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121924430689869553254481187 182886646034804329881721781)
      ·
        refine ⟨17145623065762905926411417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182886646034804329881721781 17145623065762905926411417)
        ·
          refine ⟨12859217299322179444808563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17145623065762905926411417 12859217299322179444808563)
          ·
            refine ⟨19288825948983269167212845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12859217299322179444808563 19288825948983269167212845)
            ·
              refine ⟨7233309730868725937704817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19288825948983269167212845 7233309730868725937704817)
              ·
                refine ⟨5424982298151544453278613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7233309730868725937704817 5424982298151544453278613)
                ·
                  refine ⟨254296045225853646247435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5424982298151544453278613 254296045225853646247435)
                  ·
                    rfl

theorem cell22_2228579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 6].length) (baseStart_2228579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228579 prefixEnd_2228579 := by exact prefixLift 2228579
  have htrace : WordTrace (prefixWord ++ tailWord_2228579) baseStart_2228579 baseEnd_2228579 := by
    simpa [prefixWord, tailWord_2228579, baseEnd_2228579] using wordTrace_append hprefix tailTrace_2228579
  have hstable : (prefixWord ++ tailWord_2228579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228579).length < 2 ^ (prefixWord ++ tailWord_2228579).sum := by decide
  have hdescent : baseEnd_2228579 < baseStart_2228579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228639 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 2, 7]
def baseStart_2228639 : Nat := 118140960795 + 2228639 * 2 ^ 59
def prefixEnd_2228639 : Nat := 4983230072969 + 3 ^ 40 * 2228639 * 2
def baseEnd_2228639 : Nat := 762908674903740782242121

theorem tailTrace_2228639 : CollatzResearch.WordTrace tailWord_2228639 prefixEnd_2228639 762908674903740782242121 := by
  unfold tailWord_2228639
  simp only [CollatzResearch.WordTrace]
  refine ⟨81285142173028999083504971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54190094782019332722336647 81285142173028999083504971)
  ·
    refine ⟨121927713259543498625257457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81285142173028999083504971 121927713259543498625257457)
    ·
      refine ⟨91445784944657623968943093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121927713259543498625257457 91445784944657623968943093)
      ·
        refine ⟨8573042338561652247088415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91445784944657623968943093 8573042338561652247088415)
        ·
          refine ⟨12859563507842478370632623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573042338561652247088415 12859563507842478370632623)
          ·
            refine ⟨19289345261763717555948935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12859563507842478370632623 19289345261763717555948935)
            ·
              refine ⟨28934017892645576333923403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19289345261763717555948935 28934017892645576333923403)
              ·
                refine ⟨43401026838968364500885105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28934017892645576333923403 43401026838968364500885105)
                ·
                  refine ⟨32550770129226273375663829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43401026838968364500885105 32550770129226273375663829)
                  ·
                    refine ⟨762908674903740782242121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32550770129226273375663829 762908674903740782242121)
                    ·
                      rfl

theorem cell22_2228639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_2228639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228639 prefixEnd_2228639 := by exact prefixLift 2228639
  have htrace : WordTrace (prefixWord ++ tailWord_2228639) baseStart_2228639 baseEnd_2228639 := by
    simpa [prefixWord, tailWord_2228639, baseEnd_2228639] using wordTrace_append hprefix tailTrace_2228639
  have hstable : (prefixWord ++ tailWord_2228639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228639).length < 2 ^ (prefixWord ++ tailWord_2228639).sum := by decide
  have hdescent : baseEnd_2228639 < baseStart_2228639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228765 : List Nat := [1, 4, 2, 2, 1, 3, 2, 3, 4]
def baseStart_2228765 : Nat := 118140960795 + 2228765 * 2 ^ 59
def prefixEnd_2228765 : Nat := 4983230072969 + 3 ^ 40 * 2228765 * 2
def baseEnd_2228765 : Nat := 254317269092906151197245

theorem tailTrace_2228765 : CollatzResearch.WordTrace tailWord_2228765 prefixEnd_2228765 254317269092906151197245 := by
  unfold tailWord_2228765
  simp only [CollatzResearch.WordTrace]
  refine ⟨81289737770572522602591749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54193158513715015068394499 81289737770572522602591749)
  ·
    refine ⟨15241825831982347987985953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81289737770572522602591749 15241825831982347987985953)
    ·
      refine ⟨11431369373986760990989465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15241825831982347987985953 11431369373986760990989465)
      ·
        refine ⟨8573527030490070743242099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11431369373986760990989465 8573527030490070743242099)
        ·
          refine ⟨12860290545735106114863149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573527030490070743242099 12860290545735106114863149)
          ·
            refine ⟨4822608954650664793073681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12860290545735106114863149 4822608954650664793073681)
            ·
              refine ⟨3616956715987998594805261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4822608954650664793073681 3616956715987998594805261)
              ·
                refine ⟨1356358768495499473051973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3616956715987998594805261 1356358768495499473051973)
                ·
                  refine ⟨254317269092906151197245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356358768495499473051973 254317269092906151197245)
                  ·
                    rfl

theorem cell22_2228765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_2228765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228765 prefixEnd_2228765 := by exact prefixLift 2228765
  have htrace : WordTrace (prefixWord ++ tailWord_2228765) baseStart_2228765 baseEnd_2228765 := by
    simpa [prefixWord, tailWord_2228765, baseEnd_2228765] using wordTrace_append hprefix tailTrace_2228765
  have hstable : (prefixWord ++ tailWord_2228765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228765).length < 2 ^ (prefixWord ++ tailWord_2228765).sum := by decide
  have hdescent : baseEnd_2228765 < baseStart_2228765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228797 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_2228797 : Nat := 118140960795 + 2228797 * 2 ^ 59
def prefixEnd_2228797 : Nat := 4983230072969 + 3 ^ 40 * 2228797 * 2
def baseEnd_2228797 : Nat := 762962761532681036791637

theorem tailTrace_2228797 : CollatzResearch.WordTrace tailWord_2228797 prefixEnd_2228797 762962761532681036791637 := by
  unfold tailWord_2228797
  simp only [CollatzResearch.WordTrace]
  refine ⟨81290904906456592067756645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54193936604304394711837763 81290904906456592067756645)
  ·
    refine ⟨15242044669960611012704371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81290904906456592067756645 15242044669960611012704371)
    ·
      refine ⟨22863067004940916519056557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15242044669960611012704371 22863067004940916519056557)
      ·
        refine ⟨8573650126852843694646209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22863067004940916519056557 8573650126852843694646209)
        ·
          refine ⟨6430237595139632770984657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8573650126852843694646209 6430237595139632770984657)
          ·
            refine ⟨4822678196354724578238493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6430237595139632770984657 4822678196354724578238493)
            ·
              refine ⟨1808504323633021716839435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4822678196354724578238493 1808504323633021716839435)
              ·
                refine ⟨2712756485449532575259153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808504323633021716839435 2712756485449532575259153)
                ·
                  refine ⟨2034567364087149431444365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2712756485449532575259153 2034567364087149431444365)
                  ·
                    refine ⟨762962761532681036791637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034567364087149431444365 762962761532681036791637)
                    ·
                      rfl

theorem cell22_2228797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_2228797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228797 prefixEnd_2228797 := by exact prefixLift 2228797
  have htrace : WordTrace (prefixWord ++ tailWord_2228797) baseStart_2228797 baseEnd_2228797 := by
    simpa [prefixWord, tailWord_2228797, baseEnd_2228797] using wordTrace_append hprefix tailTrace_2228797
  have hstable : (prefixWord ++ tailWord_2228797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228797).length < 2 ^ (prefixWord ++ tailWord_2228797).sum := by decide
  have hdescent : baseEnd_2228797 < baseStart_2228797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228821 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 7]
def baseStart_2228821 : Nat := 118140960795 + 2228821 * 2 ^ 59
def prefixEnd_2228821 : Nat := 4983230072969 + 3 ^ 40 * 2228821 * 2
def baseEnd_2228821 : Nat := 254323659074384324730521

theorem tailTrace_2228821 : CollatzResearch.WordTrace tailWord_2228821 prefixEnd_2228821 254323659074384324730521 := by
  unfold tailWord_2228821
  simp only [CollatzResearch.WordTrace]
  refine ⟨81291780258369644166630317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54194520172246429444420211 81291780258369644166630317)
  ·
    refine ⟨30484417596888616562486369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81291780258369644166630317 30484417596888616562486369)
    ·
      refine ⟨22863313197666462421864777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30484417596888616562486369 22863313197666462421864777)
      ·
        refine ⟨17147484898249846816398583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22863313197666462421864777 17147484898249846816398583)
        ·
          refine ⟨25721227347374770224597875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17147484898249846816398583 25721227347374770224597875)
          ·
            refine ⟨38581841021062155336896813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25721227347374770224597875 38581841021062155336896813)
            ·
              refine ⟨14468190382898308251336305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38581841021062155336896813 14468190382898308251336305)
              ·
                refine ⟨10851142787173731188502229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14468190382898308251336305 10851142787173731188502229)
                ·
                  refine ⟨254323659074384324730521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10851142787173731188502229 254323659074384324730521)
                  ·
                    rfl

theorem cell22_2228821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_2228821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228821 prefixEnd_2228821 := by exact prefixLift 2228821
  have htrace : WordTrace (prefixWord ++ tailWord_2228821) baseStart_2228821 baseEnd_2228821 := by
    simpa [prefixWord, tailWord_2228821, baseEnd_2228821] using wordTrace_append hprefix tailTrace_2228821
  have hstable : (prefixWord ++ tailWord_2228821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228821).length < 2 ^ (prefixWord ++ tailWord_2228821).sum := by decide
  have hdescent : baseEnd_2228821 < baseStart_2228821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228900 : List Nat := [2, 3, 1, 2, 2, 1, 3, 4, 4]
def baseStart_2228900 : Nat := 118140960795 + 2228900 * 2 ^ 59
def prefixEnd_2228900 : Nat := 4983230072969 + 3 ^ 40 * 2228900 * 2
def baseEnd_2228900 : Nat := 254332673512541033822107

theorem tailTrace_2228900 : CollatzResearch.WordTrace tailWord_2228900 prefixEnd_2228900 254332673512541033822107 := by
  unfold tailWord_2228900
  simp only [CollatzResearch.WordTrace]
  refine ⟨40647330812541720329378077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54196441083388960439170769 40647330812541720329378077)
  ·
    refine ⟨15242749054703145123516779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40647330812541720329378077 15242749054703145123516779)
    ·
      refine ⟨22864123582054717685275169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15242749054703145123516779 22864123582054717685275169)
      ·
        refine ⟨17148092686541038263956377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22864123582054717685275169 17148092686541038263956377)
        ·
          refine ⟨12861069514905778697967283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17148092686541038263956377 12861069514905778697967283)
          ·
            refine ⟨19291604272358668046950925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12861069514905778697967283 19291604272358668046950925)
            ·
              refine ⟨7234351602134500517606597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19291604272358668046950925 7234351602134500517606597)
              ·
                refine ⟨1356440925400218847051237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7234351602134500517606597 1356440925400218847051237)
                ·
                  refine ⟨254332673512541033822107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356440925400218847051237 254332673512541033822107)
                  ·
                    rfl

theorem cell22_2228900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_2228900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228900 prefixEnd_2228900 := by exact prefixLift 2228900
  have htrace : WordTrace (prefixWord ++ tailWord_2228900) baseStart_2228900 baseEnd_2228900 := by
    simpa [prefixWord, tailWord_2228900, baseEnd_2228900] using wordTrace_append hprefix tailTrace_2228900
  have hstable : (prefixWord ++ tailWord_2228900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228900).length < 2 ^ (prefixWord ++ tailWord_2228900).sum := by decide
  have hdescent : baseEnd_2228900 < baseStart_2228900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228915 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 2, 3]
def baseStart_2228915 : Nat := 118140960795 + 2228915 * 2 ^ 59
def prefixEnd_2228915 : Nat := 4983230072969 + 3 ^ 40 * 2228915 * 2
def baseEnd_2228915 : Nat := 763003155344168062341275

theorem tailTrace_2228915 : CollatzResearch.WordTrace tailWord_2228915 prefixEnd_2228915 763003155344168062341275 := by
  unfold tailWord_2228915
  simp only [CollatzResearch.WordTrace]
  refine ⟨81295208720029098220552199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54196805813352732147034799 81295208720029098220552199)
  ·
    refine ⟨121942813080043647330828299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81295208720029098220552199 121942813080043647330828299)
    ·
      refine ⟨182914219620065470996242449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121942813080043647330828299 182914219620065470996242449)
      ·
        refine ⟨137185664715049103247181837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182914219620065470996242449 137185664715049103247181837)
        ·
          refine ⟨51444624268143413717693189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137185664715049103247181837 51444624268143413717693189)
          ·
            refine ⟨9645867050276890072067473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51444624268143413717693189 9645867050276890072067473)
            ·
              refine ⟨7234400287707667554050605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9645867050276890072067473 7234400287707667554050605)
              ·
                refine ⟨2712900107890375332768977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7234400287707667554050605 2712900107890375332768977)
                ·
                  refine ⟨2034675080917781499576733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2712900107890375332768977 2034675080917781499576733)
                  ·
                    refine ⟨763003155344168062341275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034675080917781499576733 763003155344168062341275)
                    ·
                      rfl

theorem cell22_2228915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 3].length) (baseStart_2228915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228915 prefixEnd_2228915 := by exact prefixLift 2228915
  have htrace : WordTrace (prefixWord ++ tailWord_2228915) baseStart_2228915 baseEnd_2228915 := by
    simpa [prefixWord, tailWord_2228915, baseEnd_2228915] using wordTrace_append hprefix tailTrace_2228915
  have hstable : (prefixWord ++ tailWord_2228915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228915).length < 2 ^ (prefixWord ++ tailWord_2228915).sum := by decide
  have hdescent : baseEnd_2228915 < baseStart_2228915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2228990 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2228990 : Nat := 118140960795 + 2228990 * 2 ^ 59
def prefixEnd_2228990 : Nat := 4983230072969 + 3 ^ 40 * 2228990 * 2
def baseEnd_2228990 : Nat := 254342943125630955572015

theorem tailTrace_2228990 : CollatzResearch.WordTrace tailWord_2228990 prefixEnd_2228990 254342943125630955572015 := by
  unfold tailWord_2228990
  simp only [CollatzResearch.WordTrace]
  refine ⟨10162243024344673253691553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54198629463171590686354949 10162243024344673253691553)
  ·
    refine ⟨7621682268258504940268665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10162243024344673253691553 7621682268258504940268665)
    ·
      refine ⟨5716261701193878705201499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7621682268258504940268665 5716261701193878705201499)
      ·
        refine ⟨8574392551790818057802249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716261701193878705201499 8574392551790818057802249)
        ·
          refine ⟨6430794413843113543351687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8574392551790818057802249 6430794413843113543351687)
          ·
            refine ⟨9646191620764670315027531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6430794413843113543351687 9646191620764670315027531)
            ·
              refine ⟨14469287431147005472541297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9646191620764670315027531 14469287431147005472541297)
              ·
                refine ⟨10851965573360254104405973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14469287431147005472541297 10851965573360254104405973)
                ·
                  refine ⟨254342943125630955572015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10851965573360254104405973 254342943125630955572015)
                  ·
                    rfl

theorem cell22_2228990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2228990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2228990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2228990 prefixEnd_2228990 := by exact prefixLift 2228990
  have htrace : WordTrace (prefixWord ++ tailWord_2228990) baseStart_2228990 baseEnd_2228990 := by
    simpa [prefixWord, tailWord_2228990, baseEnd_2228990] using wordTrace_append hprefix tailTrace_2228990
  have hstable : (prefixWord ++ tailWord_2228990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2228990).length < 2 ^ (prefixWord ++ tailWord_2228990).sum := by decide
  have hdescent : baseEnd_2228990 < baseStart_2228990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2228990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229003 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 5, 4]
def baseStart_2229003 : Nat := 118140960795 + 2229003 * 2 ^ 59
def prefixEnd_2229003 : Nat := 4983230072969 + 3 ^ 40 * 2229003 * 2
def baseEnd_2229003 : Nat := 763033279542565166141005

theorem tailTrace_2229003 : CollatzResearch.WordTrace tailWord_2229003 prefixEnd_2229003 763033279542565166141005 := by
  unfold tailWord_2229003
  simp only [CollatzResearch.WordTrace]
  refine ⟨81298418343710289249755663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54198945562473526166503775 81298418343710289249755663)
  ·
    refine ⟨121947627515565433874633495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81298418343710289249755663 121947627515565433874633495)
    ·
      refine ⟨182921441273348150811950243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121947627515565433874633495 182921441273348150811950243)
      ·
        refine ⟨274382161910022226217925365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182921441273348150811950243 274382161910022226217925365)
        ·
          refine ⟨25723327679064583707930503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 274382161910022226217925365 25723327679064583707930503)
          ·
            refine ⟨38584991518596875561895755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25723327679064583707930503 38584991518596875561895755)
            ·
              refine ⟨57877487277895313342843633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38584991518596875561895755 57877487277895313342843633)
              ·
                refine ⟨43408115458421485007132725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57877487277895313342843633 43408115458421485007132725)
                ·
                  refine ⟨4069510824227014219418693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43408115458421485007132725 4069510824227014219418693)
                  ·
                    refine ⟨763033279542565166141005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4069510824227014219418693 763033279542565166141005)
                    ·
                      rfl

theorem cell22_2229003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_2229003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229003 prefixEnd_2229003 := by exact prefixLift 2229003
  have htrace : WordTrace (prefixWord ++ tailWord_2229003) baseStart_2229003 baseEnd_2229003 := by
    simpa [prefixWord, tailWord_2229003, baseEnd_2229003] using wordTrace_append hprefix tailTrace_2229003
  have hstable : (prefixWord ++ tailWord_2229003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229003).length < 2 ^ (prefixWord ++ tailWord_2229003).sum := by decide
  have hdescent : baseEnd_2229003 < baseStart_2229003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229062 : List Nat := [6, 1, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2229062 : Nat := 118140960795 + 2229062 * 2 ^ 59
def prefixEnd_2229062 : Nat := 4983230072969 + 3 ^ 40 * 2229062 * 2
def baseEnd_2229062 : Nat := 763053476448308678915825

theorem tailTrace_2229062 : CollatzResearch.WordTrace tailWord_2229062 prefixEnd_2229062 763053476448308678915825 := by
  unfold tailWord_2229062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540642820328016947692295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54200380166997694884102293 2540642820328016947692295)
  ·
    refine ⟨3810964230492025421538443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2540642820328016947692295 3810964230492025421538443)
    ·
      refine ⟨5716446345738038132307665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810964230492025421538443 5716446345738038132307665)
      ·
        refine ⟨4287334759303528599230749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5716446345738038132307665 4287334759303528599230749)
        ·
          refine ⟨1607750534738823224711531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4287334759303528599230749 1607750534738823224711531)
          ·
            refine ⟨2411625802108234837067297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607750534738823224711531 2411625802108234837067297)
            ·
              refine ⟨1808719351581176127800473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411625802108234837067297 1808719351581176127800473)
              ·
                refine ⟨1356539513685882095850355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808719351581176127800473 1356539513685882095850355)
                ·
                  refine ⟨2034809270528823143775533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356539513685882095850355 2034809270528823143775533)
                  ·
                    refine ⟨763053476448308678915825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034809270528823143775533 763053476448308678915825)
                    ·
                      rfl

theorem cell22_2229062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2229062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229062 prefixEnd_2229062 := by exact prefixLift 2229062
  have htrace : WordTrace (prefixWord ++ tailWord_2229062) baseStart_2229062 baseEnd_2229062 := by
    simpa [prefixWord, tailWord_2229062, baseEnd_2229062] using wordTrace_append hprefix tailTrace_2229062
  have hstable : (prefixWord ++ tailWord_2229062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229062).length < 2 ^ (prefixWord ++ tailWord_2229062).sum := by decide
  have hdescent : baseEnd_2229062 < baseStart_2229062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229065 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_2229065 : Nat := 118140960795 + 2229065 * 2 ^ 59
def prefixEnd_2229065 : Nat := 4983230072969 + 3 ^ 40 * 2229065 * 2
def baseEnd_2229065 : Nat := 763054503409617671090815

theorem tailTrace_2229065 : CollatzResearch.WordTrace tailWord_2229065 prefixEnd_2229065 763054503409617671090815 := by
  unfold tailWord_2229065
  simp only [CollatzResearch.WordTrace]
  refine ⟨81300679669485673838512649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54200453112990449225675099 81300679669485673838512649)
  ·
    refine ⟨60975509752114255378884487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81300679669485673838512649 60975509752114255378884487)
    ·
      refine ⟨91463264628171383068326731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60975509752114255378884487 91463264628171383068326731)
      ·
        refine ⟨137194896942257074602490097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91463264628171383068326731 137194896942257074602490097)
        ·
          refine ⟨102896172706692805951867573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137194896942257074602490097 102896172706692805951867573)
          ·
            refine ⟨9646516191252450557987585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102896172706692805951867573 9646516191252450557987585)
            ·
              refine ⟨7234887143439337918490689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9646516191252450557987585 7234887143439337918490689)
              ·
                refine ⟨5426165357579503438868017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7234887143439337918490689 5426165357579503438868017)
                ·
                  refine ⟨4069624018184627579151013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5426165357579503438868017 4069624018184627579151013)
                  ·
                    refine ⟨763054503409617671090815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4069624018184627579151013 763054503409617671090815)
                    ·
                      rfl

theorem cell22_2229065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_2229065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229065 prefixEnd_2229065 := by exact prefixLift 2229065
  have htrace : WordTrace (prefixWord ++ tailWord_2229065) baseStart_2229065 baseEnd_2229065 := by
    simpa [prefixWord, tailWord_2229065, baseEnd_2229065] using wordTrace_append hprefix tailTrace_2229065
  have hstable : (prefixWord ++ tailWord_2229065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229065).length < 2 ^ (prefixWord ++ tailWord_2229065).sum := by decide
  have hdescent : baseEnd_2229065 < baseStart_2229065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229084 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2229084 : Nat := 118140960795 + 2229084 * 2 ^ 59
def prefixEnd_2229084 : Nat := 4983230072969 + 3 ^ 40 * 2229084 * 2
def baseEnd_2229084 : Nat := 763061007497907954865757

theorem tailTrace_2229084 : CollatzResearch.WordTrace tailWord_2229084 prefixEnd_2229084 763061007497907954865757 := by
  unfold tailWord_2229084
  simp only [CollatzResearch.WordTrace]
  refine ⟨40650686328208420041727153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54200915104277893388969537 40650686328208420041727153)
  ·
    refine ⟨30488014746156315031295365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40650686328208420041727153 30488014746156315031295365)
    ·
      refine ⟨5716502764904309068367881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30488014746156315031295365 5716502764904309068367881)
      ·
        refine ⟨4287377073678231801275911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5716502764904309068367881 4287377073678231801275911)
        ·
          refine ⟨6431065610517347701913867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4287377073678231801275911 6431065610517347701913867)
          ·
            refine ⟨9646598415776021552870801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6431065610517347701913867 9646598415776021552870801)
            ·
              refine ⟨7234948811832016164653101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9646598415776021552870801 7234948811832016164653101)
              ·
                refine ⟨2713105804437006061744913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7234948811832016164653101 2713105804437006061744913)
                ·
                  refine ⟨2034829353327754546308685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2713105804437006061744913 2034829353327754546308685)
                  ·
                    refine ⟨763061007497907954865757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034829353327754546308685 763061007497907954865757)
                    ·
                      rfl

theorem cell22_2229084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2229084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229084 prefixEnd_2229084 := by exact prefixLift 2229084
  have htrace : WordTrace (prefixWord ++ tailWord_2229084) baseStart_2229084 baseEnd_2229084 := by
    simpa [prefixWord, tailWord_2229084, baseEnd_2229084] using wordTrace_append hprefix tailTrace_2229084
  have hstable : (prefixWord ++ tailWord_2229084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229084).length < 2 ^ (prefixWord ++ tailWord_2229084).sum := by decide
  have hdescent : baseEnd_2229084 < baseStart_2229084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229118 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2229118 : Nat := 118140960795 + 2229118 * 2 ^ 59
def prefixEnd_2229118 : Nat := 4983230072969 + 3 ^ 40 * 2229118 * 2
def baseEnd_2229118 : Nat := 763072646392743199515653

theorem tailTrace_2229118 : CollatzResearch.WordTrace tailWord_2229118 prefixEnd_2229118 763072646392743199515653 := by
  unfold tailWord_2229118
  simp only [CollatzResearch.WordTrace]
  refine ⟨10162826592286707986274001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54201741825529109260128005 10162826592286707986274001)
  ·
    refine ⟨7622119944215030989705501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10162826592286707986274001 7622119944215030989705501)
    ·
      refine ⟨2858294979080636621139563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7622119944215030989705501 2858294979080636621139563)
      ·
        refine ⟨4287442468620954931709345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2858294979080636621139563 4287442468620954931709345)
        ·
          refine ⟨3215581851465716198782009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4287442468620954931709345 3215581851465716198782009)
          ·
            refine ⟨2411686388599287149086507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215581851465716198782009 2411686388599287149086507)
            ·
              refine ⟨3617529582898930723629761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411686388599287149086507 3617529582898930723629761)
              ·
                refine ⟨2713147187174198042722321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617529582898930723629761 2713147187174198042722321)
                ·
                  refine ⟨2034860390380648532041741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2713147187174198042722321 2034860390380648532041741)
                  ·
                    refine ⟨763072646392743199515653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034860390380648532041741 763072646392743199515653)
                    ·
                      rfl

theorem cell22_2229118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2229118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229118 prefixEnd_2229118 := by exact prefixLift 2229118
  have htrace : WordTrace (prefixWord ++ tailWord_2229118) baseStart_2229118 baseEnd_2229118 := by
    simpa [prefixWord, tailWord_2229118, baseEnd_2229118] using wordTrace_append hprefix tailTrace_2229118
  have hstable : (prefixWord ++ tailWord_2229118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229118).length < 2 ^ (prefixWord ++ tailWord_2229118).sum := by decide
  have hdescent : baseEnd_2229118 < baseStart_2229118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229125 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 7]
def baseStart_2229125 : Nat := 118140960795 + 2229125 * 2 ^ 59
def prefixEnd_2229125 : Nat := 4983230072969 + 3 ^ 40 * 2229125 * 2
def baseEnd_2229125 : Nat := 254358347545265838196877

theorem tailTrace_2229125 : CollatzResearch.WordTrace tailWord_2229125 prefixEnd_2229125 254358347545265838196877 := by
  unfold tailWord_2229125
  simp only [CollatzResearch.WordTrace]
  refine ⟨81302868049268304085696829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54201912032845536057131219 81302868049268304085696829)
  ·
    refine ⟨30488575518475614032136311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81302868049268304085696829 30488575518475614032136311)
    ·
      refine ⟨45732863277713421048204467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30488575518475614032136311 45732863277713421048204467)
      ·
        refine ⟨68599294916570131572306701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45732863277713421048204467 68599294916570131572306701)
        ·
          refine ⟨25724735593713799339615013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68599294916570131572306701 25724735593713799339615013)
          ·
            refine ⟨4823387923821337376177815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25724735593713799339615013 4823387923821337376177815)
            ·
              refine ⟨7235081885732006064266723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4823387923821337376177815 7235081885732006064266723)
              ·
                refine ⟨10852622828598009096400085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7235081885732006064266723 10852622828598009096400085)
                ·
                  refine ⟨254358347545265838196877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10852622828598009096400085 254358347545265838196877)
                  ·
                    rfl

theorem cell22_2229125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_2229125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229125 prefixEnd_2229125 := by exact prefixLift 2229125
  have htrace : WordTrace (prefixWord ++ tailWord_2229125) baseStart_2229125 baseEnd_2229125 := by
    simpa [prefixWord, tailWord_2229125, baseEnd_2229125] using wordTrace_append hprefix tailTrace_2229125
  have hstable : (prefixWord ++ tailWord_2229125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229125).length < 2 ^ (prefixWord ++ tailWord_2229125).sum := by decide
  have hdescent : baseEnd_2229125 < baseStart_2229125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229129 : List Nat := [1, 2, 1, 1, 5, 2, 2, 4, 1, 3]
def baseStart_2229129 : Nat := 118140960795 + 2229129 * 2 ^ 59
def prefixEnd_2229129 : Nat := 4983230072969 + 3 ^ 40 * 2229129 * 2
def baseEnd_2229129 : Nat := 763076411917542837490619

theorem tailTrace_2229129 : CollatzResearch.WordTrace tailWord_2229129 prefixEnd_2229129 763076411917542837490619 := by
  unfold tailWord_2229129
  simp only [CollatzResearch.WordTrace]
  refine ⟨81303013941253812768842441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54202009294169208512561627 81303013941253812768842441)
  ·
    refine ⟨60977260455940359576631831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81303013941253812768842441 60977260455940359576631831)
    ·
      refine ⟨91465890683910539364947747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60977260455940359576631831 91465890683910539364947747)
      ·
        refine ⟨137198836025865809047421621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91465890683910539364947747 137198836025865809047421621)
        ·
          refine ⟨12862390877424919598195777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137198836025865809047421621 12862390877424919598195777)
          ·
            refine ⟨9646793158068689698646833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12862390877424919598195777 9646793158068689698646833)
            ·
              refine ⟨7235094868551517273985125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9646793158068689698646833 7235094868551517273985125)
              ·
                refine ⟨1356580287853409488872211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7235094868551517273985125 1356580287853409488872211)
                ·
                  refine ⟨2034870431780114233308317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356580287853409488872211 2034870431780114233308317)
                  ·
                    refine ⟨763076411917542837490619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2034870431780114233308317 763076411917542837490619)
                    ·
                      rfl

theorem cell22_2229129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 3].length) (baseStart_2229129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229129 prefixEnd_2229129 := by exact prefixLift 2229129
  have htrace : WordTrace (prefixWord ++ tailWord_2229129) baseStart_2229129 baseEnd_2229129 := by
    simpa [prefixWord, tailWord_2229129, baseEnd_2229129] using wordTrace_append hprefix tailTrace_2229129
  have hstable : (prefixWord ++ tailWord_2229129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229129).length < 2 ^ (prefixWord ++ tailWord_2229129).sum := by decide
  have hdescent : baseEnd_2229129 < baseStart_2229129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229155 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 3, 4]
def baseStart_2229155 : Nat := 118140960795 + 2229155 * 2 ^ 59
def prefixEnd_2229155 : Nat := 4983230072969 + 3 ^ 40 * 2229155 * 2
def baseEnd_2229155 : Nat := 763085312248887436340539

theorem tailTrace_2229155 : CollatzResearch.WordTrace tailWord_2229155 prefixEnd_2229155 763085312248887436340539 := by
  unfold tailWord_2229155
  simp only [CollatzResearch.WordTrace]
  refine ⟨81303962239159619209288919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54202641492773079472859279 81303962239159619209288919)
  ·
    refine ⟨121955943358739428813933379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81303962239159619209288919 121955943358739428813933379)
    ·
      refine ⟨182933915038109143220900069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121955943358739428813933379 182933915038109143220900069)
      ·
        refine ⟨34300109069645464353918763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182933915038109143220900069 34300109069645464353918763)
        ·
          refine ⟨51450163604468196530878145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34300109069645464353918763 51450163604468196530878145)
          ·
            refine ⟨38587622703351147398158609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51450163604468196530878145 38587622703351147398158609)
            ·
              refine ⟨28940717027513360548618957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38587622703351147398158609 28940717027513360548618957)
              ·
                refine ⟨10852768885317510205732109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28940717027513360548618957 10852768885317510205732109)
                ·
                  refine ⟨4069788331994066327149541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10852768885317510205732109 4069788331994066327149541)
                  ·
                    refine ⟨763085312248887436340539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4069788331994066327149541 763085312248887436340539)
                    ·
                      rfl

theorem cell22_2229155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_2229155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229155 prefixEnd_2229155 := by exact prefixLift 2229155
  have htrace : WordTrace (prefixWord ++ tailWord_2229155) baseStart_2229155 baseEnd_2229155 := by
    simpa [prefixWord, tailWord_2229155, baseEnd_2229155] using wordTrace_append hprefix tailTrace_2229155
  have hstable : (prefixWord ++ tailWord_2229155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229155).length < 2 ^ (prefixWord ++ tailWord_2229155).sum := by decide
  have hdescent : baseEnd_2229155 < baseStart_2229155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229200 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_2229200 : Nat := 118140960795 + 2229200 * 2 ^ 59
def prefixEnd_2229200 : Nat := 4983230072969 + 3 ^ 40 * 2229200 * 2
def baseEnd_2229200 : Nat := 763100716668522318965401

theorem tailTrace_2229200 : CollatzResearch.WordTrace tailWord_2229200 prefixEnd_2229200 763100716668522318965401 := by
  unfold tailWord_2229200
  simp only [CollatzResearch.WordTrace]
  refine ⟨40652801761998295947338527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54203735682664394596451369 40652801761998295947338527)
  ·
    refine ⟨60979202642997443921007791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40652801761998295947338527 60979202642997443921007791)
    ·
      refine ⟨91468803964496165881511687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60979202642997443921007791 91468803964496165881511687)
      ·
        refine ⟨137203205946744248822267531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91468803964496165881511687 137203205946744248822267531)
        ·
          refine ⟨205804808920116373233401297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137203205946744248822267531 205804808920116373233401297)
          ·
            refine ⟨154353606690087279925050973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205804808920116373233401297 154353606690087279925050973)
            ·
              refine ⟨57882602508782729971894115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154353606690087279925050973 57882602508782729971894115)
              ·
                refine ⟨86823903763174094957841173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57882602508782729971894115 86823903763174094957841173)
                ·
                  refine ⟨4069870488898785701148805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86823903763174094957841173 4069870488898785701148805)
                  ·
                    refine ⟨763100716668522318965401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4069870488898785701148805 763100716668522318965401)
                    ·
                      rfl

theorem cell22_2229200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_2229200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229200 prefixEnd_2229200 := by exact prefixLift 2229200
  have htrace : WordTrace (prefixWord ++ tailWord_2229200) baseStart_2229200 baseEnd_2229200 := by
    simpa [prefixWord, tailWord_2229200, baseEnd_2229200] using wordTrace_append hprefix tailTrace_2229200
  have hstable : (prefixWord ++ tailWord_2229200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229200).length < 2 ^ (prefixWord ++ tailWord_2229200).sum := by decide
  have hdescent : baseEnd_2229200 < baseStart_2229200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229206 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2229206 : Nat := 118140960795 + 2229206 * 2 ^ 59
def prefixEnd_2229206 : Nat := 4983230072969 + 3 ^ 40 * 2229206 * 2
def baseEnd_2229206 : Nat := 763102770591140303315383

theorem tailTrace_2229206 : CollatzResearch.WordTrace tailWord_2229206 prefixEnd_2229206 763102770591140303315383 := by
  unfold tailWord_2229206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081613897623428432462217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54203881574649903279596981 5081613897623428432462217)
  ·
    refine ⟨3811210423217571324346663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5081613897623428432462217 3811210423217571324346663)
    ·
      refine ⟨5716815634826356986519995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811210423217571324346663 5716815634826356986519995)
      ·
        refine ⟨8575223452239535479779993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716815634826356986519995 8575223452239535479779993)
        ·
          refine ⟨6431417589179651609834995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8575223452239535479779993 6431417589179651609834995)
          ·
            refine ⟨9647126383769477414752493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6431417589179651609834995 9647126383769477414752493)
            ·
              refine ⟨3617672393913554030532185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9647126383769477414752493 3617672393913554030532185)
              ·
                refine ⟨2713254295435165522899139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617672393913554030532185 2713254295435165522899139)
                ·
                  refine ⟨4069881443152748284348709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713254295435165522899139 4069881443152748284348709)
                  ·
                    refine ⟨763102770591140303315383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4069881443152748284348709 763102770591140303315383)
                    ·
                      rfl

theorem cell22_2229206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2229206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229206 prefixEnd_2229206 := by exact prefixLift 2229206
  have htrace : WordTrace (prefixWord ++ tailWord_2229206) baseStart_2229206 baseEnd_2229206 := by
    simpa [prefixWord, tailWord_2229206, baseEnd_2229206] using wordTrace_append hprefix tailTrace_2229206
  have hstable : (prefixWord ++ tailWord_2229206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229206).length < 2 ^ (prefixWord ++ tailWord_2229206).sum := by decide
  have hdescent : baseEnd_2229206 < baseStart_2229206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229238 : List Nat := [5, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2229238 : Nat := 118140960795 + 2229238 * 2 ^ 59
def prefixEnd_2229238 : Nat := 4983230072969 + 3 ^ 40 * 2229238 * 2
def baseEnd_2229238 : Nat := 254371241615034295505095

theorem tailTrace_2229238 : CollatzResearch.WordTrace tailWord_2229238 prefixEnd_2229238 254371241615034295505095 := by
  unfold tailWord_2229238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081686843616182774035023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54204659665239282923040245 5081686843616182774035023)
  ·
    refine ⟨7622530265424274161052535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5081686843616182774035023 7622530265424274161052535)
    ·
      refine ⟨11433795398136411241578803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7622530265424274161052535 11433795398136411241578803)
      ·
        refine ⟨17150693097204616862368205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11433795398136411241578803 17150693097204616862368205)
        ·
          refine ⟨6431509911451731323388077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17150693097204616862368205 6431509911451731323388077)
          ·
            refine ⟨2411816216794399246270529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6431509911451731323388077 2411816216794399246270529)
            ·
              refine ⟨1808862162595799434702897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411816216794399246270529 1808862162595799434702897)
              ·
                refine ⟨1356646621946849576027173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808862162595799434702897 1356646621946849576027173)
                ·
                  refine ⟨254371241615034295505095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356646621946849576027173 254371241615034295505095)
                  ·
                    rfl

theorem cell22_2229238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2229238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229238 prefixEnd_2229238 := by exact prefixLift 2229238
  have htrace : WordTrace (prefixWord ++ tailWord_2229238) baseStart_2229238 baseEnd_2229238 := by
    simpa [prefixWord, tailWord_2229238, baseEnd_2229238] using wordTrace_append hprefix tailTrace_2229238
  have hstable : (prefixWord ++ tailWord_2229238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229238).length < 2 ^ (prefixWord ++ tailWord_2229238).sum := by decide
  have hdescent : baseEnd_2229238 < baseStart_2229238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229281 : List Nat := [1, 2, 3, 2, 3, 1, 1, 5, 1, 3]
def baseStart_2229281 : Nat := 118140960795 + 2229281 * 2 ^ 59
def prefixEnd_2229281 : Nat := 4983230072969 + 3 ^ 40 * 2229281 * 2
def baseEnd_2229281 : Nat := 763128444623865107690153

theorem tailTrace_2229281 : CollatzResearch.WordTrace tailWord_2229281 prefixEnd_2229281 763128444623865107690153 := by
  unfold tailWord_2229281
  simp only [CollatzResearch.WordTrace]
  refine ⟨81308557836703142728375697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54205705224468761818917131 81308557836703142728375697)
  ·
    refine ⟨60981418377527357046281773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81308557836703142728375697 60981418377527357046281773)
    ·
      refine ⟨22868031891572758892355665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60981418377527357046281773 22868031891572758892355665)
      ·
        refine ⟨17151023918679569169266749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22868031891572758892355665 17151023918679569169266749)
        ·
          refine ⟨6431633969504838438475031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17151023918679569169266749 6431633969504838438475031)
          ·
            refine ⟨9647450954257257657712547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6431633969504838438475031 9647450954257257657712547)
            ·
              refine ⟨14471176431385886486568821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9647450954257257657712547 14471176431385886486568821)
              ·
                refine ⟨1356672790442426858115827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14471176431385886486568821 1356672790442426858115827)
                ·
                  refine ⟨2035009185663640287173741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356672790442426858115827 2035009185663640287173741)
                  ·
                    refine ⟨763128444623865107690153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2035009185663640287173741 763128444623865107690153)
                    ·
                      rfl

theorem cell22_2229281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_2229281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229281 prefixEnd_2229281 := by exact prefixLift 2229281
  have htrace : WordTrace (prefixWord ++ tailWord_2229281) baseStart_2229281 baseEnd_2229281 := by
    simpa [prefixWord, tailWord_2229281, baseEnd_2229281] using wordTrace_append hprefix tailTrace_2229281
  have hstable : (prefixWord ++ tailWord_2229281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229281).length < 2 ^ (prefixWord ++ tailWord_2229281).sum := by decide
  have hdescent : baseEnd_2229281 < baseStart_2229281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229322 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_2229322 : Nat := 118140960795 + 2229322 * 2 ^ 59
def prefixEnd_2229322 : Nat := 4983230072969 + 3 ^ 40 * 2229322 * 2
def baseEnd_2229322 : Nat := 254380826587251555805009

theorem tailTrace_2229322 : CollatzResearch.WordTrace tailWord_2229322 prefixEnd_2229322 254380826587251555805009 := by
  unfold tailWord_2229322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20327513307388651682654555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54206702153036404487078813 20327513307388651682654555)
  ·
    refine ⟨30491269961082977523981833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20327513307388651682654555 30491269961082977523981833)
    ·
      refine ⟨22868452470812233142986375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30491269961082977523981833 22868452470812233142986375)
      ·
        refine ⟨34302678706218349714479563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22868452470812233142986375 34302678706218349714479563)
        ·
          refine ⟨51454018059327524571719345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34302678706218349714479563 51454018059327524571719345)
          ·
            refine ⟨38590513544495643428789509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51454018059327524571719345 38590513544495643428789509)
            ·
              refine ⟨7235721289592933142898033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38590513544495643428789509 7235721289592933142898033)
              ·
                refine ⟨5426790967194699857173525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7235721289592933142898033 5426790967194699857173525)
                ·
                  refine ⟨254380826587251555805009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5426790967194699857173525 254380826587251555805009)
                  ·
                    rfl

theorem cell22_2229322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_2229322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229322 prefixEnd_2229322 := by exact prefixLift 2229322
  have htrace : WordTrace (prefixWord ++ tailWord_2229322) baseStart_2229322 baseEnd_2229322 := by
    simpa [prefixWord, tailWord_2229322, baseEnd_2229322] using wordTrace_append hprefix tailTrace_2229322
  have hstable : (prefixWord ++ tailWord_2229322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229322).length < 2 ^ (prefixWord ++ tailWord_2229322).sum := by decide
  have hdescent : baseEnd_2229322 < baseStart_2229322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229356 : List Nat := [2, 2, 1, 1, 3, 2, 5, 2, 4]
def baseStart_2229356 : Nat := 118140960795 + 2229356 * 2 ^ 59
def prefixEnd_2229356 : Nat := 4983230072969 + 3 ^ 40 * 2229356 * 2
def baseEnd_2229356 : Nat := 254384706218863304021641

theorem tailTrace_2229356 : CollatzResearch.WordTrace tailWord_2229356 prefixEnd_2229356 254384706218863304021641 := by
  unfold tailWord_2229356
  simp only [CollatzResearch.WordTrace]
  refine ⟨40655646655715715268677961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54207528874287620358237281 40655646655715715268677961)
  ·
    refine ⟨30491734991786786451508471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40655646655715715268677961 30491734991786786451508471)
    ·
      refine ⟨45737602487680179677262707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30491734991786786451508471 45737602487680179677262707)
      ·
        refine ⟨68606403731520269515894061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45737602487680179677262707 68606403731520269515894061)
        ·
          refine ⟨25727401399320101068460273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68606403731520269515894061 25727401399320101068460273)
          ·
            refine ⟨19295551049490075801345205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25727401399320101068460273 19295551049490075801345205)
            ·
              refine ⟨1808957910889694606376113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19295551049490075801345205 1808957910889694606376113)
              ·
                refine ⟨1356718433167270954782085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808957910889694606376113 1356718433167270954782085)
                ·
                  refine ⟨254384706218863304021641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356718433167270954782085 254384706218863304021641)
                  ·
                    rfl

theorem cell22_2229356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_2229356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229356 prefixEnd_2229356 := by exact prefixLift 2229356
  have htrace : WordTrace (prefixWord ++ tailWord_2229356) baseStart_2229356 baseEnd_2229356 := by
    simpa [prefixWord, tailWord_2229356, baseEnd_2229356] using wordTrace_append hprefix tailTrace_2229356
  have hstable : (prefixWord ++ tailWord_2229356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229356).length < 2 ^ (prefixWord ++ tailWord_2229356).sum := by decide
  have hdescent : baseEnd_2229356 < baseStart_2229356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229367 : List Nat := [1, 1, 3, 1, 1, 4, 4, 7]
def baseStart_2229367 : Nat := 118140960795 + 2229367 * 2 ^ 59
def prefixEnd_2229367 : Nat := 4983230072969 + 3 ^ 40 * 2229367 * 2
def baseEnd_2229367 : Nat := 84795320464598838893321

theorem tailTrace_2229367 : CollatzResearch.WordTrace tailWord_2229367 prefixEnd_2229367 84795320464598838893321 := by
  unfold tailWord_2229367
  simp only [CollatzResearch.WordTrace]
  refine ⟨81311694514391579416006355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54207796342927719610670903 81311694514391579416006355)
  ·
    refine ⟨121967541771587369124009533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81311694514391579416006355 121967541771587369124009533)
    ·
      refine ⟨45737828164345263421503575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121967541771587369124009533 45737828164345263421503575)
      ·
        refine ⟨68606742246517895132255363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45737828164345263421503575 68606742246517895132255363)
        ·
          refine ⟨102910113369776842698383045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68606742246517895132255363 102910113369776842698383045)
          ·
            refine ⟨19295646256833158005946821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102910113369776842698383045 19295646256833158005946821)
            ·
              refine ⟨3617933673156217126115029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19295646256833158005946821 3617933673156217126115029)
              ·
                refine ⟨84795320464598838893321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3617933673156217126115029 84795320464598838893321)
                ·
                  rfl

theorem cell22_2229367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 7].length) (baseStart_2229367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229367 prefixEnd_2229367 := by exact prefixLift 2229367
  have htrace : WordTrace (prefixWord ++ tailWord_2229367) baseStart_2229367 baseEnd_2229367 := by
    simpa [prefixWord, tailWord_2229367, baseEnd_2229367] using wordTrace_append hprefix tailTrace_2229367
  have hstable : (prefixWord ++ tailWord_2229367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229367).length < 2 ^ (prefixWord ++ tailWord_2229367).sum := by decide
  have hdescent : baseEnd_2229367 < baseStart_2229367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229427 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 1, 7]
def baseStart_2229427 : Nat := 118140960795 + 2229427 * 2 ^ 59
def prefixEnd_2229427 : Nat := 4983230072969 + 3 ^ 40 * 2229427 * 2
def baseEnd_2229427 : Nat := 763178423407569393539705

theorem tailTrace_2229427 : CollatzResearch.WordTrace tailWord_2229427 prefixEnd_2229427 763178423407569393539705 := by
  unfold tailWord_2229427
  simp only [CollatzResearch.WordTrace]
  refine ⟨81313882894174209663190535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54209255262782806442127023 81313882894174209663190535)
  ·
    refine ⟨121970824341261314494785803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81313882894174209663190535 121970824341261314494785803)
    ·
      refine ⟨182956236511891971742178705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121970824341261314494785803 182956236511891971742178705)
      ·
        refine ⟨137217177383918978806634029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182956236511891971742178705 137217177383918978806634029)
        ·
          refine ⟨51456441518969617052487761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137217177383918978806634029 51456441518969617052487761)
          ·
            refine ⟨38592331139227212789365821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51456441518969617052487761 38592331139227212789365821)
            ·
              refine ⟨14472124177210204796012183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38592331139227212789365821 14472124177210204796012183)
              ·
                refine ⟨21708186265815307194018275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14472124177210204796012183 21708186265815307194018275)
                ·
                  refine ⟨32562279398722960791027413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21708186265815307194018275 32562279398722960791027413)
                  ·
                    refine ⟨763178423407569393539705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32562279398722960791027413 763178423407569393539705)
                    ·
                      rfl

theorem cell22_2229427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_2229427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229427 prefixEnd_2229427 := by exact prefixLift 2229427
  have htrace : WordTrace (prefixWord ++ tailWord_2229427) baseStart_2229427 baseEnd_2229427 := by
    simpa [prefixWord, tailWord_2229427, baseEnd_2229427] using wordTrace_append hprefix tailTrace_2229427
  have hstable : (prefixWord ++ tailWord_2229427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229427).length < 2 ^ (prefixWord ++ tailWord_2229427).sum := by decide
  have hdescent : baseEnd_2229427 < baseStart_2229427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229457 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 10]
def baseStart_2229457 : Nat := 118140960795 + 2229457 * 2 ^ 59
def prefixEnd_2229457 : Nat := 4983230072969 + 3 ^ 40 * 2229457 * 2
def baseEnd_2229457 : Nat := 254396231006886438429871

theorem tailTrace_2229457 : CollatzResearch.WordTrace tailWord_2229457 prefixEnd_2229457 254396231006886438429871 := by
  unfold tailWord_2229457
  simp only [CollatzResearch.WordTrace]
  refine ⟨81314977084065524786782625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54209984722710349857855083 81314977084065524786782625)
  ·
    refine ⟨60986232813049143590086969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81314977084065524786782625 60986232813049143590086969)
    ·
      refine ⟨45739674609786857692565227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60986232813049143590086969 45739674609786857692565227)
      ·
        refine ⟨68609511914680286538847841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45739674609786857692565227 68609511914680286538847841)
        ·
          refine ⟨51457133936010214904135881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68609511914680286538847841 51457133936010214904135881)
          ·
            refine ⟨38592850452007661178101911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51457133936010214904135881 38592850452007661178101911)
            ·
              refine ⟨57889275678011491767152867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38592850452007661178101911 57889275678011491767152867)
              ·
                refine ⟨86833913517017237650729301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57889275678011491767152867 86833913517017237650729301)
                ·
                  refine ⟨254396231006886438429871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 86833913517017237650729301 254396231006886438429871)
                  ·
                    rfl

theorem cell22_2229457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_2229457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229457 prefixEnd_2229457 := by exact prefixLift 2229457
  have htrace : WordTrace (prefixWord ++ tailWord_2229457) baseStart_2229457 baseEnd_2229457 := by
    simpa [prefixWord, tailWord_2229457, baseEnd_2229457] using wordTrace_append hprefix tailTrace_2229457
  have hstable : (prefixWord ++ tailWord_2229457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229457).length < 2 ^ (prefixWord ++ tailWord_2229457).sum := by decide
  have hdescent : baseEnd_2229457 < baseStart_2229457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229459 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 1, 4]
def baseStart_2229459 : Nat := 118140960795 + 2229459 * 2 ^ 59
def prefixEnd_2229459 : Nat := 4983230072969 + 3 ^ 40 * 2229459 * 2
def baseEnd_2229459 : Nat := 763189377661531976739607

theorem tailTrace_2229459 : CollatzResearch.WordTrace tailWord_2229459 prefixEnd_2229459 763189377661531976739607 := by
  unfold tailWord_2229459
  simp only [CollatzResearch.WordTrace]
  refine ⟨81315050030058279128355431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54210033353372186085570287 81315050030058279128355431)
  ·
    refine ⟨121972575045087418692533147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81315050030058279128355431 121972575045087418692533147)
    ·
      refine ⟨182958862567631128038799721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121972575045087418692533147 182958862567631128038799721)
      ·
        refine ⟨137219146925723346029099791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182958862567631128038799721 137219146925723346029099791)
        ·
          refine ⟨205828720388585019043649687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137219146925723346029099791 205828720388585019043649687)
          ·
            refine ⟨308743080582877528565474531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205828720388585019043649687 308743080582877528565474531)
            ·
              refine ⟨463114620874316292848211797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308743080582877528565474531 463114620874316292848211797)
              ·
                refine ⟨2713562231685447028407491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 463114620874316292848211797 2713562231685447028407491)
                ·
                  refine ⟨4070343347528170542611237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713562231685447028407491 4070343347528170542611237)
                  ·
                    refine ⟨763189377661531976739607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4070343347528170542611237 763189377661531976739607)
                    ·
                      rfl

theorem cell22_2229459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 4].length) (baseStart_2229459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229459 prefixEnd_2229459 := by exact prefixLift 2229459
  have htrace : WordTrace (prefixWord ++ tailWord_2229459) baseStart_2229459 baseEnd_2229459 := by
    simpa [prefixWord, tailWord_2229459, baseEnd_2229459] using wordTrace_append hprefix tailTrace_2229459
  have hstable : (prefixWord ++ tailWord_2229459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229459).length < 2 ^ (prefixWord ++ tailWord_2229459).sum := by decide
  have hdescent : baseEnd_2229459 < baseStart_2229459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229504 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_2229504 : Nat := 118140960795 + 2229504 * 2 ^ 59
def prefixEnd_2229504 : Nat := 4983230072969 + 3 ^ 40 * 2229504 * 2
def baseEnd_2229504 : Nat := 763204782081166859364469

theorem tailTrace_2229504 : CollatzResearch.WordTrace tailWord_2229504 prefixEnd_2229504 763204782081166859364469 := by
  unfold tailWord_2229504
  simp only [CollatzResearch.WordTrace]
  refine ⟨40658345657447625906871783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54211127543263501209162377 40658345657447625906871783)
  ·
    refine ⟨60987518486171438860307675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40658345657447625906871783 60987518486171438860307675)
    ·
      refine ⟨91481277729257158290461513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60987518486171438860307675 91481277729257158290461513)
      ·
        refine ⟨68610958296942868717846135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91481277729257158290461513 68610958296942868717846135)
        ·
          refine ⟨102916437445414303076769203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68610958296942868717846135 102916437445414303076769203)
          ·
            refine ⟨154374656168121454615153805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102916437445414303076769203 154374656168121454615153805)
            ·
              refine ⟨57890496063045545480682677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154374656168121454615153805 57890496063045545480682677)
              ·
                refine ⟨5427234005910519888814001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57890496063045545480682677 5427234005910519888814001)
                ·
                  refine ⟨4070425504432889916610501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5427234005910519888814001 4070425504432889916610501)
                  ·
                    refine ⟨763204782081166859364469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4070425504432889916610501 763204782081166859364469)
                    ·
                      rfl

theorem cell22_2229504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_2229504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229504 prefixEnd_2229504 := by exact prefixLift 2229504
  have htrace : WordTrace (prefixWord ++ tailWord_2229504) baseStart_2229504 baseEnd_2229504 := by
    simpa [prefixWord, tailWord_2229504, baseEnd_2229504] using wordTrace_append hprefix tailTrace_2229504
  have hstable : (prefixWord ++ tailWord_2229504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229504).length < 2 ^ (prefixWord ++ tailWord_2229504).sum := by decide
  have hdescent : baseEnd_2229504 < baseStart_2229504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229508 : List Nat := [2, 3, 2, 2, 2, 1, 3, 3, 4]
def baseStart_2229508 : Nat := 118140960795 + 2229508 * 2 ^ 59
def prefixEnd_2229508 : Nat := 4983230072969 + 3 ^ 40 * 2229508 * 2
def baseEnd_2229508 : Nat := 254402050454304060754819

theorem tailTrace_2229508 : CollatzResearch.WordTrace tailWord_2229508 prefixEnd_2229508 254402050454304060754819 := by
  unfold tailWord_2229508
  simp only [CollatzResearch.WordTrace]
  refine ⟨40658418603440380248444589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54211224804587173664592785 40658418603440380248444589)
  ·
    refine ⟨15246906976290142593166721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40658418603440380248444589 15246906976290142593166721)
    ·
      refine ⟨11435180232217606944875041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15246906976290142593166721 11435180232217606944875041)
      ·
        refine ⟨8576385174163205208656281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11435180232217606944875041 8576385174163205208656281)
        ·
          refine ⟨6432288880622403906492211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8576385174163205208656281 6432288880622403906492211)
          ·
            refine ⟨9648433320933605859738317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6432288880622403906492211 9648433320933605859738317)
            ·
              refine ⟨3618162495350102197401869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9648433320933605859738317 3618162495350102197401869)
              ·
                refine ⟨1356810935756288324025701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3618162495350102197401869 1356810935756288324025701)
                ·
                  refine ⟨254402050454304060754819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356810935756288324025701 254402050454304060754819)
                  ·
                    rfl

theorem cell22_2229508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_2229508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229508 prefixEnd_2229508 := by exact prefixLift 2229508
  have htrace : WordTrace (prefixWord ++ tailWord_2229508) baseStart_2229508 baseEnd_2229508 := by
    simpa [prefixWord, tailWord_2229508, baseEnd_2229508] using wordTrace_append hprefix tailTrace_2229508
  have hstable : (prefixWord ++ tailWord_2229508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229508).length < 2 ^ (prefixWord ++ tailWord_2229508).sum := by decide
  have hdescent : baseEnd_2229508 < baseStart_2229508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229536 : List Nat := [2, 1, 1, 5, 3, 1, 2, 7]
def baseStart_2229536 : Nat := 118140960795 + 2229536 * 2 ^ 59
def prefixEnd_2229536 : Nat := 4983230072969 + 3 ^ 40 * 2229536 * 2
def baseEnd_2229536 : Nat := 84801748481681049173819

theorem tailTrace_2229536 : CollatzResearch.WordTrace tailWord_2229536 prefixEnd_2229536 84801748481681049173819 := by
  unfold tailWord_2229536
  simp only [CollatzResearch.WordTrace]
  refine ⟨40658929225389660639454231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54211905633852880852605641 40658929225389660639454231)
  ·
    refine ⟨60988393838084490959181347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40658929225389660639454231 60988393838084490959181347)
    ·
      refine ⟨91482590757126736438772021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60988393838084490959181347 91482590757126736438772021)
      ·
        refine ⟨8576492883480631541134877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91482590757126736438772021 8576492883480631541134877)
        ·
          refine ⟨3216184831305236827925579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8576492883480631541134877 3216184831305236827925579)
          ·
            refine ⟨4824277246957855241888369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216184831305236827925579 4824277246957855241888369)
            ·
              refine ⟨3618207935218391431416277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4824277246957855241888369 3618207935218391431416277)
              ·
                refine ⟨84801748481681049173819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3618207935218391431416277 84801748481681049173819)
                ·
                  rfl

theorem cell22_2229536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_2229536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229536 prefixEnd_2229536 := by exact prefixLift 2229536
  have htrace : WordTrace (prefixWord ++ tailWord_2229536) baseStart_2229536 baseEnd_2229536 := by
    simpa [prefixWord, tailWord_2229536, baseEnd_2229536] using wordTrace_append hprefix tailTrace_2229536
  have hstable : (prefixWord ++ tailWord_2229536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229536).length < 2 ^ (prefixWord ++ tailWord_2229536).sum := by decide
  have hdescent : baseEnd_2229536 < baseStart_2229536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229568 : List Nat := [2, 1, 1, 2, 2, 1, 4, 5, 1, 3]
def baseStart_2229568 : Nat := 118140960795 + 2229568 * 2 ^ 59
def prefixEnd_2229568 : Nat := 4983230072969 + 3 ^ 40 * 2229568 * 2
def baseEnd_2229568 : Nat := 763226690589092025764273

theorem tailTrace_2229568 : CollatzResearch.WordTrace tailWord_2229568 prefixEnd_2229568 763226690589092025764273 := by
  unfold tailWord_2229568
  simp only [CollatzResearch.WordTrace]
  refine ⟨40659512793331695372036679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54212683724442260496048905 40659512793331695372036679)
  ·
    refine ⟨60989269189997543058055019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40659512793331695372036679 60989269189997543058055019)
    ·
      refine ⟨91483903784996314587082529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60989269189997543058055019 91483903784996314587082529)
      ·
        refine ⟨68612927838747235940311897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91483903784996314587082529 68612927838747235940311897)
        ·
          refine ⟨51459695879060426955233923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68612927838747235940311897 51459695879060426955233923)
          ·
            refine ⟨77189543818590640432850885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51459695879060426955233923 77189543818590640432850885)
            ·
              refine ⟨14473039465985745081159541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77189543818590640432850885 14473039465985745081159541)
              ·
                refine ⟨1356847449936163601358707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14473039465985745081159541 1356847449936163601358707)
                ·
                  refine ⟨2035271174904245402038061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356847449936163601358707 2035271174904245402038061)
                  ·
                    refine ⟨763226690589092025764273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2035271174904245402038061 763226690589092025764273)
                    ·
                      rfl

theorem cell22_2229568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 3].length) (baseStart_2229568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229568 prefixEnd_2229568 := by exact prefixLift 2229568
  have htrace : WordTrace (prefixWord ++ tailWord_2229568) baseStart_2229568 baseEnd_2229568 := by
    simpa [prefixWord, tailWord_2229568, baseEnd_2229568] using wordTrace_append hprefix tailTrace_2229568
  have hstable : (prefixWord ++ tailWord_2229568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229568).length < 2 ^ (prefixWord ++ tailWord_2229568).sum := by decide
  have hdescent : baseEnd_2229568 < baseStart_2229568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229574 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2229574 : Nat := 118140960795 + 2229574 * 2 ^ 59
def prefixEnd_2229574 : Nat := 4983230072969 + 3 ^ 40 * 2229574 * 2
def baseEnd_2229574 : Nat := 763228744511710010114255

theorem tailTrace_2229574 : CollatzResearch.WordTrace tailWord_2229574 prefixEnd_2229574 763228744511710010114255 := by
  unfold tailWord_2229574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541226388270051680274743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54212829616427769179194517 2541226388270051680274743)
  ·
    refine ⟨3811839582405077520412115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2541226388270051680274743 3811839582405077520412115)
    ·
      refine ⟨5717759373607616280618173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811839582405077520412115 5717759373607616280618173)
      ·
        refine ⟨2144159765102856105231815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5717759373607616280618173 2144159765102856105231815)
        ·
          refine ⟨3216239647654284157847723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144159765102856105231815 3216239647654284157847723)
          ·
            refine ⟨4824359471481426236771585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216239647654284157847723 4824359471481426236771585)
            ·
              refine ⟨3618269603611069677578689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4824359471481426236771585 3618269603611069677578689)
              ·
                refine ⟨2713702202708302258184017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618269603611069677578689 2713702202708302258184017)
                ·
                  refine ⟨2035276652031226693638013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2713702202708302258184017 2035276652031226693638013)
                  ·
                    refine ⟨763228744511710010114255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2035276652031226693638013 763228744511710010114255)
                    ·
                      rfl

theorem cell22_2229574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2229574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229574 prefixEnd_2229574 := by exact prefixLift 2229574
  have htrace : WordTrace (prefixWord ++ tailWord_2229574) baseStart_2229574 baseEnd_2229574 := by
    simpa [prefixWord, tailWord_2229574, baseEnd_2229574] using wordTrace_append hprefix tailTrace_2229574
  have hstable : (prefixWord ++ tailWord_2229574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229574).length < 2 ^ (prefixWord ++ tailWord_2229574).sum := by decide
  have hdescent : baseEnd_2229574 < baseStart_2229574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229662 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2229662 : Nat := 118140960795 + 2229662 * 2 ^ 59
def prefixEnd_2229662 : Nat := 4983230072969 + 3 ^ 40 * 2229662 * 2
def baseEnd_2229662 : Nat := 763258868710107113913985

theorem tailTrace_2229662 : CollatzResearch.WordTrace tailWord_2229662 prefixEnd_2229662 763258868710107113913985 := by
  unfold tailWord_2229662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165306756040355599749405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54214969365548563198663493 10165306756040355599749405)
  ·
    refine ⟨3811990033515133349906027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10165306756040355599749405 3811990033515133349906027)
    ·
      refine ⟨5717985050272700024859041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3811990033515133349906027 5717985050272700024859041)
      ·
        refine ⟨4288488787704525018644281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5717985050272700024859041 4288488787704525018644281)
        ·
          refine ⟨3216366590778393763983211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4288488787704525018644281 3216366590778393763983211)
          ·
            refine ⟨4824549886167590645974817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216366590778393763983211 4824549886167590645974817)
            ·
              refine ⟨3618412414625692984481113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4824549886167590645974817 3618412414625692984481113)
              ·
                refine ⟨2713809310969269738360835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618412414625692984481113 2713809310969269738360835)
                ·
                  refine ⟨4070713966453904607541253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713809310969269738360835 4070713966453904607541253)
                  ·
                    refine ⟨763258868710107113913985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4070713966453904607541253 763258868710107113913985)
                    ·
                      rfl

theorem cell22_2229662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2229662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229662 prefixEnd_2229662 := by exact prefixLift 2229662
  have htrace : WordTrace (prefixWord ++ tailWord_2229662) baseStart_2229662 baseEnd_2229662 := by
    simpa [prefixWord, tailWord_2229662, baseEnd_2229662] using wordTrace_append hprefix tailTrace_2229662
  have hstable : (prefixWord ++ tailWord_2229662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229662).length < 2 ^ (prefixWord ++ tailWord_2229662).sum := by decide
  have hdescent : baseEnd_2229662 < baseStart_2229662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229671 : List Nat := [1, 1, 6, 1, 1, 1, 3, 8]
def baseStart_2229671 : Nat := 118140960795 + 2229671 * 2 ^ 59
def prefixEnd_2229671 : Nat := 4983230072969 + 3 ^ 40 * 2229671 * 2
def baseEnd_2229671 : Nat := 84806883288226010048773

theorem tailTrace_2229671 : CollatzResearch.WordTrace tailWord_2229671 prefixEnd_2229671 84806883288226010048773 := by
  unfold tailWord_2229671
  simp only [CollatzResearch.WordTrace]
  refine ⟨81322782305290239335072867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54215188203526826223381911 81322782305290239335072867)
  ·
    refine ⟨121984173457935359002609301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81322782305290239335072867 121984173457935359002609301)
    ·
      refine ⟨5718008130840719953247311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121984173457935359002609301 5718008130840719953247311)
      ·
        refine ⟨8577012196261079929870967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5718008130840719953247311 8577012196261079929870967)
        ·
          refine ⟨12865518294391619894806451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8577012196261079929870967 12865518294391619894806451)
          ·
            refine ⟨19298277441587429842209677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12865518294391619894806451 19298277441587429842209677)
            ·
              refine ⟨7236854040595286190828629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19298277441587429842209677 7236854040595286190828629)
              ·
                refine ⟨84806883288226010048773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7236854040595286190828629 84806883288226010048773)
                ·
                  rfl

theorem cell22_2229671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 8].length) (baseStart_2229671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229671 prefixEnd_2229671 := by exact prefixLift 2229671
  have htrace : WordTrace (prefixWord ++ tailWord_2229671) baseStart_2229671 baseEnd_2229671 := by
    simpa [prefixWord, tailWord_2229671, baseEnd_2229671] using wordTrace_append hprefix tailTrace_2229671
  have hstable : (prefixWord ++ tailWord_2229671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229671).length < 2 ^ (prefixWord ++ tailWord_2229671).sum := by decide
  have hdescent : baseEnd_2229671 < baseStart_2229671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229677 : List Nat := [1, 5, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2229677 : Nat := 118140960795 + 2229677 * 2 ^ 59
def prefixEnd_2229677 : Nat := 4983230072969 + 3 ^ 40 * 2229677 * 2
def baseEnd_2229677 : Nat := 254421334505550691596313

theorem tailTrace_2229677 : CollatzResearch.WordTrace tailWord_2229677 prefixEnd_2229677 254421334505550691596313 := by
  unfold tailWord_2229677
  simp only [CollatzResearch.WordTrace]
  refine ⟨81323001143268502359791285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54215334095512334906527523 81323001143268502359791285)
  ·
    refine ⟨7624031357181422096230433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81323001143268502359791285 7624031357181422096230433)
    ·
      refine ⟨5718023517886066572172825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7624031357181422096230433 5718023517886066572172825)
      ·
        refine ⟨4288517638414549929129619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5718023517886066572172825 4288517638414549929129619)
        ·
          refine ⟨6432776457621824893694429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288517638414549929129619 6432776457621824893694429)
          ·
            refine ⟨2412291171608184335135411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6432776457621824893694429 2412291171608184335135411)
            ·
              refine ⟨3618436757412276502703117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412291171608184335135411 3618436757412276502703117)
              ·
                refine ⟨1356913784029603688513669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3618436757412276502703117 1356913784029603688513669)
                ·
                  refine ⟨254421334505550691596313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356913784029603688513669 254421334505550691596313)
                  ·
                    rfl

theorem cell22_2229677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2229677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229677 prefixEnd_2229677 := by exact prefixLift 2229677
  have htrace : WordTrace (prefixWord ++ tailWord_2229677) baseStart_2229677 baseEnd_2229677 := by
    simpa [prefixWord, tailWord_2229677, baseEnd_2229677] using wordTrace_append hprefix tailTrace_2229677
  have hstable : (prefixWord ++ tailWord_2229677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229677).length < 2 ^ (prefixWord ++ tailWord_2229677).sum := by decide
  have hdescent : baseEnd_2229677 < baseStart_2229677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229750 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_2229750 : Nat := 118140960795 + 2229750 * 2 ^ 59
def prefixEnd_2229750 : Nat := 4983230072969 + 3 ^ 40 * 2229750 * 2
def baseEnd_2229750 : Nat := 254429664302834739237905

theorem tailTrace_2229750 : CollatzResearch.WordTrace tailWord_2229750 prefixEnd_2229750 254429664302834739237905 := by
  unfold tailWord_2229750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082853979500252239199919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54217109114669357218132469 5082853979500252239199919)
  ·
    refine ⟨7624280969250378358799879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5082853979500252239199919 7624280969250378358799879)
    ·
      refine ⟨11436421453875567538199819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7624280969250378358799879 11436421453875567538199819)
      ·
        refine ⟨17154632180813351307299729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11436421453875567538199819 17154632180813351307299729)
        ·
          refine ⟨12865974135610013480474797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17154632180813351307299729 12865974135610013480474797)
          ·
            refine ⟨4824740300853755055178049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12865974135610013480474797 4824740300853755055178049)
            ·
              refine ⟨3618555225640316291383537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4824740300853755055178049 3618555225640316291383537)
              ·
                refine ⟨2713916419230237218537653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618555225640316291383537 2713916419230237218537653)
                ·
                  refine ⟨254429664302834739237905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2713916419230237218537653 254429664302834739237905)
                  ·
                    rfl

theorem cell22_2229750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_2229750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229750 prefixEnd_2229750 := by exact prefixLift 2229750
  have htrace : WordTrace (prefixWord ++ tailWord_2229750) baseStart_2229750 baseEnd_2229750 := by
    simpa [prefixWord, tailWord_2229750, baseEnd_2229750] using wordTrace_append hprefix tailTrace_2229750
  have hstable : (prefixWord ++ tailWord_2229750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229750).length < 2 ^ (prefixWord ++ tailWord_2229750).sum := by decide
  have hdescent : baseEnd_2229750 < baseStart_2229750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229793 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2229793 : Nat := 118140960795 + 2229793 * 2 ^ 59
def prefixEnd_2229793 : Nat := 4983230072969 + 3 ^ 40 * 2229793 * 2
def baseEnd_2229793 : Nat := 763303712687266438888583

theorem tailTrace_2229793 : CollatzResearch.WordTrace tailWord_2229793 prefixEnd_2229793 763303712687266438888583 := by
  unfold tailWord_2229793
  simp only [CollatzResearch.WordTrace]
  refine ⟨81327232010848254171014033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54218154673898836114009355 81327232010848254171014033)
  ·
    refine ⟨60995424008136190628260525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81327232010848254171014033 60995424008136190628260525)
    ·
      refine ⟨22873284003051071485597697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60995424008136190628260525 22873284003051071485597697)
      ·
        refine ⟨17154963002288303614198273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22873284003051071485597697 17154963002288303614198273)
        ·
          refine ⟨12866222251716227710648705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17154963002288303614198273 12866222251716227710648705)
          ·
            refine ⟨9649666688787170782986529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12866222251716227710648705 9649666688787170782986529)
            ·
              refine ⟨7237250016590378087239897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9649666688787170782986529 7237250016590378087239897)
              ·
                refine ⟨5427937512442783565429923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7237250016590378087239897 5427937512442783565429923)
                ·
                  refine ⟨8141906268664175348144885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427937512442783565429923 8141906268664175348144885)
                  ·
                    refine ⟨763303712687266438888583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8141906268664175348144885 763303712687266438888583)
                    ·
                      rfl

theorem cell22_2229793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2229793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229793 prefixEnd_2229793 := by exact prefixLift 2229793
  have htrace : WordTrace (prefixWord ++ tailWord_2229793) baseStart_2229793 baseEnd_2229793 := by
    simpa [prefixWord, tailWord_2229793, baseEnd_2229793] using wordTrace_append hprefix tailTrace_2229793
  have hstable : (prefixWord ++ tailWord_2229793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229793).length < 2 ^ (prefixWord ++ tailWord_2229793).sum := by decide
  have hdescent : baseEnd_2229793 < baseStart_2229793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229868 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 5]
def baseStart_2229868 : Nat := 118140960795 + 2229868 * 2 ^ 59
def prefixEnd_2229868 : Nat := 4983230072969 + 3 ^ 40 * 2229868 * 2
def baseEnd_2229868 : Nat := 254443128906663747754451

theorem tailTrace_2229868 : CollatzResearch.WordTrace tailWord_2229868 prefixEnd_2229868 254443128906663747754451 := by
  unfold tailWord_2229868
  simp only [CollatzResearch.WordTrace]
  refine ⟨40664983742788270989997129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54219978323717694653329505 40664983742788270989997129)
  ·
    refine ⟨30498737807091203242497847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40664983742788270989997129 30498737807091203242497847)
    ·
      refine ⟨45748106710636804863746771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30498737807091203242497847 45748106710636804863746771)
      ·
        refine ⟨68622160065955207295620157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45748106710636804863746771 68622160065955207295620157)
        ·
          refine ⟨25733310024733202735857559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68622160065955207295620157 25733310024733202735857559)
          ·
            refine ⟨38599965037099804103786339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25733310024733202735857559 38599965037099804103786339)
            ·
              refine ⟨57899947555649706155679509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38599965037099804103786339 57899947555649706155679509)
              ·
                refine ⟨2714060041671079976047477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57899947555649706155679509 2714060041671079976047477)
                ·
                  refine ⟨254443128906663747754451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2714060041671079976047477 254443128906663747754451)
                  ·
                    rfl

theorem cell22_2229868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_2229868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229868 prefixEnd_2229868 := by exact prefixLift 2229868
  have htrace : WordTrace (prefixWord ++ tailWord_2229868) baseStart_2229868 baseEnd_2229868 := by
    simpa [prefixWord, tailWord_2229868, baseEnd_2229868] using wordTrace_append hprefix tailTrace_2229868
  have hstable : (prefixWord ++ tailWord_2229868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229868).length < 2 ^ (prefixWord ++ tailWord_2229868).sum := by decide
  have hdescent : baseEnd_2229868 < baseStart_2229868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229872 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 3, 3]
def baseStart_2229872 : Nat := 118140960795 + 2229872 * 2 ^ 59
def prefixEnd_2229872 : Nat := 4983230072969 + 3 ^ 40 * 2229872 * 2
def baseEnd_2229872 : Nat := 763330756001736566163341

theorem tailTrace_2229872 : CollatzResearch.WordTrace tailWord_2229872 prefixEnd_2229872 763330756001736566163341 := by
  unfold tailWord_2229872
  simp only [CollatzResearch.WordTrace]
  refine ⟨40665056688781025331569935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54220075585041367108759913 40665056688781025331569935)
  ·
    refine ⟨60997585033171537997354903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40665056688781025331569935 60997585033171537997354903)
    ·
      refine ⟨91496377549757306996032355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60997585033171537997354903 91496377549757306996032355)
      ·
        refine ⟨137244566324635960494048533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91496377549757306996032355 137244566324635960494048533)
        ·
          refine ⟨6433339046467310648158525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 137244566324635960494048533 6433339046467310648158525)
          ·
            refine ⟨2412502142425241493059447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6433339046467310648158525 2412502142425241493059447)
            ·
              refine ⟨3618753213637862239589171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412502142425241493059447 3618753213637862239589171)
              ·
                refine ⟨5428129820456793359383757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618753213637862239589171 5428129820456793359383757)
                ·
                  refine ⟨2035548682671297509768909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5428129820456793359383757 2035548682671297509768909)
                  ·
                    refine ⟨763330756001736566163341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2035548682671297509768909 763330756001736566163341)
                    ·
                      rfl

theorem cell22_2229872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_2229872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229872 prefixEnd_2229872 := by exact prefixLift 2229872
  have htrace : WordTrace (prefixWord ++ tailWord_2229872) baseStart_2229872 baseEnd_2229872 := by
    simpa [prefixWord, tailWord_2229872, baseEnd_2229872] using wordTrace_append hprefix tailTrace_2229872
  have hstable : (prefixWord ++ tailWord_2229872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229872).length < 2 ^ (prefixWord ++ tailWord_2229872).sum := by decide
  have hdescent : baseEnd_2229872 < baseStart_2229872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229885 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2229885 : Nat := 118140960795 + 2229885 * 2 ^ 59
def prefixEnd_2229885 : Nat := 4983230072969 + 3 ^ 40 * 2229885 * 2
def baseEnd_2229885 : Nat := 254445068722469621862767

theorem tailTrace_2229885 : CollatzResearch.WordTrace tailWord_2229885 prefixEnd_2229885 254445068722469621862767 := by
  unfold tailWord_2229885
  simp only [CollatzResearch.WordTrace]
  refine ⟨81330587526514953883363109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54220391684343302588908739 81330587526514953883363109)
  ·
    refine ⟨15249485161221553853130583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81330587526514953883363109 15249485161221553853130583)
    ·
      refine ⟨22874227741832330779695875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15249485161221553853130583 22874227741832330779695875)
      ·
        refine ⟨34311341612748496169543813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22874227741832330779695875 34311341612748496169543813)
        ·
          refine ⟨6433376552390343031789465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34311341612748496169543813 6433376552390343031789465)
          ·
            refine ⟨4825032414292757273842099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6433376552390343031789465 4825032414292757273842099)
            ·
              refine ⟨7237548621439135910763149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4825032414292757273842099 7237548621439135910763149)
              ·
                refine ⟨2714080733039675966536181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7237548621439135910763149 2714080733039675966536181)
                ·
                  refine ⟨254445068722469621862767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2714080733039675966536181 254445068722469621862767)
                  ·
                    rfl

theorem cell22_2229885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2229885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229885 prefixEnd_2229885 := by exact prefixLift 2229885
  have htrace : WordTrace (prefixWord ++ tailWord_2229885) baseStart_2229885 baseEnd_2229885 := by
    simpa [prefixWord, tailWord_2229885, baseEnd_2229885] using wordTrace_append hprefix tailTrace_2229885
  have hstable : (prefixWord ++ tailWord_2229885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229885).length < 2 ^ (prefixWord ++ tailWord_2229885).sum := by decide
  have hdescent : baseEnd_2229885 < baseStart_2229885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2229964 : List Nat := [2, 2, 1, 5, 2, 1, 2, 3, 4]
def baseStart_2229964 : Nat := 118140960795 + 2229964 * 2 ^ 59
def prefixEnd_2229964 : Nat := 4983230072969 + 3 ^ 40 * 2229964 * 2
def baseEnd_2229964 : Nat := 254454083160626330954353

theorem tailTrace_2229964 : CollatzResearch.WordTrace tailWord_2229964 prefixEnd_2229964 254454083160626330954353 := by
  unfold tailWord_2229964
  simp only [CollatzResearch.WordTrace]
  refine ⟨40666734446614375187744473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54222312595485833583659297 40666734446614375187744473)
  ·
    refine ⟨30500050834960781390808355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40666734446614375187744473 30500050834960781390808355)
    ·
      refine ⟨45750076252441172086212533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30500050834960781390808355 45750076252441172086212533)
      ·
        refine ⟨4289069648666359883082425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45750076252441172086212533 4289069648666359883082425)
        ·
          refine ⟨3216802236499769912311819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4289069648666359883082425 3216802236499769912311819)
          ·
            refine ⟨4825203354749654868467729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216802236499769912311819 4825203354749654868467729)
            ·
              refine ⟨3618902516062241151350797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825203354749654868467729 3618902516062241151350797)
              ·
                refine ⟨1357088443523340431756549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3618902516062241151350797 1357088443523340431756549)
                ·
                  refine ⟨254454083160626330954353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357088443523340431756549 254454083160626330954353)
                  ·
                    rfl

theorem cell22_2229964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_2229964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2229964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2229964 prefixEnd_2229964 := by exact prefixLift 2229964
  have htrace : WordTrace (prefixWord ++ tailWord_2229964) baseStart_2229964 baseEnd_2229964 := by
    simpa [prefixWord, tailWord_2229964, baseEnd_2229964] using wordTrace_append hprefix tailTrace_2229964
  have hstable : (prefixWord ++ tailWord_2229964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2229964).length < 2 ^ (prefixWord ++ tailWord_2229964).sum := by decide
  have hdescent : baseEnd_2229964 < baseStart_2229964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2229964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230020 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 7]
def baseStart_2230020 : Nat := 118140960795 + 2230020 * 2 ^ 59
def prefixEnd_2230020 : Nat := 4983230072969 + 3 ^ 40 * 2230020 * 2
def baseEnd_2230020 : Nat := 254460473142104504487629

theorem tailTrace_2230020 : CollatzResearch.WordTrace tailWord_2230020 prefixEnd_2230020 254460473142104504487629 := by
  unfold tailWord_2230020
  simp only [CollatzResearch.WordTrace]
  refine ⟨40667755690512935969763757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54223674254017247959685009 40667755690512935969763757)
  ·
    refine ⟨15250408383942350988661409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40667755690512935969763757 15250408383942350988661409)
    ·
      refine ⟨11437806287956763241496057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15250408383942350988661409 11437806287956763241496057)
      ·
        refine ⟨8578354715967572431122043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11437806287956763241496057 8578354715967572431122043)
        ·
          refine ⟨12867532073951358646683065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8578354715967572431122043 12867532073951358646683065)
          ·
            refine ⟨9650649055463518985012299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12867532073951358646683065 9650649055463518985012299)
            ·
              refine ⟨14475973583195278477518449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9650649055463518985012299 14475973583195278477518449)
              ·
                refine ⟨10856980187396458858138837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14475973583195278477518449 10856980187396458858138837)
                ·
                  refine ⟨254460473142104504487629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10856980187396458858138837 254460473142104504487629)
                  ·
                    rfl

theorem cell22_2230020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_2230020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230020 prefixEnd_2230020 := by exact prefixLift 2230020
  have htrace : WordTrace (prefixWord ++ tailWord_2230020) baseStart_2230020 baseEnd_2230020 := by
    simpa [prefixWord, tailWord_2230020, baseEnd_2230020] using wordTrace_append hprefix tailTrace_2230020
  have hstable : (prefixWord ++ tailWord_2230020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230020).length < 2 ^ (prefixWord ++ tailWord_2230020).sum := by decide
  have hdescent : baseEnd_2230020 < baseStart_2230020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230067 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 3, 4]
def baseStart_2230067 : Nat := 118140960795 + 2230067 * 2 ^ 59
def prefixEnd_2230067 : Nat := 4983230072969 + 3 ^ 40 * 2230067 * 2
def baseEnd_2230067 : Nat := 763397508486821057537743

theorem tailTrace_2230067 : CollatzResearch.WordTrace tailWord_2230067 prefixEnd_2230067 763397508486821057537743 := by
  unfold tailWord_2230067
  simp only [CollatzResearch.WordTrace]
  refine ⟨81337225611855598966488455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54224817074570399310992303 81337225611855598966488455)
  ·
    refine ⟨122005838417783398449732683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81337225611855598966488455 122005838417783398449732683)
    ·
      refine ⟨183008757626675097674599025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122005838417783398449732683 183008757626675097674599025)
      ·
        refine ⟨137256568220006323255949269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183008757626675097674599025 137256568220006323255949269)
        ·
          refine ⟨3216950817656398201311311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 137256568220006323255949269 3216950817656398201311311)
          ·
            refine ⟨4825426226484597301966967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216950817656398201311311 4825426226484597301966967)
            ·
              refine ⟨7238139339726895952950451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4825426226484597301966967 7238139339726895952950451)
              ·
                refine ⟨10857209009590343929425677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238139339726895952950451 10857209009590343929425677)
                ·
                  refine ⟨4071453378596378973534629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10857209009590343929425677 4071453378596378973534629)
                  ·
                    refine ⟨763397508486821057537743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071453378596378973534629 763397508486821057537743)
                    ·
                      rfl

theorem cell22_2230067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4].length) (baseStart_2230067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230067 prefixEnd_2230067 := by exact prefixLift 2230067
  have htrace : WordTrace (prefixWord ++ tailWord_2230067) baseStart_2230067 baseEnd_2230067 := by
    simpa [prefixWord, tailWord_2230067, baseEnd_2230067] using wordTrace_append hprefix tailTrace_2230067
  have hstable : (prefixWord ++ tailWord_2230067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230067).length < 2 ^ (prefixWord ++ tailWord_2230067).sum := by decide
  have hdescent : baseEnd_2230067 < baseStart_2230067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230114 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2230114 : Nat := 118140960795 + 2230114 * 2 ^ 59
def prefixEnd_2230114 : Nat := 4983230072969 + 3 ^ 40 * 2230114 * 2
def baseEnd_2230114 : Nat := 763413597547328601612599

theorem tailTrace_2230114 : CollatzResearch.WordTrace tailWord_2230114 prefixEnd_2230114 763413597547328601612599 := by
  unfold tailWord_2230114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20334734960671331498362349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54225959895123550662299597 20334734960671331498362349)
  ·
    refine ⟨7625525610251749311885881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20334734960671331498362349 7625525610251749311885881)
    ·
      refine ⟨5719144207688811983914411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7625525610251749311885881 5719144207688811983914411)
      ·
        refine ⟨8578716311533217975871617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5719144207688811983914411 8578716311533217975871617)
        ·
          refine ⟨6434037233649913481903713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8578716311533217975871617 6434037233649913481903713)
          ·
            refine ⟨4825527925237435111427785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6434037233649913481903713 4825527925237435111427785)
            ·
              refine ⟨3619145943928076333570839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825527925237435111427785 3619145943928076333570839)
              ·
                refine ⟨5428718915892114500356259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619145943928076333570839 5428718915892114500356259)
                ·
                  refine ⟨8143078373838171750534389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5428718915892114500356259 8143078373838171750534389)
                  ·
                    refine ⟨763413597547328601612599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8143078373838171750534389 763413597547328601612599)
                    ·
                      rfl

theorem cell22_2230114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2230114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230114 prefixEnd_2230114 := by exact prefixLift 2230114
  have htrace : WordTrace (prefixWord ++ tailWord_2230114) baseStart_2230114 baseEnd_2230114 := by
    simpa [prefixWord, tailWord_2230114, baseEnd_2230114] using wordTrace_append hprefix tailTrace_2230114
  have hstable : (prefixWord ++ tailWord_2230114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230114).length < 2 ^ (prefixWord ++ tailWord_2230114).sum := by decide
  have hdescent : baseEnd_2230114 < baseStart_2230114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230193 : List Nat := [1, 2, 2, 4, 2, 3, 1, 3, 1, 3]
def baseStart_2230193 : Nat := 118140960795 + 2230193 * 2 ^ 59
def prefixEnd_2230193 : Nat := 4983230072969 + 3 ^ 40 * 2230193 * 2
def baseEnd_2230193 : Nat := 763440640861798728887357

theorem tailTrace_2230193 : CollatzResearch.WordTrace tailWord_2230193 prefixEnd_2230193 763440640861798728887357 := by
  unfold tailWord_2230193
  simp only [CollatzResearch.WordTrace]
  refine ⟨81341821209399122485575233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54227880806266081657050155 81341821209399122485575233)
  ·
    refine ⟨61006365907049341864181425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81341821209399122485575233 61006365907049341864181425)
    ·
      refine ⟨45754774430287006398136069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61006365907049341864181425 45754774430287006398136069)
      ·
        refine ⟨8579020205678813699650513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45754774430287006398136069 8579020205678813699650513)
        ·
          refine ⟨6434265154259110274737885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8579020205678813699650513 6434265154259110274737885)
          ·
            refine ⟨2412849432847166353026707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6434265154259110274737885 2412849432847166353026707)
            ·
              refine ⟨3619274149270749529540061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412849432847166353026707 3619274149270749529540061)
              ·
                refine ⟨1357227805976531073577523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3619274149270749529540061 1357227805976531073577523)
                ·
                  refine ⟨2035841708964796610366285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357227805976531073577523 2035841708964796610366285)
                  ·
                    refine ⟨763440640861798728887357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2035841708964796610366285 763440640861798728887357)
                    ·
                      rfl

theorem cell22_2230193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_2230193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230193 prefixEnd_2230193 := by exact prefixLift 2230193
  have htrace : WordTrace (prefixWord ++ tailWord_2230193) baseStart_2230193 baseEnd_2230193 := by
    simpa [prefixWord, tailWord_2230193, baseEnd_2230193] using wordTrace_append hprefix tailTrace_2230193
  have hstable : (prefixWord ++ tailWord_2230193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230193).length < 2 ^ (prefixWord ++ tailWord_2230193).sum := by decide
  have hdescent : baseEnd_2230193 < baseStart_2230193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230232 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_2230232 : Nat := 118140960795 + 2230232 * 2 ^ 59
def prefixEnd_2230232 : Nat := 4983230072969 + 3 ^ 40 * 2230232 * 2
def baseEnd_2230232 : Nat := 763453991358815627162237

theorem tailTrace_2230232 : CollatzResearch.WordTrace tailWord_2230232 prefixEnd_2230232 763453991358815627162237 := by
  unfold tailWord_2230232
  simp only [CollatzResearch.WordTrace]
  refine ⟨40671621828128916073122475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54228829104171888097496633 40671621828128916073122475)
  ·
    refine ⟨61007432742193374109683713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40671621828128916073122475 61007432742193374109683713)
    ·
      refine ⟨45755574556645030582262785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61007432742193374109683713 45755574556645030582262785)
      ·
        refine ⟨34316680917483772936697089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45755574556645030582262785 34316680917483772936697089)
        ·
          refine ⟨25737510688112829702522817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34316680917483772936697089 25737510688112829702522817)
          ·
            refine ⟨19303133016084622276892113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25737510688112829702522817 19303133016084622276892113)
            ·
              refine ⟨14477349762063466707669085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19303133016084622276892113 14477349762063466707669085)
              ·
                refine ⟨5429006160773800015375907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14477349762063466707669085 5429006160773800015375907)
                ·
                  refine ⟨8143509241160700023063861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5429006160773800015375907 8143509241160700023063861)
                  ·
                    refine ⟨763453991358815627162237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8143509241160700023063861 763453991358815627162237)
                    ·
                      rfl

theorem cell22_2230232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_2230232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230232 prefixEnd_2230232 := by exact prefixLift 2230232
  have htrace : WordTrace (prefixWord ++ tailWord_2230232) baseStart_2230232 baseEnd_2230232 := by
    simpa [prefixWord, tailWord_2230232, baseEnd_2230232] using wordTrace_append hprefix tailTrace_2230232
  have hstable : (prefixWord ++ tailWord_2230232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230232).length < 2 ^ (prefixWord ++ tailWord_2230232).sum := by decide
  have hdescent : baseEnd_2230232 < baseStart_2230232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230262 : List Nat := [5, 1, 1, 1, 14]
def baseStart_2230262 : Nat := 118140960795 + 2230262 * 2 ^ 59
def prefixEnd_2230262 : Nat := 4983230072969 + 3 ^ 40 * 2230262 * 2
def baseEnd_2230262 : Nat := 3141828234452286209515

theorem tailTrace_2230262 : CollatzResearch.WordTrace tailWord_2230262 prefixEnd_2230262 3141828234452286209515 := by
  unfold tailWord_2230262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5084021115384321704364815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54229558564099431513224693 5084021115384321704364815)
  ·
    refine ⟨7626031673076482556547223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5084021115384321704364815 7626031673076482556547223)
    ·
      refine ⟨11439047509614723834820835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7626031673076482556547223 11439047509614723834820835)
      ·
        refine ⟨17158571264422085752231253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11439047509614723834820835 17158571264422085752231253)
        ·
          refine ⟨3141828234452286209515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 17158571264422085752231253 3141828234452286209515)
          ·
            rfl

theorem cell22_2230262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 14].length) (baseStart_2230262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230262 prefixEnd_2230262 := by exact prefixLift 2230262
  have htrace : WordTrace (prefixWord ++ tailWord_2230262) baseStart_2230262 baseEnd_2230262 := by
    simpa [prefixWord, tailWord_2230262, baseEnd_2230262] using wordTrace_append hprefix tailTrace_2230262
  have hstable : (prefixWord ++ tailWord_2230262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230262).length < 2 ^ (prefixWord ++ tailWord_2230262).sum := by decide
  have hdescent : baseEnd_2230262 < baseStart_2230262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230279 : List Nat := [1, 1, 4, 3, 1, 4, 1, 7]
def baseStart_2230279 : Nat := 118140960795 + 2230279 * 2 ^ 59
def prefixEnd_2230279 : Nat := 4983230072969 + 3 ^ 40 * 2230279 * 2
def baseEnd_2230279 : Nat := 84830008935480352359677

theorem tailTrace_2230279 : CollatzResearch.WordTrace tailWord_2230279 prefixEnd_2230279 84830008935480352359677 := by
  unfold tailWord_2230279
  simp only [CollatzResearch.WordTrace]
  refine ⟨81344957887087559173205891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54229971924725039448803927 81344957887087559173205891)
  ·
    refine ⟨122017436830631338759808837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81344957887087559173205891 122017436830631338759808837)
    ·
      refine ⟨22878269405743376017464157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122017436830631338759808837 22878269405743376017464157)
      ·
        refine ⟨8579351027153766006549059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22878269405743376017464157 8579351027153766006549059)
        ·
          refine ⟨12869026540730649009823589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8579351027153766006549059 12869026540730649009823589)
          ·
            refine ⟨2412942476386996689341923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12869026540730649009823589 2412942476386996689341923)
            ·
              refine ⟨3619413714580495034012885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412942476386996689341923 3619413714580495034012885)
              ·
                refine ⟨84830008935480352359677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3619413714580495034012885 84830008935480352359677)
                ·
                  rfl

theorem cell22_2230279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 7].length) (baseStart_2230279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230279 prefixEnd_2230279 := by exact prefixLift 2230279
  have htrace : WordTrace (prefixWord ++ tailWord_2230279) baseStart_2230279 baseEnd_2230279 := by
    simpa [prefixWord, tailWord_2230279, baseEnd_2230279] using wordTrace_append hprefix tailTrace_2230279
  have hstable : (prefixWord ++ tailWord_2230279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230279).length < 2 ^ (prefixWord ++ tailWord_2230279).sum := by decide
  have hdescent : baseEnd_2230279 < baseStart_2230279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230307 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 7]
def baseStart_2230307 : Nat := 118140960795 + 2230307 * 2 ^ 59
def prefixEnd_2230307 : Nat := 4983230072969 + 3 ^ 40 * 2230307 * 2
def baseEnd_2230307 : Nat := 254493221797180143845669

theorem tailTrace_2230307 : CollatzResearch.WordTrace tailWord_2230307 prefixEnd_2230307 254493221797180143845669 := by
  unfold tailWord_2230307
  simp only [CollatzResearch.WordTrace]
  refine ⟨81345979130986119955225175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54230652753990746636816783 81345979130986119955225175)
  ·
    refine ⟨122018968696479179932837763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81345979130986119955225175 122018968696479179932837763)
    ·
      refine ⟨183028453044718769899256645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122018968696479179932837763 183028453044718769899256645)
      ·
        refine ⟨34317834945884769356110621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183028453044718769899256645 34317834945884769356110621)
        ·
          refine ⟨12869188104706788508541483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34317834945884769356110621 12869188104706788508541483)
          ·
            refine ⟨19303782157060182762812225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12869188104706788508541483 19303782157060182762812225)
            ·
              refine ⟨14477836617795137072109169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19303782157060182762812225 14477836617795137072109169)
              ·
                refine ⟨10858377463346352804081877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14477836617795137072109169 10858377463346352804081877)
                ·
                  refine ⟨254493221797180143845669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10858377463346352804081877 254493221797180143845669)
                  ·
                    rfl

theorem cell22_2230307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_2230307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230307 prefixEnd_2230307 := by exact prefixLift 2230307
  have htrace : WordTrace (prefixWord ++ tailWord_2230307) baseStart_2230307 baseEnd_2230307 := by
    simpa [prefixWord, tailWord_2230307, baseEnd_2230307] using wordTrace_append hprefix tailTrace_2230307
  have hstable : (prefixWord ++ tailWord_2230307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230307).length < 2 ^ (prefixWord ++ tailWord_2230307).sum := by decide
  have hdescent : baseEnd_2230307 < baseStart_2230307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230386 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_2230386 : Nat := 118140960795 + 2230386 * 2 ^ 59
def prefixEnd_2230386 : Nat := 4983230072969 + 3 ^ 40 * 2230386 * 2
def baseEnd_2230386 : Nat := 254502236235336852937255

theorem tailTrace_2230386 : CollatzResearch.WordTrace tailWord_2230386 prefixEnd_2230386 254502236235336852937255 := by
  unfold tailWord_2230386
  simp only [CollatzResearch.WordTrace]
  refine ⟨20337215124424979111837753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54232573665133277631567341 20337215124424979111837753)
  ·
    refine ⟨15252911343318734333878315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20337215124424979111837753 15252911343318734333878315)
    ·
      refine ⟨22879367014978101500817473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15252911343318734333878315 22879367014978101500817473)
      ·
        refine ⟨17159525261233576125613105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22879367014978101500817473 17159525261233576125613105)
        ·
          refine ⟨12869643945925182094209829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17159525261233576125613105 12869643945925182094209829)
          ·
            refine ⟨2413058239860971642664343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12869643945925182094209829 2413058239860971642664343)
            ·
              refine ⟨3619587359791457463996515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413058239860971642664343 3619587359791457463996515)
              ·
                refine ⟨5429381039687186195994773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619587359791457463996515 5429381039687186195994773)
                ·
                  refine ⟨254502236235336852937255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5429381039687186195994773 254502236235336852937255)
                  ·
                    rfl

theorem cell22_2230386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_2230386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230386 prefixEnd_2230386 := by exact prefixLift 2230386
  have htrace : WordTrace (prefixWord ++ tailWord_2230386) baseStart_2230386 baseEnd_2230386 := by
    simpa [prefixWord, tailWord_2230386, baseEnd_2230386] using wordTrace_append hprefix tailTrace_2230386
  have hstable : (prefixWord ++ tailWord_2230386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230386).length < 2 ^ (prefixWord ++ tailWord_2230386).sum := by decide
  have hdescent : baseEnd_2230386 < baseStart_2230386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230452 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2230452 : Nat := 118140960795 + 2230452 * 2 ^ 59
def prefixEnd_2230452 : Nat := 4983230072969 + 3 ^ 40 * 2230452 * 2
def baseEnd_2230452 : Nat := 763529301854808386661563

theorem tailTrace_2230452 : CollatzResearch.WordTrace tailWord_2230452 prefixEnd_2230452 763529301854808386661563 := by
  unfold tailWord_2230452
  simp only [CollatzResearch.WordTrace]
  refine ⟨40675633857730404859626805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54234178476973873146169073 40675633857730404859626805)
  ·
    refine ⟨3813340674162225455590013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40675633857730404859626805 3813340674162225455590013)
    ·
      refine ⟨1430002752810834545846255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3813340674162225455590013 1430002752810834545846255)
      ·
        refine ⟨2145004129216251818769383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430002752810834545846255 2145004129216251818769383)
        ·
          refine ⟨3217506193824377728154075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145004129216251818769383 3217506193824377728154075)
          ·
            refine ⟨4826259290736566592231113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217506193824377728154075 4826259290736566592231113)
            ·
              refine ⟨3619694468052424944173335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4826259290736566592231113 3619694468052424944173335)
              ·
                refine ⟨5429541702078637416260003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619694468052424944173335 5429541702078637416260003)
                ·
                  refine ⟨8144312553117956124390005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5429541702078637416260003 8144312553117956124390005)
                  ·
                    refine ⟨763529301854808386661563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8144312553117956124390005 763529301854808386661563)
                    ·
                      rfl

theorem cell22_2230452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2230452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230452 prefixEnd_2230452 := by exact prefixLift 2230452
  have htrace : WordTrace (prefixWord ++ tailWord_2230452) baseStart_2230452 baseEnd_2230452 := by
    simpa [prefixWord, tailWord_2230452, baseEnd_2230452] using wordTrace_append hprefix tailTrace_2230452
  have hstable : (prefixWord ++ tailWord_2230452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230452).length < 2 ^ (prefixWord ++ tailWord_2230452).sum := by decide
  have hdescent : baseEnd_2230452 < baseStart_2230452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230459 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 5]
def baseStart_2230459 : Nat := 118140960795 + 2230459 * 2 ^ 59
def prefixEnd_2230459 : Nat := 4983230072969 + 3 ^ 40 * 2230459 * 2
def baseEnd_2230459 : Nat := 254510566032620900578847

theorem tailTrace_2230459 : CollatzResearch.WordTrace tailWord_2230459 prefixEnd_2230459 254510566032620900578847 := by
  unfold tailWord_2230459
  simp only [CollatzResearch.WordTrace]
  refine ⟨81351523026435449914758431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54234348684290299943172287 81351523026435449914758431)
  ·
    refine ⟨122027284539653174872137647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81351523026435449914758431 122027284539653174872137647)
    ·
      refine ⟨183040926809479762308206471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122027284539653174872137647 183040926809479762308206471)
      ·
        refine ⟨274561390214219643462309707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183040926809479762308206471 274561390214219643462309707)
        ·
          refine ⟨411842085321329465193464561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274561390214219643462309707 411842085321329465193464561)
          ·
            refine ⟨308881563990997098895098421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411842085321329465193464561 308881563990997098895098421)
            ·
              refine ⟨28957646624155978021415477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 308881563990997098895098421 28957646624155978021415477)
              ·
                refine ⟨2714779371014622939507701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28957646624155978021415477 2714779371014622939507701)
                ·
                  refine ⟨254510566032620900578847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2714779371014622939507701 254510566032620900578847)
                  ·
                    rfl

theorem cell22_2230459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 5].length) (baseStart_2230459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230459 prefixEnd_2230459 := by exact prefixLift 2230459
  have htrace : WordTrace (prefixWord ++ tailWord_2230459) baseStart_2230459 baseEnd_2230459 := by
    simpa [prefixWord, tailWord_2230459, baseEnd_2230459] using wordTrace_append hprefix tailTrace_2230459
  have hstable : (prefixWord ++ tailWord_2230459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230459).length < 2 ^ (prefixWord ++ tailWord_2230459).sum := by decide
  have hdescent : baseEnd_2230459 < baseStart_2230459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230474 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_2230474 : Nat := 118140960795 + 2230474 * 2 ^ 59
def prefixEnd_2230474 : Nat := 4983230072969 + 3 ^ 40 * 2230474 * 2
def baseEnd_2230474 : Nat := 763536832904407662611495

theorem tailTrace_2230474 : CollatzResearch.WordTrace tailWord_2230474 prefixEnd_2230474 763536832904407662611495 := by
  unfold tailWord_2230474
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338017530345276869138619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54234713414254071651036317 20338017530345276869138619)
  ·
    refine ⟨30507026295517915303707929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20338017530345276869138619 30507026295517915303707929)
    ·
      refine ⟨22880269721638436477780947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30507026295517915303707929 22880269721638436477780947)
      ·
        refine ⟨34320404582457654716671421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22880269721638436477780947 34320404582457654716671421)
        ·
          refine ⟨12870151718421620518751783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34320404582457654716671421 12870151718421620518751783)
          ·
            refine ⟨19305227577632430778127675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12870151718421620518751783 19305227577632430778127675)
            ·
              refine ⟨28957841366448646167191513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19305227577632430778127675 28957841366448646167191513)
              ·
                refine ⟨21718381024836484625393635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28957841366448646167191513 21718381024836484625393635)
                ·
                  refine ⟨32577571537254726938090453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21718381024836484625393635 32577571537254726938090453)
                  ·
                    refine ⟨763536832904407662611495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32577571537254726938090453 763536832904407662611495)
                    ·
                      rfl

theorem cell22_2230474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_2230474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230474 prefixEnd_2230474 := by exact prefixLift 2230474
  have htrace : WordTrace (prefixWord ++ tailWord_2230474) baseStart_2230474 baseEnd_2230474 := by
    simpa [prefixWord, tailWord_2230474, baseEnd_2230474] using wordTrace_append hprefix tailTrace_2230474
  have hstable : (prefixWord ++ tailWord_2230474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230474).length < 2 ^ (prefixWord ++ tailWord_2230474).sum := by decide
  have hdescent : baseEnd_2230474 < baseStart_2230474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230493 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 5]
def baseStart_2230493 : Nat := 118140960795 + 2230493 * 2 ^ 59
def prefixEnd_2230493 : Nat := 4983230072969 + 3 ^ 40 * 2230493 * 2
def baseEnd_2230493 : Nat := 254514445664232648795479

theorem tailTrace_2230493 : CollatzResearch.WordTrace tailWord_2230493 prefixEnd_2230493 254514445664232648795479 := by
  unfold tailWord_2230493
  simp only [CollatzResearch.WordTrace]
  refine ⟨81352763108312273721496133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54235175405541515814330755 81352763108312273721496133)
  ·
    refine ⟨15253643082808551322780525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81352763108312273721496133 15253643082808551322780525)
    ·
      refine ⟨5720116156053206746042697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15253643082808551322780525 5720116156053206746042697)
      ·
        refine ⟨4290087117039905059532023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5720116156053206746042697 4290087117039905059532023)
        ·
          refine ⟨6435130675559857589298035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4290087117039905059532023 6435130675559857589298035)
          ·
            refine ⟨9652696013339786383947053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6435130675559857589298035 9652696013339786383947053)
            ·
              refine ⟨3619761005002419893980145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9652696013339786383947053 3619761005002419893980145)
              ·
                refine ⟨2714820753751814920485109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619761005002419893980145 2714820753751814920485109)
                ·
                  refine ⟨254514445664232648795479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2714820753751814920485109 254514445664232648795479)
                  ·
                    rfl

theorem cell22_2230493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_2230493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230493 prefixEnd_2230493 := by exact prefixLift 2230493
  have htrace : WordTrace (prefixWord ++ tailWord_2230493) baseStart_2230493 baseEnd_2230493 := by
    simpa [prefixWord, tailWord_2230493, baseEnd_2230493] using wordTrace_append hprefix tailTrace_2230493
  have hstable : (prefixWord ++ tailWord_2230493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230493).length < 2 ^ (prefixWord ++ tailWord_2230493).sum := by decide
  have hdescent : baseEnd_2230493 < baseStart_2230493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230538 : List Nat := [3, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_2230538 : Nat := 118140960795 + 2230538 * 2 ^ 59
def prefixEnd_2230538 : Nat := 4983230072969 + 3 ^ 40 * 2230538 * 2
def baseEnd_2230538 : Nat := 254519580470777609670433

theorem tailTrace_2230538 : CollatzResearch.WordTrace tailWord_2230538 prefixEnd_2230538 254519580470777609670433 := by
  unfold tailWord_2230538
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338601098287311601721067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54236269595432830937922845 20338601098287311601721067)
  ·
    refine ⟨30507901647430967402581601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20338601098287311601721067 30507901647430967402581601)
    ·
      refine ⟨22880926235573225551936201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30507901647430967402581601 22880926235573225551936201)
      ·
        refine ⟨17160694676679919163952151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22880926235573225551936201 17160694676679919163952151)
        ·
          refine ⟨25741042015019878745928227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17160694676679919163952151 25741042015019878745928227)
          ·
            refine ⟨38611563022529818118892341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25741042015019878745928227 38611563022529818118892341)
            ·
              refine ⟨3619834033362170448646157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38611563022529818118892341 3619834033362170448646157)
              ·
                refine ⟨1357437762510813918242309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3619834033362170448646157 1357437762510813918242309)
                ·
                  refine ⟨254519580470777609670433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357437762510813918242309 254519580470777609670433)
                  ·
                    rfl

theorem cell22_2230538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_2230538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230538 prefixEnd_2230538 := by exact prefixLift 2230538
  have htrace : WordTrace (prefixWord ++ tailWord_2230538) baseStart_2230538 baseEnd_2230538 := by
    simpa [prefixWord, tailWord_2230538, baseEnd_2230538] using wordTrace_append hprefix tailTrace_2230538
  have hstable : (prefixWord ++ tailWord_2230538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230538).length < 2 ^ (prefixWord ++ tailWord_2230538).sum := by decide
  have hdescent : baseEnd_2230538 < baseStart_2230538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230549 : List Nat := [1, 3, 2, 1, 2, 1, 12]
def baseStart_2230549 : Nat := 118140960795 + 2230549 * 2 ^ 59
def prefixEnd_2230549 : Nat := 4983230072969 + 3 ^ 40 * 2230549 * 2
def baseEnd_2230549 : Nat := 28280092849523424703195

theorem tailTrace_2230549 : CollatzResearch.WordTrace tailWord_2230549 prefixEnd_2230549 28280092849523424703195 := by
  unfold tailWord_2230549
  simp only [CollatzResearch.WordTrace]
  refine ⟨81354805596109395285534701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54236537064072930190356467 81354805596109395285534701)
  ·
    refine ⟨30508052098541023232075513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81354805596109395285534701 30508052098541023232075513)
    ·
      refine ⟨22881039073905767424056635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30508052098541023232075513 22881039073905767424056635)
      ·
        refine ⟨34321558610858651136084953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22881039073905767424056635 34321558610858651136084953)
        ·
          refine ⟨25741168958143988352063715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34321558610858651136084953 25741168958143988352063715)
          ·
            refine ⟨38611753437215982528095573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25741168958143988352063715 38611753437215982528095573)
            ·
              refine ⟨28280092849523424703195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 38611753437215982528095573 28280092849523424703195)
              ·
                rfl

theorem cell22_2230549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 12].length) (baseStart_2230549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230549 prefixEnd_2230549 := by exact prefixLift 2230549
  have htrace : WordTrace (prefixWord ++ tailWord_2230549) baseStart_2230549 baseEnd_2230549 := by
    simpa [prefixWord, tailWord_2230549, baseEnd_2230549] using wordTrace_append hprefix tailTrace_2230549
  have hstable : (prefixWord ++ tailWord_2230549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230549).length < 2 ^ (prefixWord ++ tailWord_2230549).sum := by decide
  have hdescent : baseEnd_2230549 < baseStart_2230549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230551 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 4, 4]
def baseStart_2230551 : Nat := 118140960795 + 2230551 * 2 ^ 59
def prefixEnd_2230551 : Nat := 4983230072969 + 3 ^ 40 * 2230551 * 2
def baseEnd_2230551 : Nat := 763563191578005128436259

theorem tailTrace_2230551 : CollatzResearch.WordTrace tailWord_2230551 prefixEnd_2230551 763563191578005128436259 := by
  unfold tailWord_2230551
  simp only [CollatzResearch.WordTrace]
  refine ⟨81354878542102149627107507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54236585694734766418071671 81354878542102149627107507)
  ·
    refine ⟨122032317813153224440661261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81354878542102149627107507 122032317813153224440661261)
    ·
      refine ⟨45762119179932459165247973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122032317813153224440661261 45762119179932459165247973)
      ·
        refine ⟨8580397346237336093483995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45762119179932459165247973 8580397346237336093483995)
        ·
          refine ⟨12870596019356004140225993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8580397346237336093483995 12870596019356004140225993)
          ·
            refine ⟨9652947014517003105169495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12870596019356004140225993 9652947014517003105169495)
            ·
              refine ⟨14479420521775504657754243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9652947014517003105169495 14479420521775504657754243)
              ·
                refine ⟨21719130782663256986631365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14479420521775504657754243 21719130782663256986631365)
                ·
                  refine ⟨4072337021749360684993381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21719130782663256986631365 4072337021749360684993381)
                  ·
                    refine ⟨763563191578005128436259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072337021749360684993381 763563191578005128436259)
                    ·
                      rfl

theorem cell22_2230551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_2230551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230551 prefixEnd_2230551 := by exact prefixLift 2230551
  have htrace : WordTrace (prefixWord ++ tailWord_2230551) baseStart_2230551 baseEnd_2230551 := by
    simpa [prefixWord, tailWord_2230551, baseEnd_2230551] using wordTrace_append hprefix tailTrace_2230551
  have hstable : (prefixWord ++ tailWord_2230551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230551).length < 2 ^ (prefixWord ++ tailWord_2230551).sum := by decide
  have hdescent : baseEnd_2230551 < baseStart_2230551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230574 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2230574 : Nat := 118140960795 + 2230574 * 2 ^ 59
def prefixEnd_2230574 : Nat := 4983230072969 + 3 ^ 40 * 2230574 * 2
def baseEnd_2230574 : Nat := 763571064948040735111189

theorem tailTrace_2230574 : CollatzResearch.WordTrace tailWord_2230574 prefixEnd_2230574 763571064948040735111189 := by
  unfold tailWord_2230574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10169464677627353069399347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54237144947345883036796517 10169464677627353069399347)
  ·
    refine ⟨15254197016441029604099021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10169464677627353069399347 15254197016441029604099021)
    ·
      refine ⟨5720323881165386101537133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15254197016441029604099021 5720323881165386101537133)
      ·
        refine ⟨2145121455437019788076425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5720323881165386101537133 2145121455437019788076425)
        ·
          refine ⟨1608841091577764841057319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2145121455437019788076425 1608841091577764841057319)
          ·
            refine ⟨2413261637366647261585979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608841091577764841057319 2413261637366647261585979)
            ·
              refine ⟨3619892456049970892378969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413261637366647261585979 3619892456049970892378969)
              ·
                refine ⟨2714919342037478169284227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619892456049970892378969 2714919342037478169284227)
                ·
                  refine ⟨4072379013056217253926341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714919342037478169284227 4072379013056217253926341)
                  ·
                    refine ⟨763571064948040735111189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072379013056217253926341 763571064948040735111189)
                    ·
                      rfl

theorem cell22_2230574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2230574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230574 prefixEnd_2230574 := by exact prefixLift 2230574
  have htrace : WordTrace (prefixWord ++ tailWord_2230574) baseStart_2230574 baseEnd_2230574 := by
    simpa [prefixWord, tailWord_2230574, baseEnd_2230574] using wordTrace_append hprefix tailTrace_2230574
  have hstable : (prefixWord ++ tailWord_2230574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230574).length < 2 ^ (prefixWord ++ tailWord_2230574).sum := by decide
  have hdescent : baseEnd_2230574 < baseStart_2230574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230615 : List Nat := [1, 1, 3, 2, 3, 1, 3, 4, 1, 3]
def baseStart_2230615 : Nat := 118140960795 + 2230615 * 2 ^ 59
def prefixEnd_2230615 : Nat := 4983230072969 + 3 ^ 40 * 2230615 * 2
def baseEnd_2230615 : Nat := 763585100085930294836063

theorem tailTrace_2230615 : CollatzResearch.WordTrace tailWord_2230615 prefixEnd_2230615 763585100085930294836063 := by
  unfold tailWord_2230615
  simp only [CollatzResearch.WordTrace]
  refine ⟨81357212813870288557437299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54238141875913525704958199 81357212813870288557437299)
  ·
    refine ⟨122035819220805432836155949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81357212813870288557437299 122035819220805432836155949)
    ·
      refine ⟨45763432207802037313558481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122035819220805432836155949 45763432207802037313558481)
      ·
        refine ⟨34322574155851527985168861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45763432207802037313558481 34322574155851527985168861)
        ·
          refine ⟨12870965308444322994438323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34322574155851527985168861 12870965308444322994438323)
          ·
            refine ⟨19306447962666484491657485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12870965308444322994438323 19306447962666484491657485)
            ·
              refine ⟨7239917985999931684371557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19306447962666484491657485 7239917985999931684371557)
              ·
                refine ⟨1357484622374987190819667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7239917985999931684371557 1357484622374987190819667)
                ·
                  refine ⟨2036226933562480786229501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357484622374987190819667 2036226933562480786229501)
                  ·
                    refine ⟨763585100085930294836063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036226933562480786229501 763585100085930294836063)
                    ·
                      rfl

theorem cell22_2230615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_2230615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230615 prefixEnd_2230615 := by exact prefixLift 2230615
  have htrace : WordTrace (prefixWord ++ tailWord_2230615) baseStart_2230615 baseEnd_2230615 := by
    simpa [prefixWord, tailWord_2230615, baseEnd_2230615] using wordTrace_append hprefix tailTrace_2230615
  have hstable : (prefixWord ++ tailWord_2230615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230615).length < 2 ^ (prefixWord ++ tailWord_2230615).sum := by decide
  have hdescent : baseEnd_2230615 < baseStart_2230615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230688 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_2230688 : Nat := 118140960795 + 2230688 * 2 ^ 59
def prefixEnd_2230688 : Nat := 4983230072969 + 3 ^ 40 * 2230688 * 2
def baseEnd_2230688 : Nat := 763610089477782437760839

theorem tailTrace_2230688 : CollatzResearch.WordTrace tailWord_2230688 prefixEnd_2230688 763610089477782437760839 := by
  unfold tailWord_2230688
  simp only [CollatzResearch.WordTrace]
  refine ⟨40679937671302911012422359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54239916895070548016563145 40679937671302911012422359)
  ·
    refine ⟨61019906506954366518633539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40679937671302911012422359 61019906506954366518633539)
    ·
      refine ⟨91529859760431549777950309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61019906506954366518633539 91529859760431549777950309)
      ·
        refine ⟨17161848705080915583365683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91529859760431549777950309 17161848705080915583365683)
        ·
          refine ⟨25742773057621373375048525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17161848705080915583365683 25742773057621373375048525)
          ·
            refine ⟨9653539896608015015643197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25742773057621373375048525 9653539896608015015643197)
            ·
              refine ⟨3620077461228005630866199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9653539896608015015643197 3620077461228005630866199)
              ·
                refine ⟨5430116191842008446299299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620077461228005630866199 5430116191842008446299299)
                ·
                  refine ⟨8145174287763012669448949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5430116191842008446299299 8145174287763012669448949)
                  ·
                    refine ⟨763610089477782437760839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8145174287763012669448949 763610089477782437760839)
                    ·
                      rfl

theorem cell22_2230688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_2230688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230688 prefixEnd_2230688 := by exact prefixLift 2230688
  have htrace : WordTrace (prefixWord ++ tailWord_2230688) baseStart_2230688 baseEnd_2230688 := by
    simpa [prefixWord, tailWord_2230688, baseEnd_2230688] using wordTrace_append hprefix tailTrace_2230688
  have hstable : (prefixWord ++ tailWord_2230688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230688).length < 2 ^ (prefixWord ++ tailWord_2230688).sum := by decide
  have hdescent : baseEnd_2230688 < baseStart_2230688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230724 : List Nat := [2, 3, 3, 2, 2, 1, 3, 2, 4]
def baseStart_2230724 : Nat := 118140960795 + 2230724 * 2 ^ 59
def prefixEnd_2230724 : Nat := 4983230072969 + 3 ^ 40 * 2230724 * 2
def baseEnd_2230724 : Nat := 254540804337830114620243

theorem tailTrace_2230724 : CollatzResearch.WordTrace tailWord_2230724 prefixEnd_2230724 254540804337830114620243 := by
  unfold tailWord_2230724
  simp only [CollatzResearch.WordTrace]
  refine ⟨40680594185237700086577613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54240792246983600115436817 40680594185237700086577613)
  ·
    refine ⟨15255222819464137532466605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40680594185237700086577613 15255222819464137532466605)
    ·
      refine ⟨5720708557299051574674977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15255222819464137532466605 5720708557299051574674977)
      ·
        refine ⟨4290531417974288681006233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5720708557299051574674977 4290531417974288681006233)
        ·
          refine ⟨3217898563480716510754675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4290531417974288681006233 3217898563480716510754675)
          ·
            refine ⟨4826847845221074766132013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217898563480716510754675 4826847845221074766132013)
            ·
              refine ⟨1810067941957903037299505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4826847845221074766132013 1810067941957903037299505)
              ·
                refine ⟨1357550956468427277974629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1810067941957903037299505 1357550956468427277974629)
                ·
                  refine ⟨254540804337830114620243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357550956468427277974629 254540804337830114620243)
                  ·
                    rfl

theorem cell22_2230724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_2230724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230724 prefixEnd_2230724 := by exact prefixLift 2230724
  have htrace : WordTrace (prefixWord ++ tailWord_2230724) baseStart_2230724 baseEnd_2230724 := by
    simpa [prefixWord, tailWord_2230724, baseEnd_2230724] using wordTrace_append hprefix tailTrace_2230724
  have hstable : (prefixWord ++ tailWord_2230724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230724).length < 2 ^ (prefixWord ++ tailWord_2230724).sum := by decide
  have hdescent : baseEnd_2230724 < baseStart_2230724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230731 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 2, 6]
def baseStart_2230731 : Nat := 118140960795 + 2230731 * 2 ^ 59
def prefixEnd_2230731 : Nat := 4983230072969 + 3 ^ 40 * 2230731 * 2
def baseEnd_2230731 : Nat := 763624809256544658935707

theorem tailTrace_2230731 : CollatzResearch.WordTrace tailWord_2230731 prefixEnd_2230731 763624809256544658935707 := by
  unfold tailWord_2230731
  simp only [CollatzResearch.WordTrace]
  refine ⟨81361443681450040368660047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54240962454300026912440031 81361443681450040368660047)
  ·
    refine ⟨122042165522175060552990071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81361443681450040368660047 122042165522175060552990071)
    ·
      refine ⟨183063248283262590829485107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122042165522175060552990071 183063248283262590829485107)
      ·
        refine ⟨274594872424893886244227661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183063248283262590829485107 274594872424893886244227661)
        ·
          refine ⟨102973077159335207341585373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274594872424893886244227661 102973077159335207341585373)
          ·
            refine ⟨38614903934750702753094515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102973077159335207341585373 38614903934750702753094515)
            ·
              refine ⟨57922355902126054129641773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38614903934750702753094515 57922355902126054129641773)
              ·
                refine ⟨21720883463297270298615665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57922355902126054129641773 21720883463297270298615665)
                ·
                  refine ⟨16290662597472952723961749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21720883463297270298615665 16290662597472952723961749)
                  ·
                    refine ⟨763624809256544658935707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16290662597472952723961749 763624809256544658935707)
                    ·
                      rfl

theorem cell22_2230731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_2230731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230731 prefixEnd_2230731 := by exact prefixLift 2230731
  have htrace : WordTrace (prefixWord ++ tailWord_2230731) baseStart_2230731 baseEnd_2230731 := by
    simpa [prefixWord, tailWord_2230731, baseEnd_2230731] using wordTrace_append hprefix tailTrace_2230731
  have hstable : (prefixWord ++ tailWord_2230731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230731).length < 2 ^ (prefixWord ++ tailWord_2230731).sum := by decide
  have hdescent : baseEnd_2230731 < baseStart_2230731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230754 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2230754 : Nat := 118140960795 + 2230754 * 2 ^ 59
def prefixEnd_2230754 : Nat := 4983230072969 + 3 ^ 40 * 2230754 * 2
def baseEnd_2230754 : Nat := 763632682626580265610637

theorem tailTrace_2230754 : CollatzResearch.WordTrace tailWord_2230754 prefixEnd_2230754 763632682626580265610637 := by
  unfold tailWord_2230754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20340570640091678824186829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54241521706911143531164877 20340570640091678824186829)
  ·
    refine ⟨7627713990034379559070061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20340570640091678824186829 7627713990034379559070061)
    ·
      refine ⟨2860392746262892334651273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7627713990034379559070061 2860392746262892334651273)
      ·
        refine ⟨2145294559697169250988455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2860392746262892334651273 2145294559697169250988455)
        ·
          refine ⟨3217941839545753876482683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145294559697169250988455 3217941839545753876482683)
          ·
            refine ⟨4826912759318630814724025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217941839545753876482683 4826912759318630814724025)
            ·
              refine ⟨3620184569488973111043019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4826912759318630814724025 3620184569488973111043019)
              ·
                refine ⟨5430276854233459666564529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620184569488973111043019 5430276854233459666564529)
                ·
                  refine ⟨4072707640675094749923397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5430276854233459666564529 4072707640675094749923397)
                  ·
                    refine ⟨763632682626580265610637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072707640675094749923397 763632682626580265610637)
                    ·
                      rfl

theorem cell22_2230754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2230754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230754 prefixEnd_2230754 := by exact prefixLift 2230754
  have htrace : WordTrace (prefixWord ++ tailWord_2230754) baseStart_2230754 baseEnd_2230754 := by
    simpa [prefixWord, tailWord_2230754, baseEnd_2230754] using wordTrace_append hprefix tailTrace_2230754
  have hstable : (prefixWord ++ tailWord_2230754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230754).length < 2 ^ (prefixWord ++ tailWord_2230754).sum := by decide
  have hdescent : baseEnd_2230754 < baseStart_2230754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230761 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_2230761 : Nat := 118140960795 + 2230761 * 2 ^ 59
def prefixEnd_2230761 : Nat := 4983230072969 + 3 ^ 40 * 2230761 * 2
def baseEnd_2230761 : Nat := 763635078869634580685615

theorem tailTrace_2230761 : CollatzResearch.WordTrace tailWord_2230761 prefixEnd_2230761 763635078869634580685615 := by
  unfold tailWord_2230761
  simp only [CollatzResearch.WordTrace]
  refine ⟨81362537871341355492252137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54241691914227570328168091 81362537871341355492252137)
  ·
    refine ⟨61021903403506016619189103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81362537871341355492252137 61021903403506016619189103)
    ·
      refine ⟨91532855105259024928783655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61021903403506016619189103 91532855105259024928783655)
      ·
        refine ⟨137299282657888537393175483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91532855105259024928783655 137299282657888537393175483)
        ·
          refine ⟨205948923986832806089763225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137299282657888537393175483 205948923986832806089763225)
          ·
            refine ⟨154461692990124604567322419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205948923986832806089763225 154461692990124604567322419)
            ·
              refine ⟨231692539485186906850983629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154461692990124604567322419 231692539485186906850983629)
              ·
                refine ⟨86884702306945090069118861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231692539485186906850983629 86884702306945090069118861)
                ·
                  refine ⟨32581763365104408775919573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86884702306945090069118861 32581763365104408775919573)
                  ·
                    refine ⟨763635078869634580685615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32581763365104408775919573 763635078869634580685615)
                    ·
                      rfl

theorem cell22_2230761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_2230761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230761 prefixEnd_2230761 := by exact prefixLift 2230761
  have htrace : WordTrace (prefixWord ++ tailWord_2230761) baseStart_2230761 baseEnd_2230761 := by
    simpa [prefixWord, tailWord_2230761, baseEnd_2230761] using wordTrace_append hprefix tailTrace_2230761
  have hstable : (prefixWord ++ tailWord_2230761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230761).length < 2 ^ (prefixWord ++ tailWord_2230761).sum := by decide
  have hdescent : baseEnd_2230761 < baseStart_2230761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230808 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 8]
def baseStart_2230808 : Nat := 118140960795 + 2230808 * 2 ^ 59
def prefixEnd_2230808 : Nat := 4983230072969 + 3 ^ 40 * 2230808 * 2
def baseEnd_2230808 : Nat := 254550389310047374920157

theorem tailTrace_2230808 : CollatzResearch.WordTrace tailWord_2230808 prefixEnd_2230808 254550389310047374920157 := by
  unfold tailWord_2230808
  simp only [CollatzResearch.WordTrace]
  refine ⟨40682126051085541259606539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54242834734780721679475385 40682126051085541259606539)
  ·
    refine ⟨61023189076628311889409809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40682126051085541259606539 61023189076628311889409809)
    ·
      refine ⟨45767391807471233917057357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61023189076628311889409809 45767391807471233917057357)
      ·
        refine ⟨17162771927801712718896509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45767391807471233917057357 17162771927801712718896509)
        ·
          refine ⟨6436039472925642269586191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17162771927801712718896509 6436039472925642269586191)
          ·
            refine ⟨9654059209388463404379287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6436039472925642269586191 9654059209388463404379287)
            ·
              refine ⟨14481088814082695106568931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9654059209388463404379287 14481088814082695106568931)
              ·
                refine ⟨21721633221124042659853397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14481088814082695106568931 21721633221124042659853397)
                ·
                  refine ⟨254550389310047374920157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21721633221124042659853397 254550389310047374920157)
                  ·
                    rfl

theorem cell22_2230808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_2230808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230808 prefixEnd_2230808 := by exact prefixLift 2230808
  have htrace : WordTrace (prefixWord ++ tailWord_2230808) baseStart_2230808 baseEnd_2230808 := by
    simpa [prefixWord, tailWord_2230808, baseEnd_2230808] using wordTrace_append hprefix tailTrace_2230808
  have hstable : (prefixWord ++ tailWord_2230808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230808).length < 2 ^ (prefixWord ++ tailWord_2230808).sum := by decide
  have hdescent : baseEnd_2230808 < baseStart_2230808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230840 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 4, 3]
def baseStart_2230840 : Nat := 118140960795 + 2230840 * 2 ^ 59
def prefixEnd_2230840 : Nat := 4983230072969 + 3 ^ 40 * 2230840 * 2
def baseEnd_2230840 : Nat := 763662122184104707960373

theorem tailTrace_2230840 : CollatzResearch.WordTrace tailWord_2230840 prefixEnd_2230840 763662122184104707960373 := by
  unfold tailWord_2230840
  simp only [CollatzResearch.WordTrace]
  refine ⟨40682709619027575992188987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54243612825370101322918649 40682709619027575992188987)
  ·
    refine ⟨61024064428541363988283481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40682709619027575992188987 61024064428541363988283481)
    ·
      refine ⟨45768048321406022991212611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61024064428541363988283481 45768048321406022991212611)
      ·
        refine ⟨68652072482109034486818917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45768048321406022991212611 68652072482109034486818917)
        ·
          refine ⟨12872263590395443966278547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68652072482109034486818917 12872263590395443966278547)
          ·
            refine ⟨19308395385593165949417821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12872263590395443966278547 19308395385593165949417821)
            ·
              refine ⟨7240648269597437231031683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19308395385593165949417821 7240648269597437231031683)
              ·
                refine ⟨10860972404396155846547525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7240648269597437231031683 10860972404396155846547525)
                ·
                  refine ⟨2036432325824279221227661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10860972404396155846547525 2036432325824279221227661)
                  ·
                    refine ⟨763662122184104707960373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036432325824279221227661 763662122184104707960373)
                    ·
                      rfl

theorem cell22_2230840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_2230840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230840 prefixEnd_2230840 := by exact prefixLift 2230840
  have htrace : WordTrace (prefixWord ++ tailWord_2230840) baseStart_2230840 baseEnd_2230840 := by
    simpa [prefixWord, tailWord_2230840, baseEnd_2230840] using wordTrace_append hprefix tailTrace_2230840
  have hstable : (prefixWord ++ tailWord_2230840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230840).length < 2 ^ (prefixWord ++ tailWord_2230840).sum := by decide
  have hdescent : baseEnd_2230840 < baseStart_2230840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230876 : List Nat := [2, 2, 4, 1, 4, 1, 1, 3, 4]
def baseStart_2230876 : Nat := 118140960795 + 2230876 * 2 ^ 59
def prefixEnd_2230876 : Nat := 4983230072969 + 3 ^ 40 * 2230876 * 2
def baseEnd_2230876 : Nat := 254558148573270871353421

theorem tailTrace_2230876 : CollatzResearch.WordTrace tailWord_2230876 prefixEnd_2230876 254558148573270871353421 := by
  unfold tailWord_2230876
  simp only [CollatzResearch.WordTrace]
  refine ⟨40683366132962365066344241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54244488177283153421792321 40683366132962365066344241)
  ·
    refine ⟨30512524599721773799758181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40683366132962365066344241 30512524599721773799758181)
    ·
      refine ⟨5721098362447832587454659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30512524599721773799758181 5721098362447832587454659)
      ·
        refine ⟨8581647543671748881181989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5721098362447832587454659 8581647543671748881181989)
        ·
          refine ⟨1609058914438452915221623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8581647543671748881181989 1609058914438452915221623)
          ·
            refine ⟨2413588371657679372832435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609058914438452915221623 2413588371657679372832435)
            ·
              refine ⟨3620382557486519059248653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413588371657679372832435 3620382557486519059248653)
              ·
                refine ⟨1357643459057444647218245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3620382557486519059248653 1357643459057444647218245)
                ·
                  refine ⟨254558148573270871353421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357643459057444647218245 254558148573270871353421)
                  ·
                    rfl

theorem cell22_2230876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_2230876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230876 prefixEnd_2230876 := by exact prefixLift 2230876
  have htrace : WordTrace (prefixWord ++ tailWord_2230876) baseStart_2230876 baseEnd_2230876 := by
    simpa [prefixWord, tailWord_2230876, baseEnd_2230876] using wordTrace_append hprefix tailTrace_2230876
  have hstable : (prefixWord ++ tailWord_2230876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230876).length < 2 ^ (prefixWord ++ tailWord_2230876).sum := by decide
  have hdescent : baseEnd_2230876 < baseStart_2230876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2230975 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 1, 5]
def baseStart_2230975 : Nat := 118140960795 + 2230975 * 2 ^ 59
def prefixEnd_2230975 : Nat := 4983230072969 + 3 ^ 40 * 2230975 * 2
def baseEnd_2230975 : Nat := 763708335443009355834959

theorem tailTrace_2230975 : CollatzResearch.WordTrace tailWord_2230975 prefixEnd_2230975 763708335443009355834959 := by
  unfold tailWord_2230975
  simp only [CollatzResearch.WordTrace]
  refine ⟨81370343092566070040542379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54246895395044046693694919 81370343092566070040542379)
  ·
    refine ⟨122055514638849105060813569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81370343092566070040542379 122055514638849105060813569)
    ·
      refine ⟨91541635979136828795610177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122055514638849105060813569 91541635979136828795610177)
      ·
        refine ⟨68656226984352621596707633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91541635979136828795610177 68656226984352621596707633)
        ·
          refine ⟨51492170238264466197530725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68656226984352621596707633 51492170238264466197530725)
          ·
            refine ⟨9654781919674587412037011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51492170238264466197530725 9654781919674587412037011)
            ·
              refine ⟨14482172879511881118055517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9654781919674587412037011 14482172879511881118055517)
              ·
                refine ⟨5430814829816955419270819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14482172879511881118055517 5430814829816955419270819)
                ·
                  refine ⟨8146222244725433128906229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5430814829816955419270819 8146222244725433128906229)
                  ·
                    refine ⟨763708335443009355834959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8146222244725433128906229 763708335443009355834959)
                    ·
                      rfl

theorem cell22_2230975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_2230975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2230975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2230975 prefixEnd_2230975 := by exact prefixLift 2230975
  have htrace : WordTrace (prefixWord ++ tailWord_2230975) baseStart_2230975 baseEnd_2230975 := by
    simpa [prefixWord, tailWord_2230975, baseEnd_2230975] using wordTrace_append hprefix tailTrace_2230975
  have hstable : (prefixWord ++ tailWord_2230975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2230975).length < 2 ^ (prefixWord ++ tailWord_2230975).sum := by decide
  have hdescent : baseEnd_2230975 < baseStart_2230975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2230975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231009 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 2, 3]
def baseStart_2231009 : Nat := 118140960795 + 2231009 * 2 ^ 59
def prefixEnd_2231009 : Nat := 4983230072969 + 3 ^ 40 * 2231009 * 2
def baseEnd_2231009 : Nat := 763719974337844600484855

theorem tailTrace_2231009 : CollatzResearch.WordTrace tailWord_2231009 prefixEnd_2231009 763719974337844600484855 := by
  unfold tailWord_2231009
  simp only [CollatzResearch.WordTrace]
  refine ⟨81371583174442893847280081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54247722116295262564853387 81371583174442893847280081)
  ·
    refine ⟨61028687380832170385460061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81371583174442893847280081 61028687380832170385460061)
    ·
      refine ⟨22885757767812063894547523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61028687380832170385460061 22885757767812063894547523)
      ·
        refine ⟨34328636651718095841821285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22885757767812063894547523 34328636651718095841821285)
        ·
          refine ⟨6436619372197142970341491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34328636651718095841821285 6436619372197142970341491)
          ·
            refine ⟨9654929058295714455512237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6436619372197142970341491 9654929058295714455512237)
            ·
              refine ⟨3620598396860892920817089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9654929058295714455512237 3620598396860892920817089)
              ·
                refine ⟨2715448797645669690612817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620598396860892920817089 2715448797645669690612817)
                ·
                  refine ⟨2036586598234252267959613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2715448797645669690612817 2036586598234252267959613)
                  ·
                    refine ⟨763719974337844600484855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036586598234252267959613 763719974337844600484855)
                    ·
                      rfl

theorem cell22_2231009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_2231009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231009 prefixEnd_2231009 := by exact prefixLift 2231009
  have htrace : WordTrace (prefixWord ++ tailWord_2231009) baseStart_2231009 baseEnd_2231009 := by
    simpa [prefixWord, tailWord_2231009, baseEnd_2231009] using wordTrace_append hprefix tailTrace_2231009
  have hstable : (prefixWord ++ tailWord_2231009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231009).length < 2 ^ (prefixWord ++ tailWord_2231009).sum := by decide
  have hdescent : baseEnd_2231009 < baseStart_2231009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231026 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_2231026 : Nat := 118140960795 + 2231026 * 2 ^ 59
def prefixEnd_2231026 : Nat := 4983230072969 + 3 ^ 40 * 2231026 * 2
def baseEnd_2231026 : Nat := 763725793785262222809803

theorem tailTrace_2231026 : CollatzResearch.WordTrace tailWord_2231026 prefixEnd_2231026 763725793785262222809803 := by
  unfold tailWord_2231026
  simp only [CollatzResearch.WordTrace]
  refine ⟨20343050803845326437662233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54248135476920870500432621 20343050803845326437662233)
  ·
    refine ⟨15257288102883994828246675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20343050803845326437662233 15257288102883994828246675)
    ·
      refine ⟨22885932154325992242370013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15257288102883994828246675 22885932154325992242370013)
      ·
        refine ⟨8582224557872247090888755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22885932154325992242370013 8582224557872247090888755)
        ·
          refine ⟨12873336836808370636333133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8582224557872247090888755 12873336836808370636333133)
          ·
            refine ⟨4827501313803138988624925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12873336836808370636333133 4827501313803138988624925)
            ·
              refine ⟨1810312992676177120734347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4827501313803138988624925 1810312992676177120734347)
              ·
                refine ⟨2715469489014265681101521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810312992676177120734347 2715469489014265681101521)
                ·
                  refine ⟨2036602116760699260826141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2715469489014265681101521 2036602116760699260826141)
                  ·
                    refine ⟨763725793785262222809803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036602116760699260826141 763725793785262222809803)
                    ·
                      rfl

theorem cell22_2231026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_2231026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231026 prefixEnd_2231026 := by exact prefixLift 2231026
  have htrace : WordTrace (prefixWord ++ tailWord_2231026) baseStart_2231026 baseEnd_2231026 := by
    simpa [prefixWord, tailWord_2231026, baseEnd_2231026] using wordTrace_append hprefix tailTrace_2231026
  have hstable : (prefixWord ++ tailWord_2231026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231026).length < 2 ^ (prefixWord ++ tailWord_2231026).sum := by decide
  have hdescent : baseEnd_2231026 < baseStart_2231026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231037 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_2231037 : Nat := 118140960795 + 2231037 * 2 ^ 59
def prefixEnd_2231037 : Nat := 4983230072969 + 3 ^ 40 * 2231037 * 2
def baseEnd_2231037 : Nat := 763729559310061860784769

theorem tailTrace_2231037 : CollatzResearch.WordTrace tailWord_2231037 prefixEnd_2231037 763729559310061860784769 := by
  unfold tailWord_2231037
  simp only [CollatzResearch.WordTrace]
  refine ⟨81372604418341454629299365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54248402945560969752866243 81372604418341454629299365)
  ·
    refine ⟨15257363328439022742993631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81372604418341454629299365 15257363328439022742993631)
    ·
      refine ⟨22886044992658534114490447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15257363328439022742993631 22886044992658534114490447)
      ·
        refine ⟨34329067488987801171735671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22886044992658534114490447 34329067488987801171735671)
        ·
          refine ⟨51493601233481701757603507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34329067488987801171735671 51493601233481701757603507)
          ·
            refine ⟨77240401850222552636405261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51493601233481701757603507 77240401850222552636405261)
            ·
              refine ⟨28965150693833457238651973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77240401850222552636405261 28965150693833457238651973)
              ·
                refine ⟨5430965755093773232247245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28965150693833457238651973 5430965755093773232247245)
                ·
                  refine ⟨2036612158160164962092717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5430965755093773232247245 2036612158160164962092717)
                  ·
                    refine ⟨763729559310061860784769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2036612158160164962092717 763729559310061860784769)
                    ·
                      rfl

theorem cell22_2231037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_2231037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231037 prefixEnd_2231037 := by exact prefixLift 2231037
  have htrace : WordTrace (prefixWord ++ tailWord_2231037) baseStart_2231037 baseEnd_2231037 := by
    simpa [prefixWord, tailWord_2231037, baseEnd_2231037] using wordTrace_append hprefix tailTrace_2231037
  have hstable : (prefixWord ++ tailWord_2231037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231037).length < 2 ^ (prefixWord ++ tailWord_2231037).sum := by decide
  have hdescent : baseEnd_2231037 < baseStart_2231037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231050 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_2231050 : Nat := 118140960795 + 2231050 * 2 ^ 59
def prefixEnd_2231050 : Nat := 4983230072969 + 3 ^ 40 * 2231050 * 2
def baseEnd_2231050 : Nat := 254578003158578053403243

theorem tailTrace_2231050 : CollatzResearch.WordTrace tailWord_2231050 prefixEnd_2231050 254578003158578053403243 := by
  unfold tailWord_2231050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20343269641823589462380651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54248719044862905233015069 20343269641823589462380651)
  ·
    refine ⟨30514904462735384193570977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20343269641823589462380651 30514904462735384193570977)
    ·
      refine ⟨22886178347051538145178233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30514904462735384193570977 22886178347051538145178233)
      ·
        refine ⟨17164633760288653608883675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22886178347051538145178233 17164633760288653608883675)
        ·
          refine ⟨25746950640432980413325513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17164633760288653608883675 25746950640432980413325513)
          ·
            refine ⟨19310212980324735309994135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25746950640432980413325513 19310212980324735309994135)
            ·
              refine ⟨28965319470487102964991203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19310212980324735309994135 28965319470487102964991203)
              ·
                refine ⟨43447979205730654447486805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28965319470487102964991203 43447979205730654447486805)
                ·
                  refine ⟨254578003158578053403243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43447979205730654447486805 254578003158578053403243)
                  ·
                    rfl

theorem cell22_2231050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_2231050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231050 prefixEnd_2231050 := by exact prefixLift 2231050
  have htrace : WordTrace (prefixWord ++ tailWord_2231050) baseStart_2231050 baseEnd_2231050 := by
    simpa [prefixWord, tailWord_2231050, baseEnd_2231050] using wordTrace_append hprefix tailTrace_2231050
  have hstable : (prefixWord ++ tailWord_2231050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231050).length < 2 ^ (prefixWord ++ tailWord_2231050).sum := by decide
  have hdescent : baseEnd_2231050 < baseStart_2231050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231065 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_2231065 : Nat := 118140960795 + 2231065 * 2 ^ 59
def prefixEnd_2231065 : Nat := 4983230072969 + 3 ^ 40 * 2231065 * 2
def baseEnd_2231065 : Nat := 763739144282279121084683

theorem tailTrace_2231065 : CollatzResearch.WordTrace tailWord_2231065 prefixEnd_2231065 763739144282279121084683 := by
  unfold tailWord_2231065
  simp only [CollatzResearch.WordTrace]
  refine ⟨81373625662240015411318649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54249083774826676940879099 81373625662240015411318649)
  ·
    refine ⟨61030219246680011558488987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81373625662240015411318649 61030219246680011558488987)
    ·
      refine ⟨91545328870020017337733481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61030219246680011558488987 91545328870020017337733481)
      ·
        refine ⟨68658996652515013003300111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91545328870020017337733481 68658996652515013003300111)
        ·
          refine ⟨102988494978772519504950167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68658996652515013003300111 102988494978772519504950167)
          ·
            refine ⟨154482742468158779257425251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102988494978772519504950167 154482742468158779257425251)
            ·
              refine ⟨231724113702238168886137877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154482742468158779257425251 231724113702238168886137877)
              ·
                refine ⟨10862067829792414166537713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231724113702238168886137877 10862067829792414166537713)
                ·
                  refine ⟨8146550872344310624903285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10862067829792414166537713 8146550872344310624903285)
                  ·
                    refine ⟨763739144282279121084683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8146550872344310624903285 763739144282279121084683)
                    ·
                      rfl

theorem cell22_2231065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_2231065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231065 prefixEnd_2231065 := by exact prefixLift 2231065
  have htrace : WordTrace (prefixWord ++ tailWord_2231065) baseStart_2231065 baseEnd_2231065 := by
    simpa [prefixWord, tailWord_2231065, baseEnd_2231065] using wordTrace_append hprefix tailTrace_2231065
  have hstable : (prefixWord ++ tailWord_2231065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231065).length < 2 ^ (prefixWord ++ tailWord_2231065).sum := by decide
  have hdescent : baseEnd_2231065 < baseStart_2231065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231095 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 8]
def baseStart_2231095 : Nat := 118140960795 + 2231095 * 2 ^ 59
def prefixEnd_2231095 : Nat := 4983230072969 + 3 ^ 40 * 2231095 * 2
def baseEnd_2231095 : Nat := 254583137965123014278197

theorem tailTrace_2231095 : CollatzResearch.WordTrace tailWord_2231095 prefixEnd_2231095 254583137965123014278197 := by
  unfold tailWord_2231095
  simp only [CollatzResearch.WordTrace]
  refine ⟨81374719852131330534910739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54249813234754220356607159 81374719852131330534910739)
  ·
    refine ⟨122062079778196995802366109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81374719852131330534910739 122062079778196995802366109)
    ·
      refine ⟨45773279916823873425887291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122062079778196995802366109 45773279916823873425887291)
      ·
        refine ⟨68659919875235810138830937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45773279916823873425887291 68659919875235810138830937)
        ·
          refine ⟨51494939906426857604123203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68659919875235810138830937 51494939906426857604123203)
          ·
            refine ⟨77242409859640286406184805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51494939906426857604123203 77242409859640286406184805)
            ·
              refine ⟨14482951848682553701159651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77242409859640286406184805 14482951848682553701159651)
              ·
                refine ⟨21724427773023830551739477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14482951848682553701159651 21724427773023830551739477)
                ·
                  refine ⟨254583137965123014278197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21724427773023830551739477 254583137965123014278197)
                  ·
                    rfl

theorem cell22_2231095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 8].length) (baseStart_2231095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231095 prefixEnd_2231095 := by exact prefixLift 2231095
  have htrace : WordTrace (prefixWord ++ tailWord_2231095) baseStart_2231095 baseEnd_2231095 := by
    simpa [prefixWord, tailWord_2231095, baseEnd_2231095] using wordTrace_append hprefix tailTrace_2231095
  have hstable : (prefixWord ++ tailWord_2231095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231095).length < 2 ^ (prefixWord ++ tailWord_2231095).sum := by decide
  have hdescent : baseEnd_2231095 < baseStart_2231095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231129 : List Nat := [1, 2, 1, 2, 2, 5, 1, 4, 4]
def baseStart_2231129 : Nat := 118140960795 + 2231129 * 2 ^ 59
def prefixEnd_2231129 : Nat := 4983230072969 + 3 ^ 40 * 2231129 * 2
def baseEnd_2231129 : Nat := 254587017596734762494829

theorem tailTrace_2231129 : CollatzResearch.WordTrace tailWord_2231129 prefixEnd_2231129 254587017596734762494829 := by
  unfold tailWord_2231129
  simp only [CollatzResearch.WordTrace]
  refine ⟨81375959934008154341648441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54250639956005436227765627 81375959934008154341648441)
  ·
    refine ⟨61031969950506115756236331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81375959934008154341648441 61031969950506115756236331)
    ·
      refine ⟨91547954925759173634354497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61031969950506115756236331 91547954925759173634354497)
      ·
        refine ⟨68660966194319380225765873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91547954925759173634354497 68660966194319380225765873)
        ·
          refine ⟨51495724645739535169324405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68660966194319380225765873 51495724645739535169324405)
          ·
            refine ⟨4827724185538081422124163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51495724645739535169324405 4827724185538081422124163)
            ·
              refine ⟨7241586278307122133186245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4827724185538081422124163 7241586278307122133186245)
              ·
                refine ⟨1357797427182585399972421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7241586278307122133186245 1357797427182585399972421)
                ·
                  refine ⟨254587017596734762494829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357797427182585399972421 254587017596734762494829)
                  ·
                    rfl

theorem cell22_2231129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_2231129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231129 prefixEnd_2231129 := by exact prefixLift 2231129
  have htrace : WordTrace (prefixWord ++ tailWord_2231129) baseStart_2231129 baseEnd_2231129 := by
    simpa [prefixWord, tailWord_2231129, baseEnd_2231129] using wordTrace_append hprefix tailTrace_2231129
  have hstable : (prefixWord ++ tailWord_2231129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231129).length < 2 ^ (prefixWord ++ tailWord_2231129).sum := by decide
  have hdescent : baseEnd_2231129 < baseStart_2231129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2231144 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2231144 : Nat := 118140960795 + 2231144 * 2 ^ 59
def prefixEnd_2231144 : Nat := 4983230072969 + 3 ^ 40 * 2231144 * 2
def baseEnd_2231144 : Nat := 763766187596749248359441

theorem tailTrace_2231144 : CollatzResearch.WordTrace tailWord_2231144 prefixEnd_2231144 763766187596749248359441 := by
  unfold tailWord_2231144
  simp only [CollatzResearch.WordTrace]
  refine ⟨40688253514476905951722243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54251004685969207935629657 40688253514476905951722243)
  ·
    refine ⟨61032380271715358927583365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40688253514476905951722243 61032380271715358927583365)
    ·
      refine ⟨11443571300946629798921881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61032380271715358927583365 11443571300946629798921881)
      ·
        refine ⟨8582678475709972349191411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11443571300946629798921881 8582678475709972349191411)
        ·
          refine ⟨12874017713564958523787117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8582678475709972349191411 12874017713564958523787117)
          ·
            refine ⟨4827756642586859446420169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12874017713564958523787117 4827756642586859446420169)
            ·
              refine ⟨3620817481940144584815127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4827756642586859446420169 3620817481940144584815127)
              ·
                refine ⟨5431226222910216877222691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620817481940144584815127 5431226222910216877222691)
                ·
                  refine ⟨8146839334365325315834037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5431226222910216877222691 8146839334365325315834037)
                  ·
                    refine ⟨763766187596749248359441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8146839334365325315834037 763766187596749248359441)
                    ·
                      rfl

theorem cell22_2231144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2231144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2231144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2231144 prefixEnd_2231144 := by exact prefixLift 2231144
  have htrace : WordTrace (prefixWord ++ tailWord_2231144) baseStart_2231144 baseEnd_2231144 := by
    simpa [prefixWord, tailWord_2231144, baseEnd_2231144] using wordTrace_append hprefix tailTrace_2231144
  have hstable : (prefixWord ++ tailWord_2231144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2231144).length < 2 ^ (prefixWord ++ tailWord_2231144).sum := by decide
  have hdescent : baseEnd_2231144 < baseStart_2231144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2231144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
