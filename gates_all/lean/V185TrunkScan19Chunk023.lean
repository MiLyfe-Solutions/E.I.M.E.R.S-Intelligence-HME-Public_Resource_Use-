import V185TrunkScan19Chunk022

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_230926 : List Nat := [4, 1, 1, 2, 4, 2, 2, 3]
def baseStart_230926 : Nat := 118140960795 + 230926 * 2 ^ 59
def prefixEnd_230926 : Nat := 4983230072969 + 3 ^ 40 * 230926 * 2
def baseEnd_230926 : Nat := 70267279182381472392887

theorem tailTrace_230926 : CollatzResearch.WordTrace tailWord_230926 prefixEnd_230926 70267279182381472392887 := by
  unfold tailWord_230926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052820395175251983251079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5615042107601343910672421 1052820395175251983251079)
  ·
    refine ⟨1579230592762877974876619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1052820395175251983251079 1579230592762877974876619)
    ·
      refine ⟨2368845889144316962314929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579230592762877974876619 2368845889144316962314929)
      ·
        refine ⟨1776634416858237721736197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368845889144316962314929 1776634416858237721736197)
        ·
          refine ⟨333118953160919572825537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1776634416858237721736197 333118953160919572825537)
          ·
            refine ⟨249839214870689679619153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333118953160919572825537 249839214870689679619153)
            ·
              refine ⟨187379411153017259714365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249839214870689679619153 187379411153017259714365)
              ·
                refine ⟨70267279182381472392887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187379411153017259714365 70267279182381472392887)
                ·
                  rfl

theorem cell19_230926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_230926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230926 prefixEnd_230926 := by exact prefixLift 230926
  have htrace : WordTrace (prefixWord ++ tailWord_230926) baseStart_230926 baseEnd_230926 := by
    simpa [prefixWord, tailWord_230926, baseEnd_230926] using wordTrace_append hprefix tailTrace_230926
  have hstable : (prefixWord ++ tailWord_230926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230926).length < 2 ^ (prefixWord ++ tailWord_230926).sum := by decide
  have hdescent : baseEnd_230926 < baseStart_230926 := by decide
  rcases family_descends (prefixWord ++ tailWord_230926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230947 : List Nat := [1, 1, 1, 4, 6, 1, 5]
def baseStart_230947 : Nat := 118140960795 + 230947 * 2 ^ 59
def prefixEnd_230947 : Nat := 4983230072969 + 3 ^ 40 * 230947 * 2
def baseEnd_230947 : Nat := 23424556387953215308721

theorem tailTrace_230947 : CollatzResearch.WordTrace tailWord_230947 prefixEnd_230947 23424556387953215308721 := by
  unfold tailWord_230947
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423329094325936452523095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5615552729550624301682063 8423329094325936452523095)
  ·
    refine ⟨12634993641488904678784643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8423329094325936452523095 12634993641488904678784643)
    ·
      refine ⟨18952490462233357018176965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12634993641488904678784643 18952490462233357018176965)
      ·
        refine ⟨3553591961668754440908181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18952490462233357018176965 3553591961668754440908181)
        ·
          refine ⟨166574623203222864417571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3553591961668754440908181 166574623203222864417571)
          ·
            refine ⟨249861934804834296626357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166574623203222864417571 249861934804834296626357)
            ·
              refine ⟨23424556387953215308721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249861934804834296626357 23424556387953215308721)
              ·
                rfl

theorem cell19_230947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_230947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230947 prefixEnd_230947 := by exact prefixLift 230947
  have htrace : WordTrace (prefixWord ++ tailWord_230947) baseStart_230947 baseEnd_230947 := by
    simpa [prefixWord, tailWord_230947, baseEnd_230947] using wordTrace_append hprefix tailTrace_230947
  have hstable : (prefixWord ++ tailWord_230947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230947).length < 2 ^ (prefixWord ++ tailWord_230947).sum := by decide
  have hdescent : baseEnd_230947 < baseStart_230947 := by decide
  rcases family_descends (prefixWord ++ tailWord_230947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230968 : List Nat := [2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_230968 : Nat := 118140960795 + 230968 * 2 ^ 59
def prefixEnd_230968 : Nat := 4983230072969 + 3 ^ 40 * 230968 * 2
def baseEnd_230968 : Nat := 70280059145337819459439

theorem tailTrace_230968 : CollatzResearch.WordTrace tailWord_230968 prefixEnd_230968 70280059145337819459439 := by
  unfold tailWord_230968
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212047513624928519518779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5616063351499904692691705 4212047513624928519518779)
  ·
    refine ⟨6318071270437392779278169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4212047513624928519518779 6318071270437392779278169)
    ·
      refine ⟨4738553452828044584458627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6318071270437392779278169 4738553452828044584458627)
      ·
        refine ⟨7107830179242066876687941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738553452828044584458627 7107830179242066876687941)
        ·
          refine ⟨1332718158607887539378989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7107830179242066876687941 1332718158607887539378989)
          ·
            refine ⟨499769309477957827267121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1332718158607887539378989 499769309477957827267121)
            ·
              refine ⟨374826982108468370450341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499769309477957827267121 374826982108468370450341)
              ·
                refine ⟨70280059145337819459439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374826982108468370450341 70280059145337819459439)
                ·
                  rfl

theorem cell19_230968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_230968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230968 prefixEnd_230968 := by exact prefixLift 230968
  have htrace : WordTrace (prefixWord ++ tailWord_230968) baseStart_230968 baseEnd_230968 := by
    simpa [prefixWord, tailWord_230968, baseEnd_230968] using wordTrace_append hprefix tailTrace_230968
  have hstable : (prefixWord ++ tailWord_230968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230968).length < 2 ^ (prefixWord ++ tailWord_230968).sum := by decide
  have hdescent : baseEnd_230968 < baseStart_230968 := by decide
  rcases family_descends (prefixWord ++ tailWord_230968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231021 : List Nat := [1, 5, 1, 1, 5, 1, 1, 4]
def baseStart_231021 : Nat := 118140960795 + 231021 * 2 ^ 59
def prefixEnd_231021 : Nat := 4983230072969 + 3 ^ 40 * 231021 * 2
def baseEnd_231021 : Nat := 70296186241449400281517

theorem tailTrace_231021 : CollatzResearch.WordTrace tailWord_231021 prefixEnd_231021 70296186241449400281517 := by
  unfold tailWord_231021
  simp only [CollatzResearch.WordTrace]
  refine ⟨8426028096057847090716917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5617352064038564727144611 8426028096057847090716917)
  ·
    refine ⟨789940134005423164754711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8426028096057847090716917 789940134005423164754711)
    ·
      refine ⟨1184910201008134747132067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789940134005423164754711 1184910201008134747132067)
      ·
        refine ⟨1777365301512202120698101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184910201008134747132067 1777365301512202120698101)
        ·
          refine ⟨166627997016768948815447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1777365301512202120698101 166627997016768948815447)
          ·
            refine ⟨249941995525153423223171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166627997016768948815447 249941995525153423223171)
            ·
              refine ⟨374912993287730134834757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249941995525153423223171 374912993287730134834757)
              ·
                refine ⟨70296186241449400281517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374912993287730134834757 70296186241449400281517)
                ·
                  rfl

theorem cell19_231021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_231021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231021 prefixEnd_231021 := by exact prefixLift 231021
  have htrace : WordTrace (prefixWord ++ tailWord_231021) baseStart_231021 baseEnd_231021 := by
    simpa [prefixWord, tailWord_231021, baseEnd_231021] using wordTrace_append hprefix tailTrace_231021
  have hstable : (prefixWord ++ tailWord_231021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231021).length < 2 ^ (prefixWord ++ tailWord_231021).sum := by decide
  have hdescent : baseEnd_231021 < baseStart_231021 := by decide
  rcases family_descends (prefixWord ++ tailWord_231021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231103 : List Nat := [1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_231103 : Nat := 118140960795 + 231103 * 2 ^ 59
def prefixEnd_231103 : Nat := 4983230072969 + 3 ^ 40 * 231103 * 2
def baseEnd_231103 : Nat := 70321137597697506459071

theorem tailTrace_231103 : CollatzResearch.WordTrace tailWord_231103 prefixEnd_231103 70321137597697506459071 := by
  unfold tailWord_231103
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429018881760775095201963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5619345921173850063467975 8429018881760775095201963)
  ·
    refine ⟨12643528322641162642802945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429018881760775095201963 12643528322641162642802945)
    ·
      refine ⟨9482646241980871982102209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12643528322641162642802945 9482646241980871982102209)
      ·
        refine ⟨7111984681485653986576657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9482646241980871982102209 7111984681485653986576657)
        ·
          refine ⟨5333988511114240489932493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7111984681485653986576657 5333988511114240489932493)
          ·
            refine ⟨2000245691667840183724685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5333988511114240489932493 2000245691667840183724685)
            ·
              refine ⟨750092134375440068896757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2000245691667840183724685 750092134375440068896757)
              ·
                refine ⟨70321137597697506459071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 750092134375440068896757 70321137597697506459071)
                ·
                  rfl

theorem cell19_231103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_231103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231103 prefixEnd_231103 := by exact prefixLift 231103
  have htrace : WordTrace (prefixWord ++ tailWord_231103) baseStart_231103 baseEnd_231103 := by
    simpa [prefixWord, tailWord_231103, baseEnd_231103] using wordTrace_append hprefix tailTrace_231103
  have hstable : (prefixWord ++ tailWord_231103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231103).length < 2 ^ (prefixWord ++ tailWord_231103).sum := by decide
  have hdescent : baseEnd_231103 < baseStart_231103 := by decide
  rcases family_descends (prefixWord ++ tailWord_231103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231158 : List Nat := [5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_231158 : Nat := 118140960795 + 231158 * 2 ^ 59
def prefixEnd_231158 : Nat := 4983230072969 + 3 ^ 40 * 231158 * 2
def baseEnd_231158 : Nat := 70337873263473675236699

theorem tailTrace_231158 : CollatzResearch.WordTrace tailWord_231158 prefixEnd_231158 70337873263473675236699 := by
  unfold tailWord_231158
  simp only [CollatzResearch.WordTrace]
  refine ⟨526939056035094968028383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5620683264374346325636085 526939056035094968028383)
  ·
    refine ⟨790408584052642452042575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 526939056035094968028383 790408584052642452042575)
    ·
      refine ⟨1185612876078963678063863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790408584052642452042575 1185612876078963678063863)
      ·
        refine ⟨1778419314118445517095795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185612876078963678063863 1778419314118445517095795)
        ·
          refine ⟨2667628971177668275643693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778419314118445517095795 2667628971177668275643693)
          ·
            refine ⟨1000360864191625603366385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2667628971177668275643693 1000360864191625603366385)
            ·
              refine ⟨750270648143719202524789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000360864191625603366385 750270648143719202524789)
              ·
                refine ⟨70337873263473675236699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 750270648143719202524789 70337873263473675236699)
                ·
                  rfl

theorem cell19_231158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_231158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231158 prefixEnd_231158 := by exact prefixLift 231158
  have htrace : WordTrace (prefixWord ++ tailWord_231158) baseStart_231158 baseEnd_231158 := by
    simpa [prefixWord, tailWord_231158, baseEnd_231158] using wordTrace_append hprefix tailTrace_231158
  have hstable : (prefixWord ++ tailWord_231158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231158).length < 2 ^ (prefixWord ++ tailWord_231158).sum := by decide
  have hdescent : baseEnd_231158 < baseStart_231158 := by decide
  rcases family_descends (prefixWord ++ tailWord_231158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231188 : List Nat := [2, 4, 4, 1, 2, 1, 1, 4]
def baseStart_231188 : Nat := 118140960795 + 231188 * 2 ^ 59
def prefixEnd_231188 : Nat := 4983230072969 + 3 ^ 40 * 231188 * 2
def baseEnd_231188 : Nat := 70347001808442494569951

theorem tailTrace_231188 : CollatzResearch.WordTrace tailWord_231188 prefixEnd_231188 70347001808442494569951 := by
  unfold tailWord_231188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216059543226417306023109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5621412724301889741364145 4216059543226417306023109)
  ·
    refine ⟨790511164354953244879333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4216059543226417306023109 790511164354953244879333)
    ·
      refine ⟨148220843316553733414875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 790511164354953244879333 148220843316553733414875)
      ·
        refine ⟨222331264974830600122313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148220843316553733414875 222331264974830600122313)
        ·
          refine ⟨166748448731122950091735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222331264974830600122313 166748448731122950091735)
          ·
            refine ⟨250122673096684425137603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166748448731122950091735 250122673096684425137603)
            ·
              refine ⟨375184009645026637706405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250122673096684425137603 375184009645026637706405)
              ·
                refine ⟨70347001808442494569951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375184009645026637706405 70347001808442494569951)
                ·
                  rfl

theorem cell19_231188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_231188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231188 prefixEnd_231188 := by exact prefixLift 231188
  have htrace : WordTrace (prefixWord ++ tailWord_231188) baseStart_231188 baseEnd_231188 := by
    simpa [prefixWord, tailWord_231188, baseEnd_231188] using wordTrace_append hprefix tailTrace_231188
  have hstable : (prefixWord ++ tailWord_231188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231188).length < 2 ^ (prefixWord ++ tailWord_231188).sum := by decide
  have hdescent : baseEnd_231188 < baseStart_231188 := by decide
  rcases family_descends (prefixWord ++ tailWord_231188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231268 : List Nat := [2, 3, 1, 1, 6, 1, 2, 3]
def baseStart_231268 : Nat := 118140960795 + 231268 * 2 ^ 59
def prefixEnd_231268 : Nat := 4983230072969 + 3 ^ 40 * 231268 * 2
def baseEnd_231268 : Nat := 70371344595026012791955

theorem tailTrace_231268 : CollatzResearch.WordTrace tailWord_231268 prefixEnd_231268 70371344595026012791955 := by
  unfold tailWord_231268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217518463081504137479229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5623357950775338849972305 4217518463081504137479229)
  ·
    refine ⟨1581569423655564051554711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4217518463081504137479229 1581569423655564051554711)
    ·
      refine ⟨2372354135483346077332067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581569423655564051554711 2372354135483346077332067)
      ·
        refine ⟨3558531203225019115998101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372354135483346077332067 3558531203225019115998101)
        ·
          refine ⟨166806150151172771062411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3558531203225019115998101 166806150151172771062411)
          ·
            refine ⟨250209225226759156593617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166806150151172771062411 250209225226759156593617)
            ·
              refine ⟨187656918920069367445213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250209225226759156593617 187656918920069367445213)
              ·
                refine ⟨70371344595026012791955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187656918920069367445213 70371344595026012791955)
                ·
                  rfl

theorem cell19_231268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_231268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231268 prefixEnd_231268 := by exact prefixLift 231268
  have htrace : WordTrace (prefixWord ++ tailWord_231268) baseStart_231268 baseEnd_231268 := by
    simpa [prefixWord, tailWord_231268, baseEnd_231268] using wordTrace_append hprefix tailTrace_231268
  have hstable : (prefixWord ++ tailWord_231268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231268).length < 2 ^ (prefixWord ++ tailWord_231268).sum := by decide
  have hdescent : baseEnd_231268 < baseStart_231268 := by decide
  rcases family_descends (prefixWord ++ tailWord_231268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231348 : List Nat := [2, 5, 2, 1, 9]
def baseStart_231348 : Nat := 118140960795 + 231348 * 2 ^ 59
def prefixEnd_231348 : Nat := 4983230072969 + 3 ^ 40 * 231348 * 2
def baseEnd_231348 : Nat := 2607247680800353000517

theorem tailTrace_231348 : CollatzResearch.WordTrace tailWord_231348 prefixEnd_231348 2607247680800353000517 := by
  unfold tailWord_231348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218977382936590968935349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5625303177248787958580465 4218977382936590968935349)
  ·
    refine ⟨395529129650305403337689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4218977382936590968935349 395529129650305403337689)
    ·
      refine ⟨296646847237729052503267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395529129650305403337689 296646847237729052503267)
      ·
        refine ⟨444970270856593578754901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296646847237729052503267 444970270856593578754901)
        ·
          refine ⟨2607247680800353000517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 444970270856593578754901 2607247680800353000517)
          ·
            rfl

theorem cell19_231348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 9].length) (baseStart_231348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231348 prefixEnd_231348 := by exact prefixLift 231348
  have htrace : WordTrace (prefixWord ++ tailWord_231348) baseStart_231348 baseEnd_231348 := by
    simpa [prefixWord, tailWord_231348, baseEnd_231348] using wordTrace_append hprefix tailTrace_231348
  have hstable : (prefixWord ++ tailWord_231348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231348).length < 2 ^ (prefixWord ++ tailWord_231348).sum := by decide
  have hdescent : baseEnd_231348 < baseStart_231348 := by decide
  rcases family_descends (prefixWord ++ tailWord_231348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231382 : List Nat := [5, 2, 1, 1, 3, 1, 3, 3]
def baseStart_231382 : Nat := 118140960795 + 231382 * 2 ^ 59
def prefixEnd_231382 : Nat := 4983230072969 + 3 ^ 40 * 231382 * 2
def baseEnd_231382 : Nat := 70406033065907526258311

theorem tailTrace_231382 : CollatzResearch.WordTrace tailWord_231382 prefixEnd_231382 70406033065907526258311 := by
  unfold tailWord_231382
  simp only [CollatzResearch.WordTrace]
  refine ⟨527449677984375359038025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5626129898500003829738933 527449677984375359038025)
  ·
    refine ⟨395587258488281519278519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 527449677984375359038025 395587258488281519278519)
    ·
      refine ⟨593380887732422278917779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395587258488281519278519 593380887732422278917779)
      ·
        refine ⟨890071331598633418376669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593380887732422278917779 890071331598633418376669)
        ·
          refine ⟨333776749349487531891251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890071331598633418376669 333776749349487531891251)
          ·
            refine ⟨500665124024231297836877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333776749349487531891251 500665124024231297836877)
            ·
              refine ⟨187749421509086736688829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500665124024231297836877 187749421509086736688829)
              ·
                refine ⟨70406033065907526258311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187749421509086736688829 70406033065907526258311)
                ·
                  rfl

theorem cell19_231382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_231382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231382 prefixEnd_231382 := by exact prefixLift 231382
  have htrace : WordTrace (prefixWord ++ tailWord_231382) baseStart_231382 baseEnd_231382 := by
    simpa [prefixWord, tailWord_231382, baseEnd_231382] using wordTrace_append hprefix tailTrace_231382
  have hstable : (prefixWord ++ tailWord_231382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231382).length < 2 ^ (prefixWord ++ tailWord_231382).sum := by decide
  have hdescent : baseEnd_231382 < baseStart_231382 := by decide
  rcases family_descends (prefixWord ++ tailWord_231382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231460 : List Nat := [2, 3, 1, 4, 3, 1, 5]
def baseStart_231460 : Nat := 118140960795 + 231460 * 2 ^ 59
def prefixEnd_231460 : Nat := 4983230072969 + 3 ^ 40 * 231460 * 2
def baseEnd_231460 : Nat := 23476589094275485508255

theorem tailTrace_231460 : CollatzResearch.WordTrace tailWord_231460 prefixEnd_231460 23476589094275485508255 := by
  unfold tailWord_231460
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221019870733712532973917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5628026494311616710631889 4221019870733712532973917)
  ·
    refine ⟨1582882451525142199865219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4221019870733712532973917 1582882451525142199865219)
    ·
      refine ⟨2374323677287713299797829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582882451525142199865219 2374323677287713299797829)
      ·
        refine ⟨445185689491446243712093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2374323677287713299797829 445185689491446243712093)
        ·
          refine ⟨166944633559292341392035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445185689491446243712093 166944633559292341392035)
          ·
            refine ⟨250416950338938512088053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166944633559292341392035 250416950338938512088053)
            ·
              refine ⟨23476589094275485508255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250416950338938512088053 23476589094275485508255)
              ·
                rfl

theorem cell19_231460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_231460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231460 prefixEnd_231460 := by exact prefixLift 231460
  have htrace : WordTrace (prefixWord ++ tailWord_231460) baseStart_231460 baseEnd_231460 := by
    simpa [prefixWord, tailWord_231460, baseEnd_231460] using wordTrace_append hprefix tailTrace_231460
  have hstable : (prefixWord ++ tailWord_231460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231460).length < 2 ^ (prefixWord ++ tailWord_231460).sum := by decide
  have hdescent : baseEnd_231460 < baseStart_231460 := by decide
  rcases family_descends (prefixWord ++ tailWord_231460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231481 : List Nat := [1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_231481 : Nat := 118140960795 + 231481 * 2 ^ 59
def prefixEnd_231481 : Nat := 4983230072969 + 3 ^ 40 * 231481 * 2
def baseEnd_231481 : Nat := 70436157264304630058041

theorem tailTrace_231481 : CollatzResearch.WordTrace tailWord_231481 prefixEnd_231481 70436157264304630058041 := by
  unfold tailWord_231481
  simp only [CollatzResearch.WordTrace]
  refine ⟨8442805674391345652462297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5628537116260897101641531 8442805674391345652462297)
  ·
    refine ⟨6332104255793509239346723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8442805674391345652462297 6332104255793509239346723)
    ·
      refine ⟨9498156383690263859020085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6332104255793509239346723 9498156383690263859020085)
      ·
        refine ⟨890452160970962236783133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9498156383690263859020085 890452160970962236783133)
        ·
          refine ⟨333919560364110838793675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890452160970962236783133 333919560364110838793675)
          ·
            refine ⟨500879340546166258190513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333919560364110838793675 500879340546166258190513)
            ·
              refine ⟨375659505409624693642885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500879340546166258190513 375659505409624693642885)
              ·
                refine ⟨70436157264304630058041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375659505409624693642885 70436157264304630058041)
                ·
                  rfl

theorem cell19_231481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_231481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231481 prefixEnd_231481 := by exact prefixLift 231481
  have htrace : WordTrace (prefixWord ++ tailWord_231481) baseStart_231481 baseEnd_231481 := by
    simpa [prefixWord, tailWord_231481, baseEnd_231481] using wordTrace_append hprefix tailTrace_231481
  have hstable : (prefixWord ++ tailWord_231481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231481).length < 2 ^ (prefixWord ++ tailWord_231481).sum := by decide
  have hdescent : baseEnd_231481 < baseStart_231481 := by decide
  rcases family_descends (prefixWord ++ tailWord_231481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231502 : List Nat := [4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_231502 : Nat := 118140960795 + 231502 * 2 ^ 59
def prefixEnd_231502 : Nat := 4983230072969 + 3 ^ 40 * 231502 * 2
def baseEnd_231502 : Nat := 70442547245782803591317

theorem tailTrace_231502 : CollatzResearch.WordTrace tailWord_231502 prefixEnd_231502 70442547245782803591317 := by
  unfold tailWord_231502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055446450914408279872095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5629047738210177492651173 1055446450914408279872095)
  ·
    refine ⟨1583169676371612419808143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055446450914408279872095 1583169676371612419808143)
    ·
      refine ⟨2374754514557418629712215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583169676371612419808143 2374754514557418629712215)
      ·
        refine ⟨3562131771836127944568323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374754514557418629712215 3562131771836127944568323)
        ·
          refine ⟨5343197657754191916852485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562131771836127944568323 5343197657754191916852485)
          ·
            refine ⟨1001849560828910984409841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5343197657754191916852485 1001849560828910984409841)
            ·
              refine ⟨751387170621683238307381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001849560828910984409841 751387170621683238307381)
              ·
                refine ⟨70442547245782803591317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751387170621683238307381 70442547245782803591317)
                ·
                  rfl

theorem cell19_231502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_231502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231502 prefixEnd_231502 := by exact prefixLift 231502
  have htrace : WordTrace (prefixWord ++ tailWord_231502) baseStart_231502 baseEnd_231502 := by
    simpa [prefixWord, tailWord_231502, baseEnd_231502] using wordTrace_append hprefix tailTrace_231502
  have hstable : (prefixWord ++ tailWord_231502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231502).length < 2 ^ (prefixWord ++ tailWord_231502).sum := by decide
  have hdescent : baseEnd_231502 < baseStart_231502 := by decide
  rcases family_descends (prefixWord ++ tailWord_231502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231538 : List Nat := [3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_231538 : Nat := 118140960795 + 231538 * 2 ^ 59
def prefixEnd_231538 : Nat := 4983230072969 + 3 ^ 40 * 231538 * 2
def baseEnd_231538 : Nat := 70453501499745386791219

theorem tailTrace_231538 : CollatzResearch.WordTrace tailWord_231538 prefixEnd_231538 70453501499745386791219 := by
  unfold tailWord_231538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111221158796211096821817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5629923090123229591524845 2111221158796211096821817)
  ·
    refine ⟨1583415869097158322616363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2111221158796211096821817 1583415869097158322616363)
    ·
      refine ⟨2375123803645737483924545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583415869097158322616363 2375123803645737483924545)
      ·
        refine ⟨1781342852734303112943409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2375123803645737483924545 1781342852734303112943409)
        ·
          refine ⟨1336007139550727334707557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1781342852734303112943409 1336007139550727334707557)
          ·
            refine ⟨250501338665761375257667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1336007139550727334707557 250501338665761375257667)
            ·
              refine ⟨375752007998642062886501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250501338665761375257667 375752007998642062886501)
              ·
                refine ⟨70453501499745386791219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375752007998642062886501 70453501499745386791219)
                ·
                  rfl

theorem cell19_231538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_231538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231538 prefixEnd_231538 := by exact prefixLift 231538
  have htrace : WordTrace (prefixWord ++ tailWord_231538) baseStart_231538 baseEnd_231538 := by
    simpa [prefixWord, tailWord_231538, baseEnd_231538] using wordTrace_append hprefix tailTrace_231538
  have hstable : (prefixWord ++ tailWord_231538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231538).length < 2 ^ (prefixWord ++ tailWord_231538).sum := by decide
  have hdescent : baseEnd_231538 < baseStart_231538 := by decide
  rcases family_descends (prefixWord ++ tailWord_231538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231557 : List Nat := [1, 3, 1, 1, 5, 2, 3, 3]
def baseStart_231557 : Nat := 118140960795 + 231557 * 2 ^ 59
def prefixEnd_231557 : Nat := 4983230072969 + 3 ^ 40 * 231557 * 2
def baseEnd_231557 : Nat := 70459282911558972368945

theorem tailTrace_231557 : CollatzResearch.WordTrace tailWord_231557 prefixEnd_231557 70459282911558972368945 := by
  unfold tailWord_231557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8445577622116010632228925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5630385081410673754819283 8445577622116010632228925)
  ·
    refine ⟨3167091608293503987085847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8445577622116010632228925 3167091608293503987085847)
    ·
      refine ⟨4750637412440255980628771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167091608293503987085847 4750637412440255980628771)
      ·
        refine ⟨7125956118660383970943157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750637412440255980628771 7125956118660383970943157)
        ·
          refine ⟨668058386124410997275921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7125956118660383970943157 668058386124410997275921)
          ·
            refine ⟨501043789593308247956941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668058386124410997275921 501043789593308247956941)
            ·
              refine ⟨187891421097490592983853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501043789593308247956941 187891421097490592983853)
              ·
                refine ⟨70459282911558972368945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187891421097490592983853 70459282911558972368945)
                ·
                  rfl

theorem cell19_231557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_231557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231557 prefixEnd_231557 := by exact prefixLift 231557
  have htrace : WordTrace (prefixWord ++ tailWord_231557) baseStart_231557 baseEnd_231557 := by
    simpa [prefixWord, tailWord_231557, baseEnd_231557] using wordTrace_append hprefix tailTrace_231557
  have hstable : (prefixWord ++ tailWord_231557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231557).length < 2 ^ (prefixWord ++ tailWord_231557).sum := by decide
  have hdescent : baseEnd_231557 < baseStart_231557 := by decide
  rcases family_descends (prefixWord ++ tailWord_231557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231599 : List Nat := [1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_231599 : Nat := 118140960795 + 231599 * 2 ^ 59
def prefixEnd_231599 : Nat := 4983230072969 + 3 ^ 40 * 231599 * 2
def baseEnd_231599 : Nat := 70472062874515319435497

theorem tailTrace_231599 : CollatzResearch.WordTrace tailWord_231599 prefixEnd_231599 70472062874515319435497 := by
  unfold tailWord_231599
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447109487963851805257851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5631406325309234536838567 8447109487963851805257851)
  ·
    refine ⟨12670664231945777707886777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8447109487963851805257851 12670664231945777707886777)
    ·
      refine ⟨9502998173959333280915083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12670664231945777707886777 9502998173959333280915083)
      ·
        refine ⟨14254497260938999921372625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9502998173959333280915083 14254497260938999921372625)
        ·
          refine ⟨10690872945704249941029469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14254497260938999921372625 10690872945704249941029469)
          ·
            refine ⟨4009077354639093727886051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10690872945704249941029469 4009077354639093727886051)
            ·
              refine ⟨6013616031958640591829077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009077354639093727886051 6013616031958640591829077)
              ·
                refine ⟨70472062874515319435497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6013616031958640591829077 70472062874515319435497)
                ·
                  rfl

theorem cell19_231599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_231599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231599 prefixEnd_231599 := by exact prefixLift 231599
  have htrace : WordTrace (prefixWord ++ tailWord_231599) baseStart_231599 baseEnd_231599 := by
    simpa [prefixWord, tailWord_231599, baseEnd_231599] using wordTrace_append hprefix tailTrace_231599
  have hstable : (prefixWord ++ tailWord_231599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231599).length < 2 ^ (prefixWord ++ tailWord_231599).sum := by decide
  have hdescent : baseEnd_231599 < baseStart_231599 := by decide
  rcases family_descends (prefixWord ++ tailWord_231599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231612 : List Nat := [2, 2, 2, 3, 3, 2, 2, 3]
def baseStart_231612 : Nat := 118140960795 + 231612 * 2 ^ 59
def prefixEnd_231612 : Nat := 4983230072969 + 3 ^ 40 * 231612 * 2
def baseEnd_231612 : Nat := 70476018577335141146573

theorem tailTrace_231612 : CollatzResearch.WordTrace tailWord_231612 prefixEnd_231612 70476018577335141146573 := by
  unfold tailWord_231612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223791818458377512740545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5631722424611170016987393 4223791818458377512740545)
  ·
    refine ⟨3167843863843783134555409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4223791818458377512740545 3167843863843783134555409)
    ·
      refine ⟨2375882897882837350916557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3167843863843783134555409 2375882897882837350916557)
      ·
        refine ⟨890956086706064006593709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2375882897882837350916557 890956086706064006593709)
        ·
          refine ⟨334108532514774002472641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890956086706064006593709 334108532514774002472641)
          ·
            refine ⟨250581399386080501854481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334108532514774002472641 250581399386080501854481)
            ·
              refine ⟨187936049539560376390861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250581399386080501854481 187936049539560376390861)
              ·
                refine ⟨70476018577335141146573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187936049539560376390861 70476018577335141146573)
                ·
                  rfl

theorem cell19_231612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_231612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231612 prefixEnd_231612 := by exact prefixLift 231612
  have htrace : WordTrace (prefixWord ++ tailWord_231612) baseStart_231612 baseEnd_231612 := by
    simpa [prefixWord, tailWord_231612, baseEnd_231612] using wordTrace_append hprefix tailTrace_231612
  have hstable : (prefixWord ++ tailWord_231612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231612).length < 2 ^ (prefixWord ++ tailWord_231612).sum := by decide
  have hdescent : baseEnd_231612 < baseStart_231612 := by decide
  rcases family_descends (prefixWord ++ tailWord_231612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231614 : List Nat := [4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_231614 : Nat := 118140960795 + 231614 * 2 ^ 59
def prefixEnd_231614 : Nat := 4983230072969 + 3 ^ 40 * 231614 * 2
def baseEnd_231614 : Nat := 70476627146999729102123

theorem tailTrace_231614 : CollatzResearch.WordTrace tailWord_231614 prefixEnd_231614 70476627146999729102123 := by
  unfold tailWord_231614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055957072863688670881737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5631771055273006244702597 1055957072863688670881737)
  ·
    refine ⟨791967804647766503161303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1055957072863688670881737 791967804647766503161303)
    ·
      refine ⟨1187951706971649754741955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791967804647766503161303 1187951706971649754741955)
      ·
        refine ⟨1781927560457474632112933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187951706971649754741955 1781927560457474632112933)
        ·
          refine ⟨334111417585776493521175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1781927560457474632112933 334111417585776493521175)
          ·
            refine ⟨501167126378664740281763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334111417585776493521175 501167126378664740281763)
            ·
              refine ⟨751750689567997110422645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501167126378664740281763 751750689567997110422645)
              ·
                refine ⟨70476627146999729102123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751750689567997110422645 70476627146999729102123)
                ·
                  rfl

theorem cell19_231614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_231614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231614 prefixEnd_231614 := by exact prefixLift 231614
  have htrace : WordTrace (prefixWord ++ tailWord_231614) baseStart_231614 baseEnd_231614 := by
    simpa [prefixWord, tailWord_231614, baseEnd_231614] using wordTrace_append hprefix tailTrace_231614
  have hstable : (prefixWord ++ tailWord_231614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231614).length < 2 ^ (prefixWord ++ tailWord_231614).sum := by decide
  have hdescent : baseEnd_231614 < baseStart_231614 := by decide
  rcases family_descends (prefixWord ++ tailWord_231614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231616 : List Nat := [2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_231616 : Nat := 118140960795 + 231616 * 2 ^ 59
def prefixEnd_231616 : Nat := 4983230072969 + 3 ^ 40 * 231616 * 2
def baseEnd_231616 : Nat := 70477235716664317057673

theorem tailTrace_231616 : CollatzResearch.WordTrace tailWord_231616 prefixEnd_231616 70477235716664317057673 := by
  unfold tailWord_231616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223864764451131854313351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5631819685934842472417801 4223864764451131854313351)
  ·
    refine ⟨6335797146676697781470027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4223864764451131854313351 6335797146676697781470027)
    ·
      refine ⟨9503695720015046672205041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6335797146676697781470027 9503695720015046672205041)
      ·
        refine ⟨7127771790011285004153781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9503695720015046672205041 7127771790011285004153781)
        ·
          refine ⟨668228605313557969139417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7127771790011285004153781 668228605313557969139417)
          ·
            refine ⟨501171453985168476854563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668228605313557969139417 501171453985168476854563)
            ·
              refine ⟨751757180977752715281845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501171453985168476854563 751757180977752715281845)
              ·
                refine ⟨70477235716664317057673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751757180977752715281845 70477235716664317057673)
                ·
                  rfl

theorem cell19_231616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_231616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231616 prefixEnd_231616 := by exact prefixLift 231616
  have htrace : WordTrace (prefixWord ++ tailWord_231616) baseStart_231616 baseEnd_231616 := by
    simpa [prefixWord, tailWord_231616, baseEnd_231616] using wordTrace_append hprefix tailTrace_231616
  have hstable : (prefixWord ++ tailWord_231616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231616).length < 2 ^ (prefixWord ++ tailWord_231616).sum := by decide
  have hdescent : baseEnd_231616 < baseStart_231616 := by decide
  rcases family_descends (prefixWord ++ tailWord_231616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231711 : List Nat := [1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_231711 : Nat := 118140960795 + 231711 * 2 ^ 59
def prefixEnd_231711 : Nat := 4983230072969 + 3 ^ 40 * 231711 * 2
def baseEnd_231711 : Nat := 70506142775732244946303

theorem tailTrace_231711 : CollatzResearch.WordTrace tailWord_231711 prefixEnd_231711 70506142775732244946303 := by
  unfold tailWord_231711
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451194463558094933334987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5634129642372063288889991 8451194463558094933334987)
  ·
    refine ⟨12676791695337142400002481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8451194463558094933334987 12676791695337142400002481)
    ·
      refine ⟨9507593771502856800001861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12676791695337142400002481 9507593771502856800001861)
      ·
        refine ⟨1782673832156785650000349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9507593771502856800001861 1782673832156785650000349)
        ·
          refine ⟨668502687058794618750131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1782673832156785650000349 668502687058794618750131)
          ·
            refine ⟨1002754030588191928125197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668502687058794618750131 1002754030588191928125197)
            ·
              refine ⟨376032761470571973046949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1002754030588191928125197 376032761470571973046949)
              ·
                refine ⟨70506142775732244946303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376032761470571973046949 70506142775732244946303)
                ·
                  rfl

theorem cell19_231711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_231711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231711 prefixEnd_231711 := by exact prefixLift 231711
  have htrace : WordTrace (prefixWord ++ tailWord_231711) baseStart_231711 baseEnd_231711 := by
    simpa [prefixWord, tailWord_231711, baseEnd_231711] using wordTrace_append hprefix tailTrace_231711
  have hstable : (prefixWord ++ tailWord_231711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231711).length < 2 ^ (prefixWord ++ tailWord_231711).sum := by decide
  have hdescent : baseEnd_231711 < baseStart_231711 := by decide
  rcases family_descends (prefixWord ++ tailWord_231711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231751 : List Nat := [1, 1, 4, 1, 2, 2, 8]
def baseStart_231751 : Nat := 118140960795 + 231751 * 2 ^ 59
def prefixEnd_231751 : Nat := 4983230072969 + 3 ^ 40 * 231751 * 2
def baseEnd_231751 : Nat := 23506104723008001352435

theorem tailTrace_231751 : CollatzResearch.WordTrace tailWord_231751 prefixEnd_231751 23506104723008001352435 := by
  unfold tailWord_231751
  simp only [CollatzResearch.WordTrace]
  refine ⟨8452653383413181764791107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5635102255608787843194071 8452653383413181764791107)
  ·
    refine ⟨12678980075119772647186661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8452653383413181764791107 12678980075119772647186661)
    ·
      refine ⟨2377308764084957371347499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12678980075119772647186661 2377308764084957371347499)
      ·
        refine ⟨3565963146127436057021249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377308764084957371347499 3565963146127436057021249)
        ·
          refine ⟨2674472359595577042765937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565963146127436057021249 2674472359595577042765937)
          ·
            refine ⟨2005854269696682782074453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2674472359595577042765937 2005854269696682782074453)
            ·
              refine ⟨23506104723008001352435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2005854269696682782074453 23506104723008001352435)
              ·
                rfl

theorem cell19_231751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_231751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231751 prefixEnd_231751 := by exact prefixLift 231751
  have htrace : WordTrace (prefixWord ++ tailWord_231751) baseStart_231751 baseEnd_231751 := by
    simpa [prefixWord, tailWord_231751, baseEnd_231751] using wordTrace_append hprefix tailTrace_231751
  have hstable : (prefixWord ++ tailWord_231751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231751).length < 2 ^ (prefixWord ++ tailWord_231751).sum := by decide
  have hdescent : baseEnd_231751 < baseStart_231751 := by decide
  rcases family_descends (prefixWord ++ tailWord_231751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231770 : List Nat := [3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_231770 : Nat := 118140960795 + 231770 * 2 ^ 59
def prefixEnd_231770 : Nat := 4983230072969 + 3 ^ 40 * 231770 * 2
def baseEnd_231770 : Nat := 70524095580837589635031

theorem tailTrace_231770 : CollatzResearch.WordTrace tailWord_231770 prefixEnd_231770 70524095580837589635031 := by
  unfold tailWord_231770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113336592586087002433191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5635564246896232006488509 2113336592586087002433191)
  ·
    refine ⟨3170004888879130503649787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2113336592586087002433191 3170004888879130503649787)
    ·
      refine ⟨4755007333318695755474681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170004888879130503649787 4755007333318695755474681)
      ·
        refine ⟨3566255499989021816606011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4755007333318695755474681 3566255499989021816606011)
        ·
          refine ⟨5349383249983532724909017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566255499989021816606011 5349383249983532724909017)
          ·
            refine ⟨4012037437487649543681763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5349383249983532724909017 4012037437487649543681763)
            ·
              refine ⟨6018056156231474315522645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012037437487649543681763 6018056156231474315522645)
              ·
                refine ⟨70524095580837589635031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6018056156231474315522645 70524095580837589635031)
                ·
                  rfl

theorem cell19_231770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_231770 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231770 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231770 prefixEnd_231770 := by exact prefixLift 231770
  have htrace : WordTrace (prefixWord ++ tailWord_231770) baseStart_231770 baseEnd_231770 := by
    simpa [prefixWord, tailWord_231770, baseEnd_231770] using wordTrace_append hprefix tailTrace_231770
  have hstable : (prefixWord ++ tailWord_231770).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231770).length < 2 ^ (prefixWord ++ tailWord_231770).sum := by decide
  have hdescent : baseEnd_231770 < baseStart_231770 := by decide
  rcases family_descends (prefixWord ++ tailWord_231770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231865 : List Nat := [1, 2, 1, 4, 3, 8]
def baseStart_231865 : Nat := 118140960795 + 231865 * 2 ^ 59
def prefixEnd_231865 : Nat := 4983230072969 + 3 ^ 40 * 231865 * 2
def baseEnd_231865 : Nat := 7839222515545057502629

theorem tailTrace_231865 : CollatzResearch.WordTrace tailWord_231865 prefixEnd_231865 7839222515545057502629 := by
  unfold tailWord_231865
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456811305000179234441049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5637874203333452822960699 8456811305000179234441049)
  ·
    refine ⟨6342608478750134425830787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8456811305000179234441049 6342608478750134425830787)
    ·
      refine ⟨9513912718125201638746181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342608478750134425830787 9513912718125201638746181)
      ·
        refine ⟨1783858634648475307264909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9513912718125201638746181 1783858634648475307264909)
        ·
          refine ⟨668946987993178240224341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1783858634648475307264909 668946987993178240224341)
          ·
            refine ⟨7839222515545057502629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 668946987993178240224341 7839222515545057502629)
            ·
              rfl

theorem cell19_231865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_231865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231865 prefixEnd_231865 := by exact prefixLift 231865
  have htrace : WordTrace (prefixWord ++ tailWord_231865) baseStart_231865 baseEnd_231865 := by
    simpa [prefixWord, tailWord_231865, baseEnd_231865] using wordTrace_append hprefix tailTrace_231865
  have hstable : (prefixWord ++ tailWord_231865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231865).length < 2 ^ (prefixWord ++ tailWord_231865).sum := by decide
  have hdescent : baseEnd_231865 < baseStart_231865 := by decide
  rcases family_descends (prefixWord ++ tailWord_231865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231956 : List Nat := [2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_231956 : Nat := 118140960795 + 231956 * 2 ^ 59
def prefixEnd_231956 : Nat := 4983230072969 + 3 ^ 40 * 231956 * 2
def baseEnd_231956 : Nat := 70580692559644269501191

theorem tailTrace_231956 : CollatzResearch.WordTrace tailWord_231956 prefixEnd_231956 70580692559644269501191 := by
  unfold tailWord_231956
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230065173835250888001861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5640086898447001184002481 4230065173835250888001861)
  ·
    refine ⟨793137220094109541500349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4230065173835250888001861 793137220094109541500349)
    ·
      refine ⟨297426457535291078062631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 793137220094109541500349 297426457535291078062631)
      ·
        refine ⟨446139686302936617093947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297426457535291078062631 446139686302936617093947)
        ·
          refine ⟨669209529454404925640921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446139686302936617093947 669209529454404925640921)
          ·
            refine ⟨501907147090803694230691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669209529454404925640921 501907147090803694230691)
            ·
              refine ⟨752860720636205541346037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501907147090803694230691 752860720636205541346037)
              ·
                refine ⟨70580692559644269501191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 752860720636205541346037 70580692559644269501191)
                ·
                  rfl

theorem cell19_231956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_231956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231956 prefixEnd_231956 := by exact prefixLift 231956
  have htrace : WordTrace (prefixWord ++ tailWord_231956) baseStart_231956 baseEnd_231956 := by
    simpa [prefixWord, tailWord_231956, baseEnd_231956] using wordTrace_append hprefix tailTrace_231956
  have hstable : (prefixWord ++ tailWord_231956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231956).length < 2 ^ (prefixWord ++ tailWord_231956).sum := by decide
  have hdescent : baseEnd_231956 < baseStart_231956 := by decide
  rcases family_descends (prefixWord ++ tailWord_231956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231996 : List Nat := [2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_231996 : Nat := 118140960795 + 231996 * 2 ^ 59
def prefixEnd_231996 : Nat := 4983230072969 + 3 ^ 40 * 231996 * 2
def baseEnd_231996 : Nat := 70592863952936028612193

theorem tailTrace_231996 : CollatzResearch.WordTrace tailWord_231996 prefixEnd_231996 70592863952936028612193 := by
  unfold tailWord_231996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230794633762794303729921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5641059511683725738306561 4230794633762794303729921)
  ·
    refine ⟨3173095975322095727797441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4230794633762794303729921 3173095975322095727797441)
    ·
      refine ⟨2379821981491571795848081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3173095975322095727797441 2379821981491571795848081)
      ·
        refine ⟨1784866486118678846886061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2379821981491571795848081 1784866486118678846886061)
        ·
          refine ⟨669324932294504567582273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1784866486118678846886061 669324932294504567582273)
          ·
            refine ⟨501993699220878425686705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669324932294504567582273 501993699220878425686705)
            ·
              refine ⟨376495274415658819265029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501993699220878425686705 376495274415658819265029)
              ·
                refine ⟨70592863952936028612193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376495274415658819265029 70592863952936028612193)
                ·
                  rfl

theorem cell19_231996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_231996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_231996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_231996 prefixEnd_231996 := by exact prefixLift 231996
  have htrace : WordTrace (prefixWord ++ tailWord_231996) baseStart_231996 baseEnd_231996 := by
    simpa [prefixWord, tailWord_231996, baseEnd_231996] using wordTrace_append hprefix tailTrace_231996
  have hstable : (prefixWord ++ tailWord_231996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231996).length < 2 ^ (prefixWord ++ tailWord_231996).sum := by decide
  have hdescent : baseEnd_231996 < baseStart_231996 := by decide
  rcases family_descends (prefixWord ++ tailWord_231996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232017 : List Nat := [1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_232017 : Nat := 118140960795 + 232017 * 2 ^ 59
def prefixEnd_232017 : Nat := 4983230072969 + 3 ^ 40 * 232017 * 2
def baseEnd_232017 : Nat := 70599253934414202145469

theorem tailTrace_232017 : CollatzResearch.WordTrace tailWord_232017 prefixEnd_232017 70599253934414202145469 := by
  unfold tailWord_232017
  simp only [CollatzResearch.WordTrace]
  refine ⟨8462355200449509193974305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5641570133633006129316203 8462355200449509193974305)
  ·
    refine ⟨6346766400337131895480729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8462355200449509193974305 6346766400337131895480729)
    ·
      refine ⟨4760074800252848921610547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6346766400337131895480729 4760074800252848921610547)
      ·
        refine ⟨7140112200379273382415821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760074800252848921610547 7140112200379273382415821)
        ·
          refine ⟨2677542075142227518405933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7140112200379273382415821 2677542075142227518405933)
          ·
            refine ⟨1004078278178335319402225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2677542075142227518405933 1004078278178335319402225)
            ·
              refine ⟨753058708633751489551669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004078278178335319402225 753058708633751489551669)
              ·
                refine ⟨70599253934414202145469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 753058708633751489551669 70599253934414202145469)
                ·
                  rfl

theorem cell19_232017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_232017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232017 prefixEnd_232017 := by exact prefixLift 232017
  have htrace : WordTrace (prefixWord ++ tailWord_232017) baseStart_232017 baseEnd_232017 := by
    simpa [prefixWord, tailWord_232017, baseEnd_232017] using wordTrace_append hprefix tailTrace_232017
  have hstable : (prefixWord ++ tailWord_232017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232017).length < 2 ^ (prefixWord ++ tailWord_232017).sum := by decide
  have hdescent : baseEnd_232017 < baseStart_232017 := by decide
  rcases family_descends (prefixWord ++ tailWord_232017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232030 : List Nat := [4, 4, 1, 2, 1, 7]
def baseStart_232030 : Nat := 118140960795 + 232030 * 2 ^ 59
def prefixEnd_232030 : Nat := 4983230072969 + 3 ^ 40 * 232030 * 2
def baseEnd_232030 : Nat := 7844801070803780428505

theorem tailTrace_232030 : CollatzResearch.WordTrace tailWord_232030 prefixEnd_232030 7844801070803780428505 := by
  unfold tailWord_232030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057853668675301551774693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5641886232934941609465029 1057853668675301551774693)
  ·
    refine ⟨198347562876619040957755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1057853668675301551774693 198347562876619040957755)
    ·
      refine ⟨297521344314928561436633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198347562876619040957755 297521344314928561436633)
      ·
        refine ⟨223141008236196421077475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297521344314928561436633 223141008236196421077475)
        ·
          refine ⟨334711512354294631616213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223141008236196421077475 334711512354294631616213)
          ·
            refine ⟨7844801070803780428505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 334711512354294631616213 7844801070803780428505)
            ·
              rfl

theorem cell19_232030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 7].length) (baseStart_232030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232030 prefixEnd_232030 := by exact prefixLift 232030
  have htrace : WordTrace (prefixWord ++ tailWord_232030) baseStart_232030 baseEnd_232030 := by
    simpa [prefixWord, tailWord_232030, baseEnd_232030] using wordTrace_append hprefix tailTrace_232030
  have hstable : (prefixWord ++ tailWord_232030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232030).length < 2 ^ (prefixWord ++ tailWord_232030).sum := by decide
  have hdescent : baseEnd_232030 < baseStart_232030 := by decide
  rcases family_descends (prefixWord ++ tailWord_232030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232034 : List Nat := [3, 3, 2, 3, 8]
def baseStart_232034 : Nat := 118140960795 + 232034 * 2 ^ 59
def prefixEnd_232034 : Nat := 4983230072969 + 3 ^ 40 * 232034 * 2
def baseEnd_232034 : Nat := 2614978769502340732135

theorem tailTrace_232034 : CollatzResearch.WordTrace tailWord_232034 prefixEnd_232034 2614978769502340732135 := by
  unfold tailWord_232034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115743810346980274335789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5641983494258614064895437 2115743810346980274335789)
  ·
    refine ⟨793403928880117602875921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2115743810346980274335789 793403928880117602875921)
    ·
      refine ⟨595052946660088202156941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 793403928880117602875921 595052946660088202156941)
      ·
        refine ⟨223144854997533075808853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595052946660088202156941 223144854997533075808853)
        ·
          refine ⟨2614978769502340732135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 223144854997533075808853 2614978769502340732135)
          ·
            rfl

theorem cell19_232034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 8].length) (baseStart_232034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232034 prefixEnd_232034 := by exact prefixLift 232034
  have htrace : WordTrace (prefixWord ++ tailWord_232034) baseStart_232034 baseEnd_232034 := by
    simpa [prefixWord, tailWord_232034, baseEnd_232034] using wordTrace_append hprefix tailTrace_232034
  have hstable : (prefixWord ++ tailWord_232034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232034).length < 2 ^ (prefixWord ++ tailWord_232034).sum := by decide
  have hdescent : baseEnd_232034 < baseStart_232034 := by decide
  rcases family_descends (prefixWord ++ tailWord_232034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232055 : List Nat := [1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_232055 : Nat := 118140960795 + 232055 * 2 ^ 59
def prefixEnd_232055 : Nat := 4983230072969 + 3 ^ 40 * 232055 * 2
def baseEnd_232055 : Nat := 70610816758041373300921

theorem tailTrace_232055 : CollatzResearch.WordTrace tailWord_232055 prefixEnd_232055 70610816758041373300921 := by
  unfold tailWord_232055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463741174311841683857619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5642494116207894455905079 8463741174311841683857619)
  ·
    refine ⟨12695611761467762525786429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8463741174311841683857619 12695611761467762525786429)
    ·
      refine ⟨4760854410550410947169911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12695611761467762525786429 4760854410550410947169911)
      ·
        refine ⟨7141281615825616420754867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760854410550410947169911 7141281615825616420754867)
        ·
          refine ⟨10711922423738424631132301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141281615825616420754867 10711922423738424631132301)
          ·
            refine ⟨4016970908901909236674613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10711922423738424631132301 4016970908901909236674613)
            ·
              refine ⟨376591022709553990938245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4016970908901909236674613 376591022709553990938245)
              ·
                refine ⟨70610816758041373300921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376591022709553990938245 70610816758041373300921)
                ·
                  rfl

theorem cell19_232055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_232055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232055 prefixEnd_232055 := by exact prefixLift 232055
  have htrace : WordTrace (prefixWord ++ tailWord_232055) baseStart_232055 baseEnd_232055 := by
    simpa [prefixWord, tailWord_232055, baseEnd_232055] using wordTrace_append hprefix tailTrace_232055
  have hstable : (prefixWord ++ tailWord_232055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232055).length < 2 ^ (prefixWord ++ tailWord_232055).sum := by decide
  have hdescent : baseEnd_232055 < baseStart_232055 := by decide
  rcases family_descends (prefixWord ++ tailWord_232055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232146 : List Nat := [3, 2, 2, 2, 4, 1, 5]
def baseStart_232146 : Nat := 118140960795 + 232146 * 2 ^ 59
def prefixEnd_232146 : Nat := 4983230072969 + 3 ^ 40 * 232146 * 2
def baseEnd_232146 : Nat := 23546168892593375092817

theorem tailTrace_232146 : CollatzResearch.WordTrace tailWord_232146 prefixEnd_232146 23546168892593375092817 := by
  unfold tailWord_232146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116765054245541056355073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5644706811321442816946861 2116765054245541056355073)
  ·
    refine ⟨1587573790684155792266305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2116765054245541056355073 1587573790684155792266305)
    ·
      refine ⟨1190680343013116844199729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1587573790684155792266305 1190680343013116844199729)
      ·
        refine ⟨893010257259837633149797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190680343013116844199729 893010257259837633149797)
        ·
          refine ⟨167439423236219556215587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 893010257259837633149797 167439423236219556215587)
          ·
            refine ⟨251159134854329334323381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167439423236219556215587 251159134854329334323381)
            ·
              refine ⟨23546168892593375092817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251159134854329334323381 23546168892593375092817)
              ·
                rfl

theorem cell19_232146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_232146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232146 prefixEnd_232146 := by exact prefixLift 232146
  have htrace : WordTrace (prefixWord ++ tailWord_232146) baseStart_232146 baseEnd_232146 := by
    simpa [prefixWord, tailWord_232146, baseEnd_232146] using wordTrace_append hprefix tailTrace_232146
  have hstable : (prefixWord ++ tailWord_232146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232146).length < 2 ^ (prefixWord ++ tailWord_232146).sum := by decide
  have hdescent : baseEnd_232146 < baseStart_232146 := by decide
  rcases family_descends (prefixWord ++ tailWord_232146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232188 : List Nat := [2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_232188 : Nat := 118140960795 + 232188 * 2 ^ 59
def prefixEnd_232188 : Nat := 4983230072969 + 3 ^ 40 * 232188 * 2
def baseEnd_232188 : Nat := 70651286640736472345003

theorem tailTrace_232188 : CollatzResearch.WordTrace tailWord_232188 prefixEnd_232188 70651286640736472345003 := by
  unfold tailWord_232188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234296041415002699224609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5645728055220003598966145 4234296041415002699224609)
  ·
    refine ⟨3175722031061252024418457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4234296041415002699224609 3175722031061252024418457)
    ·
      refine ⟨2381791523295939018313843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3175722031061252024418457 2381791523295939018313843)
      ·
        refine ⟨3572687284943908527470765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381791523295939018313843 3572687284943908527470765)
        ·
          refine ⟨1339757731853965697801537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3572687284943908527470765 1339757731853965697801537)
          ·
            refine ⟨1004818298890474273351153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339757731853965697801537 1004818298890474273351153)
            ·
              refine ⟨753613724167855705013365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004818298890474273351153 753613724167855705013365)
              ·
                refine ⟨70651286640736472345003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 753613724167855705013365 70651286640736472345003)
                ·
                  rfl

theorem cell19_232188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_232188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232188 prefixEnd_232188 := by exact prefixLift 232188
  have htrace : WordTrace (prefixWord ++ tailWord_232188) baseStart_232188 baseEnd_232188 := by
    simpa [prefixWord, tailWord_232188, baseEnd_232188] using wordTrace_append hprefix tailTrace_232188
  have hstable : (prefixWord ++ tailWord_232188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232188).length < 2 ^ (prefixWord ++ tailWord_232188).sum := by decide
  have hdescent : baseEnd_232188 < baseStart_232188 := by decide
  rcases family_descends (prefixWord ++ tailWord_232188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232224 : List Nat := [2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_232224 : Nat := 118140960795 + 232224 * 2 ^ 59
def prefixEnd_232224 : Nat := 4983230072969 + 3 ^ 40 * 232224 * 2
def baseEnd_232224 : Nat := 70662240894699055544905

theorem tailTrace_232224 : CollatzResearch.WordTrace tailWord_232224 prefixEnd_232224 70662240894699055544905 := by
  unfold tailWord_232224
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234952555349791773379863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5646603407133055697839817 4234952555349791773379863)
  ·
    refine ⟨6352428833024687660069795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4234952555349791773379863 6352428833024687660069795)
    ·
      refine ⟨9528643249537031490104693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6352428833024687660069795 9528643249537031490104693)
      ·
        refine ⟨893310304644096702197315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9528643249537031490104693 893310304644096702197315)
        ·
          refine ⟨1339965456966145053295973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893310304644096702197315 1339965456966145053295973)
          ·
            refine ⟨251243523181152197492995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1339965456966145053295973 251243523181152197492995)
            ·
              refine ⟨376865284771728296239493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251243523181152197492995 376865284771728296239493)
              ·
                refine ⟨70662240894699055544905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376865284771728296239493 70662240894699055544905)
                ·
                  rfl

theorem cell19_232224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_232224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232224 prefixEnd_232224 := by exact prefixLift 232224
  have htrace : WordTrace (prefixWord ++ tailWord_232224) baseStart_232224 baseEnd_232224 := by
    simpa [prefixWord, tailWord_232224, baseEnd_232224] using wordTrace_append hprefix tailTrace_232224
  have hstable : (prefixWord ++ tailWord_232224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232224).length < 2 ^ (prefixWord ++ tailWord_232224).sum := by decide
  have hdescent : baseEnd_232224 < baseStart_232224 := by decide
  rcases family_descends (prefixWord ++ tailWord_232224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232243 : List Nat := [1, 1, 1, 2, 6, 2, 3, 3]
def baseStart_232243 : Nat := 118140960795 + 232243 * 2 ^ 59
def prefixEnd_232243 : Nat := 4983230072969 + 3 ^ 40 * 232243 * 2
def baseEnd_232243 : Nat := 70668022306512641122631

theorem tailTrace_232243 : CollatzResearch.WordTrace tailWord_232243 prefixEnd_232243 70668022306512641122631 := by
  unfold tailWord_232243
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470598097630749791701383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5647065398420499861134255 8470598097630749791701383)
  ·
    refine ⟨12705897146446124687552075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8470598097630749791701383 12705897146446124687552075)
    ·
      refine ⟨19058845719669187031328113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12705897146446124687552075 19058845719669187031328113)
      ·
        refine ⟨14294134289751890273496085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19058845719669187031328113 14294134289751890273496085)
        ·
          refine ⟨670037544832119856570129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14294134289751890273496085 670037544832119856570129)
          ·
            refine ⟨502528158624089892427597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670037544832119856570129 502528158624089892427597)
            ·
              refine ⟨188448059484033709660349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502528158624089892427597 188448059484033709660349)
              ·
                refine ⟨70668022306512641122631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188448059484033709660349 70668022306512641122631)
                ·
                  rfl

theorem cell19_232243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_232243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232243 prefixEnd_232243 := by exact prefixLift 232243
  have htrace : WordTrace (prefixWord ++ tailWord_232243) baseStart_232243 baseEnd_232243 := by
    simpa [prefixWord, tailWord_232243, baseEnd_232243] using wordTrace_append hprefix tailTrace_232243
  have hstable : (prefixWord ++ tailWord_232243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232243).length < 2 ^ (prefixWord ++ tailWord_232243).sum := by decide
  have hdescent : baseEnd_232243 < baseStart_232243 := by decide
  rcases family_descends (prefixWord ++ tailWord_232243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232260 : List Nat := [2, 3, 4, 2, 1, 1, 6]
def baseStart_232260 : Nat := 118140960795 + 232260 * 2 ^ 59
def prefixEnd_232260 : Nat := 4983230072969 + 3 ^ 40 * 232260 * 2
def baseEnd_232260 : Nat := 23557731716220546248269

theorem tailTrace_232260 : CollatzResearch.WordTrace tailWord_232260 prefixEnd_232260 23557731716220546248269 := by
  unfold tailWord_232260
  simp only [CollatzResearch.WordTrace]
  refine ⟨4235609069284580847535117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5647478759046107796713489 4235609069284580847535117)
  ·
    refine ⟨1588353400981717817825669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4235609069284580847535117 1588353400981717817825669)
    ·
      refine ⟨297816262684072090842313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1588353400981717817825669 297816262684072090842313)
      ·
        refine ⟨223362197013054068131735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297816262684072090842313 223362197013054068131735)
        ·
          refine ⟨335043295519581102197603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223362197013054068131735 335043295519581102197603)
          ·
            refine ⟨502564943279371653296405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335043295519581102197603 502564943279371653296405)
            ·
              refine ⟨23557731716220546248269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 502564943279371653296405 23557731716220546248269)
              ·
                rfl

theorem cell19_232260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_232260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232260 prefixEnd_232260 := by exact prefixLift 232260
  have htrace : WordTrace (prefixWord ++ tailWord_232260) baseStart_232260 baseEnd_232260 := by
    simpa [prefixWord, tailWord_232260, baseEnd_232260] using wordTrace_append hprefix tailTrace_232260
  have hstable : (prefixWord ++ tailWord_232260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232260).length < 2 ^ (prefixWord ++ tailWord_232260).sum := by decide
  have hdescent : baseEnd_232260 < baseStart_232260 := by decide
  rcases family_descends (prefixWord ++ tailWord_232260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232361 : List Nat := [1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_232361 : Nat := 118140960795 + 232361 * 2 ^ 59
def prefixEnd_232361 : Nat := 4983230072969 + 3 ^ 40 * 232361 * 2
def baseEnd_232361 : Nat := 70703927916723330500087

theorem tailTrace_232361 : CollatzResearch.WordTrace tailWord_232361 prefixEnd_232361 70703927916723330500087 := by
  unfold tailWord_232361
  simp only [CollatzResearch.WordTrace]
  refine ⟨8474901911203255944496937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5649934607468837296331291 8474901911203255944496937)
  ·
    refine ⟨6356176433402441958372703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8474901911203255944496937 6356176433402441958372703)
    ·
      refine ⟨9534264650103662937559055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6356176433402441958372703 9534264650103662937559055)
      ·
        refine ⟨14301396975155494406338583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9534264650103662937559055 14301396975155494406338583)
        ·
          refine ⟨21452095462733241609507875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14301396975155494406338583 21452095462733241609507875)
          ·
            refine ⟨32178143194099862414261813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21452095462733241609507875 32178143194099862414261813)
            ·
              refine ⟨3016700924446862101337045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32178143194099862414261813 3016700924446862101337045)
              ·
                refine ⟨70703927916723330500087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3016700924446862101337045 70703927916723330500087)
                ·
                  rfl

theorem cell19_232361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_232361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232361 prefixEnd_232361 := by exact prefixLift 232361
  have htrace : WordTrace (prefixWord ++ tailWord_232361) baseStart_232361 baseEnd_232361 := by
    simpa [prefixWord, tailWord_232361, baseEnd_232361] using wordTrace_append hprefix tailTrace_232361
  have hstable : (prefixWord ++ tailWord_232361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232361).length < 2 ^ (prefixWord ++ tailWord_232361).sum := by decide
  have hdescent : baseEnd_232361 < baseStart_232361 := by decide
  rcases family_descends (prefixWord ++ tailWord_232361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232374 : List Nat := [5, 1, 4, 1, 8]
def baseStart_232374 : Nat := 118140960795 + 232374 * 2 ^ 59
def prefixEnd_232374 : Nat := 4983230072969 + 3 ^ 40 * 232374 * 2
def baseEnd_232374 : Nat := 2618810504427524155969

theorem tailTrace_232374 : CollatzResearch.WordTrace tailWord_232374 prefixEnd_232374 2618810504427524155969 := by
  unfold tailWord_232374
  simp only [CollatzResearch.WordTrace]
  refine ⟨529711003759759947795011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5650250706770772776480117 529711003759759947795011)
  ·
    refine ⟨794566505639639921692517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 529711003759759947795011 794566505639639921692517)
    ·
      refine ⟨148981219807432485317347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 794566505639639921692517 148981219807432485317347)
      ·
        refine ⟨223471829711148727976021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148981219807432485317347 223471829711148727976021)
        ·
          refine ⟨2618810504427524155969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 223471829711148727976021 2618810504427524155969)
          ·
            rfl

theorem cell19_232374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 8].length) (baseStart_232374 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232374 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232374 prefixEnd_232374 := by exact prefixLift 232374
  have htrace : WordTrace (prefixWord ++ tailWord_232374) baseStart_232374 baseEnd_232374 := by
    simpa [prefixWord, tailWord_232374, baseEnd_232374] using wordTrace_append hprefix tailTrace_232374
  have hstable : (prefixWord ++ tailWord_232374).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232374).length < 2 ^ (prefixWord ++ tailWord_232374).sum := by decide
  have hdescent : baseEnd_232374 < baseStart_232374 := by decide
  rcases family_descends (prefixWord ++ tailWord_232374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232380 : List Nat := [2, 2, 2, 13]
def baseStart_232380 : Nat := 118140960795 + 232380 * 2 ^ 59
def prefixEnd_232380 : Nat := 4983230072969 + 3 ^ 40 * 232380 * 2
def baseEnd_232380 : Nat := 872959374426381679973

theorem tailTrace_232380 : CollatzResearch.WordTrace tailWord_232380 prefixEnd_232380 872959374426381679973 := by
  unfold tailWord_232380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237797449067211094719297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5650396598756281459625729 4237797449067211094719297)
  ·
    refine ⟨3178348086800408321039473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4237797449067211094719297 3178348086800408321039473)
    ·
      refine ⟨2383761065100306240779605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3178348086800408321039473 2383761065100306240779605)
      ·
        refine ⟨872959374426381679973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2383761065100306240779605 872959374426381679973)
        ·
          rfl

theorem cell19_232380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 13].length) (baseStart_232380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232380 prefixEnd_232380 := by exact prefixLift 232380
  have htrace : WordTrace (prefixWord ++ tailWord_232380) baseStart_232380 baseEnd_232380 := by
    simpa [prefixWord, tailWord_232380, baseEnd_232380] using wordTrace_append hprefix tailTrace_232380
  have hstable : (prefixWord ++ tailWord_232380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232380).length < 2 ^ (prefixWord ++ tailWord_232380).sum := by decide
  have hdescent : baseEnd_232380 < baseStart_232380 := by decide
  rcases family_descends (prefixWord ++ tailWord_232380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232471 : List Nat := [1, 1, 3, 5, 1, 1, 4, 3]
def baseStart_232471 : Nat := 118140960795 + 232471 * 2 ^ 59
def prefixEnd_232471 : Nat := 4983230072969 + 3 ^ 40 * 232471 * 2
def baseEnd_232471 : Nat := 70737399248275668055343

theorem tailTrace_232471 : CollatzResearch.WordTrace tailWord_232471 prefixEnd_232471 70737399248275668055343 := by
  unfold tailWord_232471
  simp only [CollatzResearch.WordTrace]
  refine ⟨8478913940804744731001267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5652609293869829820667511 8478913940804744731001267)
  ·
    refine ⟨12718370911207117096501901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8478913940804744731001267 12718370911207117096501901)
    ·
      refine ⟨4769389091702668911188213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12718370911207117096501901 4769389091702668911188213)
      ·
        refine ⟨447130227347125210423895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4769389091702668911188213 447130227347125210423895)
        ·
          refine ⟨670695341020687815635843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447130227347125210423895 670695341020687815635843)
          ·
            refine ⟨1006043011531031723453765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670695341020687815635843 1006043011531031723453765)
            ·
              refine ⟨188633064662068448147581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1006043011531031723453765 188633064662068448147581)
              ·
                refine ⟨70737399248275668055343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188633064662068448147581 70737399248275668055343)
                ·
                  rfl

theorem cell19_232471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_232471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232471 prefixEnd_232471 := by exact prefixLift 232471
  have htrace : WordTrace (prefixWord ++ tailWord_232471) baseStart_232471 baseEnd_232471 := by
    simpa [prefixWord, tailWord_232471, baseEnd_232471] using wordTrace_append hprefix tailTrace_232471
  have hstable : (prefixWord ++ tailWord_232471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232471).length < 2 ^ (prefixWord ++ tailWord_232471).sum := by decide
  have hdescent : baseEnd_232471 < baseStart_232471 := by decide
  rcases family_descends (prefixWord ++ tailWord_232471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232473 : List Nat := [1, 2, 1, 2, 1, 1, 8, 3]
def baseStart_232473 : Nat := 118140960795 + 232473 * 2 ^ 59
def prefixEnd_232473 : Nat := 4983230072969 + 3 ^ 40 * 232473 * 2
def baseEnd_232473 : Nat := 70738007817940256010893

theorem tailTrace_232473 : CollatzResearch.WordTrace tailWord_232473 prefixEnd_232473 70738007817940256010893 := by
  unfold tailWord_232473
  simp only [CollatzResearch.WordTrace]
  refine ⟨8478986886797499072574073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5652657924531666048382715 8478986886797499072574073)
  ·
    refine ⟨6359240165098124304430555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8478986886797499072574073 6359240165098124304430555)
    ·
      refine ⟨9538860247647186456645833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6359240165098124304430555 9538860247647186456645833)
      ·
        refine ⟨7154145185735389842484375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9538860247647186456645833 7154145185735389842484375)
        ·
          refine ⟨10731217778603084763726563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154145185735389842484375 10731217778603084763726563)
          ·
            refine ⟨16096826667904627145589845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731217778603084763726563 16096826667904627145589845)
            ·
              refine ⟨188634687514507349362381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 16096826667904627145589845 188634687514507349362381)
              ·
                refine ⟨70738007817940256010893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188634687514507349362381 70738007817940256010893)
                ·
                  rfl

theorem cell19_232473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_232473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232473 prefixEnd_232473 := by exact prefixLift 232473
  have htrace : WordTrace (prefixWord ++ tailWord_232473) baseStart_232473 baseEnd_232473 := by
    simpa [prefixWord, tailWord_232473, baseEnd_232473] using wordTrace_append hprefix tailTrace_232473
  have hstable : (prefixWord ++ tailWord_232473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232473).length < 2 ^ (prefixWord ++ tailWord_232473).sum := by decide
  have hdescent : baseEnd_232473 < baseStart_232473 := by decide
  rcases family_descends (prefixWord ++ tailWord_232473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232490 : List Nat := [3, 1, 4, 1, 3, 2, 5]
def baseStart_232490 : Nat := 118140960795 + 232490 * 2 ^ 59
def prefixEnd_232490 : Nat := 4983230072969 + 3 ^ 40 * 232490 * 2
def baseEnd_232490 : Nat := 23581060220029751211023

theorem tailTrace_232490 : CollatzResearch.WordTrace tailWord_232490 prefixEnd_232490 23581060220029751211023 := by
  unfold tailWord_232490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119901731933977743985731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5653071285157273983961949 2119901731933977743985731)
  ·
    refine ⟨3179852597900966615978597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119901731933977743985731 3179852597900966615978597)
    ·
      refine ⟨596222362106431240495987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3179852597900966615978597 596222362106431240495987)
      ·
        refine ⟨894333543159646860743981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596222362106431240495987 894333543159646860743981)
        ·
          refine ⟨335375078684867572778993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894333543159646860743981 335375078684867572778993)
          ·
            refine ⟨251531309013650679584245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335375078684867572778993 251531309013650679584245)
            ·
              refine ⟨23581060220029751211023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251531309013650679584245 23581060220029751211023)
              ·
                rfl

theorem cell19_232490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_232490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232490 prefixEnd_232490 := by exact prefixLift 232490
  have htrace : WordTrace (prefixWord ++ tailWord_232490) baseStart_232490 baseEnd_232490 := by
    simpa [prefixWord, tailWord_232490, baseEnd_232490] using wordTrace_append hprefix tailTrace_232490
  have hstable : (prefixWord ++ tailWord_232490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232490).length < 2 ^ (prefixWord ++ tailWord_232490).sum := by decide
  have hdescent : baseEnd_232490 < baseStart_232490 := by decide
  rcases family_descends (prefixWord ++ tailWord_232490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232530 : List Nat := [3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_232530 : Nat := 118140960795 + 232530 * 2 ^ 59
def prefixEnd_232530 : Nat := 4983230072969 + 3 ^ 40 * 232530 * 2
def baseEnd_232530 : Nat := 70755352053381012744071

theorem tailTrace_232530 : CollatzResearch.WordTrace tailWord_232530 prefixEnd_232530 70755352053381012744071 := by
  unfold tailWord_232530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120266461897749451849761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5654043898393998538266029 2120266461897749451849761)
  ·
    refine ⟨1590199846423312088887321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2120266461897749451849761 1590199846423312088887321)
    ·
      refine ⟨1192649884817484066665491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1590199846423312088887321 1192649884817484066665491)
      ·
        refine ⟨1788974827226226099998237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192649884817484066665491 1788974827226226099998237)
        ·
          refine ⟨670865560209834787499339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1788974827226226099998237 670865560209834787499339)
          ·
            refine ⟨1006298340314752181249009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670865560209834787499339 1006298340314752181249009)
            ·
              refine ⟨754723755236064135936757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006298340314752181249009 754723755236064135936757)
              ·
                refine ⟨70755352053381012744071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754723755236064135936757 70755352053381012744071)
                ·
                  rfl

theorem cell19_232530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_232530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232530 prefixEnd_232530 := by exact prefixLift 232530
  have htrace : WordTrace (prefixWord ++ tailWord_232530) baseStart_232530 baseEnd_232530 := by
    simpa [prefixWord, tailWord_232530, baseEnd_232530] using wordTrace_append hprefix tailTrace_232530
  have hstable : (prefixWord ++ tailWord_232530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232530).length < 2 ^ (prefixWord ++ tailWord_232530).sum := by decide
  have hdescent : baseEnd_232530 < baseStart_232530 := by decide
  rcases family_descends (prefixWord ++ tailWord_232530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232551 : List Nat := [1, 1, 5, 1, 1, 10]
def baseStart_232551 : Nat := 118140960795 + 232551 * 2 ^ 59
def prefixEnd_232551 : Nat := 4983230072969 + 3 ^ 40 * 232551 * 2
def baseEnd_232551 : Nat := 7862415781651020697483

theorem tailTrace_232551 : CollatzResearch.WordTrace tailWord_232551 prefixEnd_232551 7862415781651020697483 := by
  unfold tailWord_232551
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481831780514918393913507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5654554520343278929275671 8481831780514918393913507)
  ·
    refine ⟨12722747670772377590870261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8481831780514918393913507 12722747670772377590870261)
    ·
      refine ⟨1192757594134910399144087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12722747670772377590870261 1192757594134910399144087)
      ·
        refine ⟨1789136391202365598716131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192757594134910399144087 1789136391202365598716131)
        ·
          refine ⟨2683704586803548398074197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789136391202365598716131 2683704586803548398074197)
          ·
            refine ⟨7862415781651020697483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2683704586803548398074197 7862415781651020697483)
            ·
              rfl

theorem cell19_232551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_232551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232551 prefixEnd_232551 := by exact prefixLift 232551
  have htrace : WordTrace (prefixWord ++ tailWord_232551) baseStart_232551 baseEnd_232551 := by
    simpa [prefixWord, tailWord_232551, baseEnd_232551] using wordTrace_append hprefix tailTrace_232551
  have hstable : (prefixWord ++ tailWord_232551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232551).length < 2 ^ (prefixWord ++ tailWord_232551).sum := by decide
  have hdescent : baseEnd_232551 < baseStart_232551 := by decide
  rcases family_descends (prefixWord ++ tailWord_232551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232608 : List Nat := [2, 1, 1, 4, 2, 1, 8]
def baseStart_232608 : Nat := 118140960795 + 232608 * 2 ^ 59
def prefixEnd_232608 : Nat := 4983230072969 + 3 ^ 40 * 232608 * 2
def baseEnd_232608 : Nat := 23593028756766647670175

theorem tailTrace_232608 : CollatzResearch.WordTrace tailWord_232608 prefixEnd_232608 23593028756766647670175 := by
  unfold tailWord_232608
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241955370654208564369239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5655940494205611419158985 4241955370654208564369239)
  ·
    refine ⟨6362933055981312846553859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241955370654208564369239 6362933055981312846553859)
    ·
      refine ⟨9544399583971969269830789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6362933055981312846553859 9544399583971969269830789)
      ·
        refine ⟨1789574921994744238093273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9544399583971969269830789 1789574921994744238093273)
        ·
          refine ⟨1342181191496058178569955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789574921994744238093273 1342181191496058178569955)
          ·
            refine ⟨2013271787244087267854933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342181191496058178569955 2013271787244087267854933)
            ·
              refine ⟨23593028756766647670175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2013271787244087267854933 23593028756766647670175)
              ·
                rfl

theorem cell19_232608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_232608 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232608 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232608 prefixEnd_232608 := by exact prefixLift 232608
  have htrace : WordTrace (prefixWord ++ tailWord_232608) baseStart_232608 baseEnd_232608 := by
    simpa [prefixWord, tailWord_232608, baseEnd_232608] using wordTrace_append hprefix tailTrace_232608
  have hstable : (prefixWord ++ tailWord_232608).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232608).length < 2 ^ (prefixWord ++ tailWord_232608).sum := by decide
  have hdescent : baseEnd_232608 < baseStart_232608 := by decide
  rcases family_descends (prefixWord ++ tailWord_232608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232640 : List Nat := [2, 1, 1, 2, 7, 1, 2, 3]
def baseStart_232640 : Nat := 118140960795 + 232640 * 2 ^ 59
def prefixEnd_232640 : Nat := 4983230072969 + 3 ^ 40 * 232640 * 2
def baseEnd_232640 : Nat := 70788823384933350299327

theorem tailTrace_232640 : CollatzResearch.WordTrace tailWord_232640 prefixEnd_232640 70788823384933350299327 := by
  unfold tailWord_232640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242538938596243296951687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5656718584794991062602249 4242538938596243296951687)
  ·
    refine ⟨6363808407894364945427531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4242538938596243296951687 6363808407894364945427531)
    ·
      refine ⟨9545712611841547418141297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6363808407894364945427531 9545712611841547418141297)
      ·
        refine ⟨7159284458881160563605973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9545712611841547418141297 7159284458881160563605973)
        ·
          refine ⟨167795729505027200709515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7159284458881160563605973 167795729505027200709515)
          ·
            refine ⟨251693594257540801064273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167795729505027200709515 251693594257540801064273)
            ·
              refine ⟨188770195693155600798205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251693594257540801064273 188770195693155600798205)
              ·
                refine ⟨70788823384933350299327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188770195693155600798205 70788823384933350299327)
                ·
                  rfl

theorem cell19_232640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_232640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232640 prefixEnd_232640 := by exact prefixLift 232640
  have htrace : WordTrace (prefixWord ++ tailWord_232640) baseStart_232640 baseEnd_232640 := by
    simpa [prefixWord, tailWord_232640, baseEnd_232640] using wordTrace_append hprefix tailTrace_232640
  have hstable : (prefixWord ++ tailWord_232640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232640).length < 2 ^ (prefixWord ++ tailWord_232640).sum := by decide
  have hdescent : baseEnd_232640 < baseStart_232640 := by decide
  rcases family_descends (prefixWord ++ tailWord_232640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232682 : List Nat := [3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_232682 : Nat := 118140960795 + 232682 * 2 ^ 59
def prefixEnd_232682 : Nat := 4983230072969 + 3 ^ 40 * 232682 * 2
def baseEnd_232682 : Nat := 70801603347889697365879

theorem tailTrace_232682 : CollatzResearch.WordTrace tailWord_232682 prefixEnd_232682 70801603347889697365879 := by
  unfold tailWord_232682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121652435760081941733075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5657739828693551844621533 2121652435760081941733075)
  ·
    refine ⟨3182478653640122912599613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2121652435760081941733075 3182478653640122912599613)
    ·
      refine ⟨1193429495115046092224855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3182478653640122912599613 1193429495115046092224855)
      ·
        refine ⟨1790144242672569138337283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193429495115046092224855 1790144242672569138337283)
        ·
          refine ⟨2685216364008853707505925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790144242672569138337283 2685216364008853707505925)
          ·
            refine ⟨503478068251660070157361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2685216364008853707505925 503478068251660070157361)
            ·
              refine ⟨377608551188745052618021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503478068251660070157361 377608551188745052618021)
              ·
                refine ⟨70801603347889697365879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377608551188745052618021 70801603347889697365879)
                ·
                  rfl

theorem cell19_232682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_232682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232682 prefixEnd_232682 := by exact prefixLift 232682
  have htrace : WordTrace (prefixWord ++ tailWord_232682) baseStart_232682 baseEnd_232682 := by
    simpa [prefixWord, tailWord_232682, baseEnd_232682] using wordTrace_append hprefix tailTrace_232682
  have hstable : (prefixWord ++ tailWord_232682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232682).length < 2 ^ (prefixWord ++ tailWord_232682).sum := by decide
  have hdescent : baseEnd_232682 < baseStart_232682 := by decide
  rcases family_descends (prefixWord ++ tailWord_232682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232684 : List Nat := [2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_232684 : Nat := 118140960795 + 232684 * 2 ^ 59
def prefixEnd_232684 : Nat := 4983230072969 + 3 ^ 40 * 232684 * 2
def baseEnd_232684 : Nat := 70802211917554285321429

theorem tailTrace_232684 : CollatzResearch.WordTrace tailWord_232684 prefixEnd_232684 70802211917554285321429 := by
  unfold tailWord_232684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243341344516541054252553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5657788459355388072336737 4243341344516541054252553)
  ·
    refine ⟨3182506008387405790689415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4243341344516541054252553 3182506008387405790689415)
    ·
      refine ⟨4773759012581108686034123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182506008387405790689415 4773759012581108686034123)
      ·
        refine ⟨7160638518871663029051185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4773759012581108686034123 7160638518871663029051185)
        ·
          refine ⟨5370478889153747271788389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7160638518871663029051185 5370478889153747271788389)
          ·
            refine ⟨1006964791716327613460323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5370478889153747271788389 1006964791716327613460323)
            ·
              refine ⟨1510447187574491420190485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006964791716327613460323 1510447187574491420190485)
              ·
                refine ⟨70802211917554285321429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1510447187574491420190485 70802211917554285321429)
                ·
                  rfl

theorem cell19_232684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_232684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232684 prefixEnd_232684 := by exact prefixLift 232684
  have htrace : WordTrace (prefixWord ++ tailWord_232684) baseStart_232684 baseEnd_232684 := by
    simpa [prefixWord, tailWord_232684, baseEnd_232684] using wordTrace_append hprefix tailTrace_232684
  have hstable : (prefixWord ++ tailWord_232684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232684).length < 2 ^ (prefixWord ++ tailWord_232684).sum := by decide
  have hdescent : baseEnd_232684 < baseStart_232684 := by decide
  rcases family_descends (prefixWord ++ tailWord_232684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232703 : List Nat := [1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_232703 : Nat := 118140960795 + 232703 * 2 ^ 59
def prefixEnd_232703 : Nat := 4983230072969 + 3 ^ 40 * 232703 * 2
def baseEnd_232703 : Nat := 70807993329367870899155

theorem tailTrace_232703 : CollatzResearch.WordTrace tailWord_232703 prefixEnd_232703 70807993329367870899155 := by
  unfold tailWord_232703
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487375675964248353446763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5658250450642832235631175 8487375675964248353446763)
  ·
    refine ⟨12731063513946372530170145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8487375675964248353446763 12731063513946372530170145)
    ·
      refine ⟨9548297635459779397627609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12731063513946372530170145 9548297635459779397627609)
      ·
        refine ⟨7161223226594834548220707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9548297635459779397627609 7161223226594834548220707)
        ·
          refine ⟨10741834839892251822331061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161223226594834548220707 10741834839892251822331061)
          ·
            refine ⟨1007047016239898608343537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10741834839892251822331061 1007047016239898608343537)
            ·
              refine ⟨755285262179923956257653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007047016239898608343537 755285262179923956257653)
              ·
                refine ⟨70807993329367870899155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 755285262179923956257653 70807993329367870899155)
                ·
                  rfl

theorem cell19_232703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_232703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232703 prefixEnd_232703 := by exact prefixLift 232703
  have htrace : WordTrace (prefixWord ++ tailWord_232703) baseStart_232703 baseEnd_232703 := by
    simpa [prefixWord, tailWord_232703, baseEnd_232703] using wordTrace_append hprefix tailTrace_232703
  have hstable : (prefixWord ++ tailWord_232703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232703).length < 2 ^ (prefixWord ++ tailWord_232703).sum := by decide
  have hdescent : baseEnd_232703 < baseStart_232703 := by decide
  rcases family_descends (prefixWord ++ tailWord_232703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232739 : List Nat := [1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_232739 : Nat := 118140960795 + 232739 * 2 ^ 59
def prefixEnd_232739 : Nat := 4983230072969 + 3 ^ 40 * 232739 * 2
def baseEnd_232739 : Nat := 70818947583330454099057

theorem tailTrace_232739 : CollatzResearch.WordTrace tailWord_232739 prefixEnd_232739 70818947583330454099057 := by
  unfold tailWord_232739
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488688703833826501757271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5659125802555884334504847 8488688703833826501757271)
  ·
    refine ⟨12733033055750739752635907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8488688703833826501757271 12733033055750739752635907)
    ·
      refine ⟨19099549583626109628953861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12733033055750739752635907 19099549583626109628953861)
      ·
        refine ⟨3581165546929895555428849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19099549583626109628953861 3581165546929895555428849)
        ·
          refine ⟨2685874160197421666571637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3581165546929895555428849 2685874160197421666571637)
          ·
            refine ⟨251800702518508281241091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2685874160197421666571637 251800702518508281241091)
            ·
              refine ⟨377701053777762421861637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251800702518508281241091 377701053777762421861637)
              ·
                refine ⟨70818947583330454099057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377701053777762421861637 70818947583330454099057)
                ·
                  rfl

theorem cell19_232739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_232739 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232739 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232739 prefixEnd_232739 := by exact prefixLift 232739
  have htrace : WordTrace (prefixWord ++ tailWord_232739) baseStart_232739 baseEnd_232739 := by
    simpa [prefixWord, tailWord_232739, baseEnd_232739] using wordTrace_append hprefix tailTrace_232739
  have hstable : (prefixWord ++ tailWord_232739).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232739).length < 2 ^ (prefixWord ++ tailWord_232739).sum := by decide
  have hdescent : baseEnd_232739 < baseStart_232739 := by decide
  rcases family_descends (prefixWord ++ tailWord_232739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232756 : List Nat := [2, 5, 1, 1, 1, 1, 5, 3]
def baseStart_232756 : Nat := 118140960795 + 232756 * 2 ^ 59
def prefixEnd_232756 : Nat := 4983230072969 + 3 ^ 40 * 232756 * 2
def baseEnd_232756 : Nat := 70824120425479451721233

theorem tailTrace_232756 : CollatzResearch.WordTrace tailWord_232756 prefixEnd_232756 70824120425479451721233 := by
  unfold tailWord_232756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244654372386119202563061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5659539163181492270084081 4244654372386119202563061)
  ·
    refine ⟨397936347411198675240287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4244654372386119202563061 397936347411198675240287)
    ·
      refine ⟨596904521116798012860431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397936347411198675240287 596904521116798012860431)
      ·
        refine ⟨895356781675197019290647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596904521116798012860431 895356781675197019290647)
        ·
          refine ⟨1343035172512795528935971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895356781675197019290647 1343035172512795528935971)
          ·
            refine ⟨2014552758769193293403957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343035172512795528935971 2014552758769193293403957)
            ·
              refine ⟨188864321134611871256621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2014552758769193293403957 188864321134611871256621)
              ·
                refine ⟨70824120425479451721233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188864321134611871256621 70824120425479451721233)
                ·
                  rfl

theorem cell19_232756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_232756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232756 prefixEnd_232756 := by exact prefixLift 232756
  have htrace : WordTrace (prefixWord ++ tailWord_232756) baseStart_232756 baseEnd_232756 := by
    simpa [prefixWord, tailWord_232756, baseEnd_232756] using wordTrace_append hprefix tailTrace_232756
  have hstable : (prefixWord ++ tailWord_232756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232756).length < 2 ^ (prefixWord ++ tailWord_232756).sum := by decide
  have hdescent : baseEnd_232756 < baseStart_232756 := by decide
  rcases family_descends (prefixWord ++ tailWord_232756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232813 : List Nat := [1, 5, 1, 1, 1, 5, 2, 3]
def baseStart_232813 : Nat := 118140960795 + 232813 * 2 ^ 59
def prefixEnd_232813 : Nat := 4983230072969 + 3 ^ 40 * 232813 * 2
def baseEnd_232813 : Nat := 70841464660920208454411

theorem tailTrace_232813 : CollatzResearch.WordTrace tailWord_232813 prefixEnd_232813 70841464660920208454411 := by
  unfold tailWord_232813
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491387705565737139951093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5660925137043824759967395 8491387705565737139951093)
  ·
    refine ⟨796067597396787856870415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8491387705565737139951093 796067597396787856870415)
    ·
      refine ⟨1194101396095181785305623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796067597396787856870415 1194101396095181785305623)
      ·
        refine ⟨1791152094142772677958435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194101396095181785305623 1791152094142772677958435)
        ·
          refine ⟨2686728141214159016937653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791152094142772677958435 2686728141214159016937653)
          ·
            refine ⟨251880763238827407837905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2686728141214159016937653 251880763238827407837905)
            ·
              refine ⟨188910572429120555878429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251880763238827407837905 188910572429120555878429)
              ·
                refine ⟨70841464660920208454411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188910572429120555878429 70841464660920208454411)
                ·
                  rfl

theorem cell19_232813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_232813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232813 prefixEnd_232813 := by exact prefixLift 232813
  have htrace : WordTrace (prefixWord ++ tailWord_232813) baseStart_232813 baseEnd_232813 := by
    simpa [prefixWord, tailWord_232813, baseEnd_232813] using wordTrace_append hprefix tailTrace_232813
  have hstable : (prefixWord ++ tailWord_232813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232813).length < 2 ^ (prefixWord ++ tailWord_232813).sum := by decide
  have hdescent : baseEnd_232813 < baseStart_232813 := by decide
  rcases family_descends (prefixWord ++ tailWord_232813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232830 : List Nat := [4, 2, 3, 2, 1, 2, 5]
def baseStart_232830 : Nat := 118140960795 + 232830 * 2 ^ 59
def prefixEnd_232830 : Nat := 4983230072969 + 3 ^ 40 * 232830 * 2
def baseEnd_232830 : Nat := 23615545834356402025529

theorem tailTrace_232830 : CollatzResearch.WordTrace tailWord_232830 prefixEnd_232830 23615545834356402025529 := by
  unfold tailWord_232830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061500968313018630414993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5661338497669432695546629 1061500968313018630414993)
  ·
    refine ⟨796125726234763972811245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1061500968313018630414993 796125726234763972811245)
    ·
      refine ⟨298547147338036489804217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 796125726234763972811245 298547147338036489804217)
      ·
        refine ⟨223910360503527367353163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298547147338036489804217 223910360503527367353163)
        ·
          refine ⟨335865540755291051029745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223910360503527367353163 335865540755291051029745)
          ·
            refine ⟨251899155566468288272309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335865540755291051029745 251899155566468288272309)
            ·
              refine ⟨23615545834356402025529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251899155566468288272309 23615545834356402025529)
              ·
                rfl

theorem cell19_232830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_232830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232830 prefixEnd_232830 := by exact prefixLift 232830
  have htrace : WordTrace (prefixWord ++ tailWord_232830) baseStart_232830 baseEnd_232830 := by
    simpa [prefixWord, tailWord_232830, baseEnd_232830] using wordTrace_append hprefix tailTrace_232830
  have hstable : (prefixWord ++ tailWord_232830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232830).length < 2 ^ (prefixWord ++ tailWord_232830).sum := by decide
  have hdescent : baseEnd_232830 < baseStart_232830 := by decide
  rcases family_descends (prefixWord ++ tailWord_232830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232836 : List Nat := [2, 3, 2, 1, 1, 3, 7]
def baseStart_232836 : Nat := 118140960795 + 232836 * 2 ^ 59
def prefixEnd_232836 : Nat := 4983230072969 + 3 ^ 40 * 232836 * 2
def baseEnd_232836 : Nat := 23616154404020989981079

theorem tailTrace_232836 : CollatzResearch.WordTrace tailWord_232836 prefixEnd_232836 23616154404020989981079 := by
  unfold tailWord_232836
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246113292241206034019181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5661484389654941378692241 4246113292241206034019181)
  ·
    refine ⟨1592292484590452262757193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4246113292241206034019181 1592292484590452262757193)
    ·
      refine ⟨1194219363442839197067895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1592292484590452262757193 1194219363442839197067895)
      ·
        refine ⟨1791329045164258795601843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194219363442839197067895 1791329045164258795601843)
        ·
          refine ⟨2686993567746388193402765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791329045164258795601843 2686993567746388193402765)
          ·
            refine ⟨1007622587904895572526037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2686993567746388193402765 1007622587904895572526037)
            ·
              refine ⟨23616154404020989981079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1007622587904895572526037 23616154404020989981079)
              ·
                rfl

theorem cell19_232836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_232836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232836 prefixEnd_232836 := by exact prefixLift 232836
  have htrace : WordTrace (prefixWord ++ tailWord_232836) baseStart_232836 baseEnd_232836 := by
    simpa [prefixWord, tailWord_232836, baseEnd_232836] using wordTrace_append hprefix tailTrace_232836
  have hstable : (prefixWord ++ tailWord_232836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232836).length < 2 ^ (prefixWord ++ tailWord_232836).sum := by decide
  have hdescent : baseEnd_232836 < baseStart_232836 := by decide
  rcases family_descends (prefixWord ++ tailWord_232836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232929 : List Nat := [1, 2, 3, 1, 2, 4, 3, 3]
def baseStart_232929 : Nat := 118140960795 + 232929 * 2 ^ 59
def prefixEnd_232929 : Nat := 4983230072969 + 3 ^ 40 * 232929 * 2
def baseEnd_232929 : Nat := 70876761701466309876317

theorem tailTrace_232929 : CollatzResearch.WordTrace tailWord_232929 prefixEnd_232929 70876761701466309876317 := by
  unfold tailWord_232929
  simp only [CollatzResearch.WordTrace]
  refine ⟨8495618573145488951173841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5663745715430325967449227 8495618573145488951173841)
  ·
    refine ⟨6371713929859116713380381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8495618573145488951173841 6371713929859116713380381)
    ·
      refine ⟨2389392723697168767517643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6371713929859116713380381 2389392723697168767517643)
      ·
        refine ⟨3584089085545753151276465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389392723697168767517643 3584089085545753151276465)
        ·
          refine ⟨2688066814159314863457349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3584089085545753151276465 2688066814159314863457349)
          ·
            refine ⟨504012527654871536898253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2688066814159314863457349 504012527654871536898253)
            ·
              refine ⟨189004697870576826336845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504012527654871536898253 189004697870576826336845)
              ·
                refine ⟨70876761701466309876317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189004697870576826336845 70876761701466309876317)
                ·
                  rfl

theorem cell19_232929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_232929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232929 prefixEnd_232929 := by exact prefixLift 232929
  have htrace : WordTrace (prefixWord ++ tailWord_232929) baseStart_232929 baseEnd_232929 := by
    simpa [prefixWord, tailWord_232929, baseEnd_232929] using wordTrace_append hprefix tailTrace_232929
  have hstable : (prefixWord ++ tailWord_232929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232929).length < 2 ^ (prefixWord ++ tailWord_232929).sum := by decide
  have hdescent : baseEnd_232929 < baseStart_232929 := by decide
  rcases family_descends (prefixWord ++ tailWord_232929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232980 : List Nat := [2, 4, 3, 1, 3, 1, 2, 3]
def baseStart_232980 : Nat := 118140960795 + 232980 * 2 ^ 59
def prefixEnd_232980 : Nat := 4983230072969 + 3 ^ 40 * 232980 * 2
def baseEnd_232980 : Nat := 70892280227913302742845

theorem tailTrace_232980 : CollatzResearch.WordTrace tailWord_232980 prefixEnd_232980 70892280227913302742845 := by
  unfold tailWord_232980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248739347980362330640197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5664985797307149774186929 4248739347980362330640197)
  ·
    refine ⟨796638627746317936995037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4248739347980362330640197 796638627746317936995037)
    ·
      refine ⟨298739485404869226373139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 796638627746317936995037 298739485404869226373139)
      ·
        refine ⟨448109228107303839559709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298739485404869226373139 448109228107303839559709)
        ·
          refine ⟨168040960540238939834891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448109228107303839559709 168040960540238939834891)
          ·
            refine ⟨252061440810358409752337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168040960540238939834891 252061440810358409752337)
            ·
              refine ⟨189046080607768807314253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252061440810358409752337 189046080607768807314253)
              ·
                refine ⟨70892280227913302742845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189046080607768807314253 70892280227913302742845)
                ·
                  rfl

theorem cell19_232980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_232980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232980 prefixEnd_232980 := by exact prefixLift 232980
  have htrace : WordTrace (prefixWord ++ tailWord_232980) baseStart_232980 baseEnd_232980 := by
    simpa [prefixWord, tailWord_232980, baseEnd_232980] using wordTrace_append hprefix tailTrace_232980
  have hstable : (prefixWord ++ tailWord_232980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232980).length < 2 ^ (prefixWord ++ tailWord_232980).sum := by decide
  have hdescent : baseEnd_232980 < baseStart_232980 := by decide
  rcases family_descends (prefixWord ++ tailWord_232980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232984 : List Nat := [2, 1, 2, 3, 4, 2, 2, 3]
def baseStart_232984 : Nat := 118140960795 + 232984 * 2 ^ 59
def prefixEnd_232984 : Nat := 4983230072969 + 3 ^ 40 * 232984 * 2
def baseEnd_232984 : Nat := 70893497367242478653945

theorem tailTrace_232984 : CollatzResearch.WordTrace tailWord_232984 prefixEnd_232984 70893497367242478653945 := by
  unfold tailWord_232984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248812293973116672213003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5665083058630822229617337 4248812293973116672213003)
  ·
    refine ⟨6373218440959675008319505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4248812293973116672213003 6373218440959675008319505)
    ·
      refine ⟨4779913830719756256239629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6373218440959675008319505 4779913830719756256239629)
      ·
        refine ⟨1792467686519908596089861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4779913830719756256239629 1792467686519908596089861)
        ·
          refine ⟨336087691222482861766849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1792467686519908596089861 336087691222482861766849)
          ·
            refine ⟨252065768416862146325137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336087691222482861766849 252065768416862146325137)
            ·
              refine ⟨189049326312646609743853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252065768416862146325137 189049326312646609743853)
              ·
                refine ⟨70893497367242478653945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189049326312646609743853 70893497367242478653945)
                ·
                  rfl

theorem cell19_232984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_232984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232984 prefixEnd_232984 := by exact prefixLift 232984
  have htrace : WordTrace (prefixWord ++ tailWord_232984) baseStart_232984 baseEnd_232984 := by
    simpa [prefixWord, tailWord_232984, baseEnd_232984] using wordTrace_append hprefix tailTrace_232984
  have hstable : (prefixWord ++ tailWord_232984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232984).length < 2 ^ (prefixWord ++ tailWord_232984).sum := by decide
  have hdescent : baseEnd_232984 < baseStart_232984 := by decide
  rcases family_descends (prefixWord ++ tailWord_232984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232988 : List Nat := [2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_232988 : Nat := 118140960795 + 232988 * 2 ^ 59
def prefixEnd_232988 : Nat := 4983230072969 + 3 ^ 40 * 232988 * 2
def baseEnd_232988 : Nat := 70894714506571654565045

theorem tailTrace_232988 : CollatzResearch.WordTrace tailWord_232988 prefixEnd_232988 70894714506571654565045 := by
  unfold tailWord_232988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248885239965871013785809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5665180319954494685047745 4248885239965871013785809)
  ·
    refine ⟨3186663929974403260339357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4248885239965871013785809 3186663929974403260339357)
    ·
      refine ⟨1194998973740401222627259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3186663929974403260339357 1194998973740401222627259)
      ·
        refine ⟨1792498460610601833940889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194998973740401222627259 1792498460610601833940889)
        ·
          refine ⟨1344373845457951375455667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1792498460610601833940889 1344373845457951375455667)
          ·
            refine ⟨2016560768186927063183501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344373845457951375455667 2016560768186927063183501)
            ·
              refine ⟨756210288070097648693813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2016560768186927063183501 756210288070097648693813)
              ·
                refine ⟨70894714506571654565045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 756210288070097648693813 70894714506571654565045)
                ·
                  rfl

theorem cell19_232988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_232988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_232988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_232988 prefixEnd_232988 := by exact prefixLift 232988
  have htrace : WordTrace (prefixWord ++ tailWord_232988) baseStart_232988 baseEnd_232988 := by
    simpa [prefixWord, tailWord_232988, baseEnd_232988] using wordTrace_append hprefix tailTrace_232988
  have hstable : (prefixWord ++ tailWord_232988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232988).length < 2 ^ (prefixWord ++ tailWord_232988).sum := by decide
  have hdescent : baseEnd_232988 < baseStart_232988 := by decide
  rcases family_descends (prefixWord ++ tailWord_232988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233064 : List Nat := [2, 1, 4, 3, 1, 8]
def baseStart_233064 : Nat := 118140960795 + 233064 * 2 ^ 59
def prefixEnd_233064 : Nat := 4983230072969 + 3 ^ 40 * 233064 * 2
def baseEnd_233064 : Nat := 7879760017091777430661

theorem tailTrace_233064 : CollatzResearch.WordTrace tailWord_233064 prefixEnd_233064 7879760017091777430661 := by
  unfold tailWord_233064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250271213828203503669123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5667028285104271338225497 4250271213828203503669123)
  ·
    refine ⟨6375406820742305255503685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250271213828203503669123 6375406820742305255503685)
    ·
      refine ⟨1195388778889182235406941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6375406820742305255503685 1195388778889182235406941)
      ·
        refine ⟨448270792083443338277603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1195388778889182235406941 448270792083443338277603)
        ·
          refine ⟨672406188125165007416405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448270792083443338277603 672406188125165007416405)
          ·
            refine ⟨7879760017091777430661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 672406188125165007416405 7879760017091777430661)
            ·
              rfl

theorem cell19_233064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_233064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233064 prefixEnd_233064 := by exact prefixLift 233064
  have htrace : WordTrace (prefixWord ++ tailWord_233064) baseStart_233064 baseEnd_233064 := by
    simpa [prefixWord, tailWord_233064, baseEnd_233064] using wordTrace_append hprefix tailTrace_233064
  have hstable : (prefixWord ++ tailWord_233064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233064).length < 2 ^ (prefixWord ++ tailWord_233064).sum := by decide
  have hdescent : baseEnd_233064 < baseStart_233064 := by decide
  rcases family_descends (prefixWord ++ tailWord_233064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233104 : List Nat := [2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_233104 : Nat := 118140960795 + 233104 * 2 ^ 59
def prefixEnd_233104 : Nat := 4983230072969 + 3 ^ 40 * 233104 * 2
def baseEnd_233104 : Nat := 70930011547117755986951

theorem tailTrace_233104 : CollatzResearch.WordTrace tailWord_233104 prefixEnd_233104 70930011547117755986951 := by
  unfold tailWord_233104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251000673755746919397183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5668000898340995892529577 4251000673755746919397183)
  ·
    refine ⟨6376501010633620379095775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4251000673755746919397183 6376501010633620379095775)
    ·
      refine ⟨9564751515950430568643663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376501010633620379095775 9564751515950430568643663)
      ·
        refine ⟨14347127273925645852965495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564751515950430568643663 14347127273925645852965495)
        ·
          refine ⟨21520690910888468779448243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14347127273925645852965495 21520690910888468779448243)
          ·
            refine ⟨32281036366332703169172365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21520690910888468779448243 32281036366332703169172365)
            ·
              refine ⟨12105388637374763688439637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32281036366332703169172365 12105388637374763688439637)
              ·
                refine ⟨70930011547117755986951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12105388637374763688439637 70930011547117755986951)
                ·
                  rfl

theorem cell19_233104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_233104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233104 prefixEnd_233104 := by exact prefixLift 233104
  have htrace : WordTrace (prefixWord ++ tailWord_233104) baseStart_233104 baseEnd_233104 := by
    simpa [prefixWord, tailWord_233104, baseEnd_233104] using wordTrace_append hprefix tailTrace_233104
  have hstable : (prefixWord ++ tailWord_233104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233104).length < 2 ^ (prefixWord ++ tailWord_233104).sum := by decide
  have hdescent : baseEnd_233104 < baseStart_233104 := by decide
  rcases family_descends (prefixWord ++ tailWord_233104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233119 : List Nat := [1, 1, 2, 7, 1, 1, 6]
def baseStart_233119 : Nat := 118140960795 + 233119 * 2 ^ 59
def prefixEnd_233119 : Nat := 4983230072969 + 3 ^ 40 * 233119 * 2
def baseEnd_233119 : Nat := 23644858606534055217859

theorem tailTrace_233119 : CollatzResearch.WordTrace tailWord_233119 prefixEnd_233119 23644858606534055217859 := by
  unfold tailWord_233119
  simp only [CollatzResearch.WordTrace]
  refine ⟨8502548442457151400590411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5668365628304767600393607 8502548442457151400590411)
  ·
    refine ⟨12753822663685727100885617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8502548442457151400590411 12753822663685727100885617)
    ·
      refine ⟨9565366997764295325664213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12753822663685727100885617 9565366997764295325664213)
      ·
        refine ⟨224188289010100671695255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9565366997764295325664213 224188289010100671695255)
        ·
          refine ⟨336282433515151007542883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224188289010100671695255 336282433515151007542883)
          ·
            refine ⟨504423650272726511314325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336282433515151007542883 504423650272726511314325)
            ·
              refine ⟨23644858606534055217859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 504423650272726511314325 23644858606534055217859)
              ·
                rfl

theorem cell19_233119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_233119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233119 prefixEnd_233119 := by exact prefixLift 233119
  have htrace : WordTrace (prefixWord ++ tailWord_233119) baseStart_233119 baseEnd_233119 := by
    simpa [prefixWord, tailWord_233119, baseEnd_233119] using wordTrace_append hprefix tailTrace_233119
  have hstable : (prefixWord ++ tailWord_233119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233119).length < 2 ^ (prefixWord ++ tailWord_233119).sum := by decide
  have hdescent : baseEnd_233119 < baseStart_233119 := by decide
  rcases family_descends (prefixWord ++ tailWord_233119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233121 : List Nat := [1, 2, 3, 3, 2, 2, 6]
def baseStart_233121 : Nat := 118140960795 + 233121 * 2 ^ 59
def prefixEnd_233121 : Nat := 4983230072969 + 3 ^ 40 * 233121 * 2
def baseEnd_233121 : Nat := 23645061463088917869709

theorem tailTrace_233121 : CollatzResearch.WordTrace tailWord_233121 prefixEnd_233121 23645061463088917869709 := by
  unfold tailWord_233121
  simp only [CollatzResearch.WordTrace]
  refine ⟨8502621388449905742163217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5668414258966603828108811 8502621388449905742163217)
  ·
    refine ⟨6376966041337429306622413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8502621388449905742163217 6376966041337429306622413)
    ·
      refine ⟨2391362265501535989983405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6376966041337429306622413 2391362265501535989983405)
      ·
        refine ⟨896760849563075996243777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2391362265501535989983405 896760849563075996243777)
        ·
          refine ⟨672570637172306997182833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896760849563075996243777 672570637172306997182833)
          ·
            refine ⟨504427977879230247887125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672570637172306997182833 504427977879230247887125)
            ·
              refine ⟨23645061463088917869709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 504427977879230247887125 23645061463088917869709)
              ·
                rfl

theorem cell19_233121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_233121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233121 prefixEnd_233121 := by exact prefixLift 233121
  have htrace : WordTrace (prefixWord ++ tailWord_233121) baseStart_233121 baseEnd_233121 := by
    simpa [prefixWord, tailWord_233121, baseEnd_233121] using wordTrace_append hprefix tailTrace_233121
  have hstable : (prefixWord ++ tailWord_233121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233121).length < 2 ^ (prefixWord ++ tailWord_233121).sum := by decide
  have hdescent : baseEnd_233121 < baseStart_233121 := by decide
  rcases family_descends (prefixWord ++ tailWord_233121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233123 : List Nat := [1, 1, 1, 4, 1, 1, 10]
def baseStart_233123 : Nat := 118140960795 + 233123 * 2 ^ 59
def prefixEnd_233123 : Nat := 4983230072969 + 3 ^ 40 * 233123 * 2
def baseEnd_233123 : Nat := 23645264319643780521559

theorem tailTrace_233123 : CollatzResearch.WordTrace tailWord_233123 prefixEnd_233123 23645264319643780521559 := by
  unfold tailWord_233123
  simp only [CollatzResearch.WordTrace]
  refine ⟨8502694334442660083736023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5668462889628440055824015 8502694334442660083736023)
  ·
    refine ⟨12754041501663990125604035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8502694334442660083736023 12754041501663990125604035)
    ·
      refine ⟨19131062252495985188406053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12754041501663990125604035 19131062252495985188406053)
      ·
        refine ⟨3587074172342997222826135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19131062252495985188406053 3587074172342997222826135)
        ·
          refine ⟨5380611258514495834239203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3587074172342997222826135 5380611258514495834239203)
          ·
            refine ⟨8070916887771743751358805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380611258514495834239203 8070916887771743751358805)
            ·
              refine ⟨23645264319643780521559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8070916887771743751358805 23645264319643780521559)
              ·
                rfl

theorem cell19_233123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_233123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233123 prefixEnd_233123 := by exact prefixLift 233123
  have htrace : WordTrace (prefixWord ++ tailWord_233123) baseStart_233123 baseEnd_233123 := by
    simpa [prefixWord, tailWord_233123, baseEnd_233123] using wordTrace_append hprefix tailTrace_233123
  have hstable : (prefixWord ++ tailWord_233123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233123).length < 2 ^ (prefixWord ++ tailWord_233123).sum := by decide
  have hdescent : baseEnd_233123 < baseStart_233123 := by decide
  rcases family_descends (prefixWord ++ tailWord_233123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233178 : List Nat := [3, 1, 1, 2, 2, 5, 5]
def baseStart_233178 : Nat := 118140960795 + 233178 * 2 ^ 59
def prefixEnd_233178 : Nat := 4983230072969 + 3 ^ 40 * 233178 * 2
def baseEnd_233178 : Nat := 23650842874902503447435

theorem tailTrace_233178 : CollatzResearch.WordTrace tailWord_233178 prefixEnd_233178 23650842874902503447435 := by
  unfold tailWord_233178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126175087310851119247047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5669800232828936317992125 2126175087310851119247047)
  ·
    refine ⟨3189262630966276678870571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2126175087310851119247047 3189262630966276678870571)
    ·
      refine ⟨4783893946449415018305857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3189262630966276678870571 4783893946449415018305857)
      ·
        refine ⟨3587920459837061263729393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4783893946449415018305857 3587920459837061263729393)
        ·
          refine ⟨2690940344877795947797045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3587920459837061263729393 2690940344877795947797045)
          ·
            refine ⟨252275657332293370105973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2690940344877795947797045 252275657332293370105973)
            ·
              refine ⟨23650842874902503447435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252275657332293370105973 23650842874902503447435)
              ·
                rfl

theorem cell19_233178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_233178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233178 prefixEnd_233178 := by exact prefixLift 233178
  have htrace : WordTrace (prefixWord ++ tailWord_233178) baseStart_233178 baseEnd_233178 := by
    simpa [prefixWord, tailWord_233178, baseEnd_233178] using wordTrace_append hprefix tailTrace_233178
  have hstable : (prefixWord ++ tailWord_233178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233178).length < 2 ^ (prefixWord ++ tailWord_233178).sum := by decide
  have hdescent : baseEnd_233178 < baseStart_233178 := by decide
  rcases family_descends (prefixWord ++ tailWord_233178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233197 : List Nat := [1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_233197 : Nat := 118140960795 + 233197 * 2 ^ 59
def prefixEnd_233197 : Nat := 4983230072969 + 3 ^ 40 * 233197 * 2
def baseEnd_233197 : Nat := 70958310036521095920031

theorem tailTrace_233197 : CollatzResearch.WordTrace tailWord_233197 prefixEnd_233197 70958310036521095920031 := by
  unfold tailWord_233197
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505393336174570721929845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5670262224116380481286563 8505393336174570721929845)
  ·
    refine ⟨797380625266366005180923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8505393336174570721929845 797380625266366005180923)
    ·
      refine ⟨1196070937899549007771385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797380625266366005180923 1196070937899549007771385)
      ·
        refine ⟨897053203424661755828539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1196070937899549007771385 897053203424661755828539)
        ·
          refine ⟨1345579805136992633742809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897053203424661755828539 1345579805136992633742809)
          ·
            refine ⟨1009184853852744475307107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1345579805136992633742809 1009184853852744475307107)
            ·
              refine ⟨1513777280779116712960661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009184853852744475307107 1513777280779116712960661)
              ·
                refine ⟨70958310036521095920031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1513777280779116712960661 70958310036521095920031)
                ·
                  rfl

theorem cell19_233197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_233197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233197 prefixEnd_233197 := by exact prefixLift 233197
  have htrace : WordTrace (prefixWord ++ tailWord_233197) baseStart_233197 baseEnd_233197 := by
    simpa [prefixWord, tailWord_233197, baseEnd_233197] using wordTrace_append hprefix tailTrace_233197
  have hstable : (prefixWord ++ tailWord_233197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233197).length < 2 ^ (prefixWord ++ tailWord_233197).sum := by decide
  have hdescent : baseEnd_233197 < baseStart_233197 := by decide
  rcases family_descends (prefixWord ++ tailWord_233197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233229 : List Nat := [1, 7, 2, 1, 1, 7]
def baseStart_233229 : Nat := 118140960795 + 233229 * 2 ^ 59
def prefixEnd_233229 : Nat := 4983230072969 + 3 ^ 40 * 233229 * 2
def baseEnd_233229 : Nat := 7885338572350500356537

theorem tailTrace_233229 : CollatzResearch.WordTrace tailWord_233229 prefixEnd_233229 7885338572350500356537 := by
  unfold tailWord_233229
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506560472058640187094741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5671040314705760124729827 8506560472058640187094741)
  ·
    refine ⟨199372511063874379385033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8506560472058640187094741 199372511063874379385033)
    ·
      refine ⟨149529383297905784538775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199372511063874379385033 149529383297905784538775)
      ·
        refine ⟨224294074946858676808163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149529383297905784538775 224294074946858676808163)
        ·
          refine ⟨336441112420288015212245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224294074946858676808163 336441112420288015212245)
          ·
            refine ⟨7885338572350500356537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 336441112420288015212245 7885338572350500356537)
            ·
              rfl

theorem cell19_233229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 7].length) (baseStart_233229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233229 prefixEnd_233229 := by exact prefixLift 233229
  have htrace : WordTrace (prefixWord ++ tailWord_233229) baseStart_233229 baseEnd_233229 := by
    simpa [prefixWord, tailWord_233229, baseEnd_233229] using wordTrace_append hprefix tailTrace_233229
  have hstable : (prefixWord ++ tailWord_233229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233229).length < 2 ^ (prefixWord ++ tailWord_233229).sum := by decide
  have hdescent : baseEnd_233229 < baseStart_233229 := by decide
  rcases family_descends (prefixWord ++ tailWord_233229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233237 : List Nat := [1, 3, 2, 1, 2, 10]
def baseStart_233237 : Nat := 118140960795 + 233237 * 2 ^ 59
def prefixEnd_233237 : Nat := 4983230072969 + 3 ^ 40 * 233237 * 2
def baseEnd_233237 : Nat := 7885609047756983892337

theorem tailTrace_233237 : CollatzResearch.WordTrace tailWord_233237 prefixEnd_233237 7885609047756983892337 := by
  unfold tailWord_233237
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506852256029657553385965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5671234837353105035590643 8506852256029657553385965)
  ·
    refine ⟨3190069596011121582519737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8506852256029657553385965 3190069596011121582519737)
    ·
      refine ⟨2392552197008341186889803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3190069596011121582519737 2392552197008341186889803)
      ·
        refine ⟨3588828295512511780334705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392552197008341186889803 3588828295512511780334705)
        ·
          refine ⟨2691621221634383835251029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588828295512511780334705 2691621221634383835251029)
          ·
            refine ⟨7885609047756983892337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2691621221634383835251029 7885609047756983892337)
            ·
              rfl

theorem cell19_233237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_233237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233237 prefixEnd_233237 := by exact prefixLift 233237
  have htrace : WordTrace (prefixWord ++ tailWord_233237) baseStart_233237 baseEnd_233237 := by
    simpa [prefixWord, tailWord_233237, baseEnd_233237] using wordTrace_append hprefix tailTrace_233237
  have hstable : (prefixWord ++ tailWord_233237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233237).length < 2 ^ (prefixWord ++ tailWord_233237).sum := by decide
  have hdescent : baseEnd_233237 < baseStart_233237 := by decide
  rcases family_descends (prefixWord ++ tailWord_233237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233246 : List Nat := [4, 3, 2, 2, 2, 1, 1, 4]
def baseStart_233246 : Nat := 118140960795 + 233246 * 2 ^ 59
def prefixEnd_233246 : Nat := 4983230072969 + 3 ^ 40 * 233246 * 2
def baseEnd_233246 : Nat := 70973219993303500831009

theorem tailTrace_233246 : CollatzResearch.WordTrace tailWord_233246 prefixEnd_233246 70973219993303500831009 := by
  unfold tailWord_233246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063397564124631511307949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5671453675331368060309061 1063397564124631511307949)
  ·
    refine ⟨398774086546736816740481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1063397564124631511307949 398774086546736816740481)
    ·
      refine ⟨299080564910052612555361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398774086546736816740481 299080564910052612555361)
      ·
        refine ⟨224310423682539459416521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299080564910052612555361 224310423682539459416521)
        ·
          refine ⟨168232817761904594562391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224310423682539459416521 168232817761904594562391)
          ·
            refine ⟨252349226642856891843587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168232817761904594562391 252349226642856891843587)
            ·
              refine ⟨378523839964285337765381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252349226642856891843587 378523839964285337765381)
              ·
                refine ⟨70973219993303500831009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378523839964285337765381 70973219993303500831009)
                ·
                  rfl

theorem cell19_233246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_233246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233246 prefixEnd_233246 := by exact prefixLift 233246
  have htrace : WordTrace (prefixWord ++ tailWord_233246) baseStart_233246 baseEnd_233246 := by
    simpa [prefixWord, tailWord_233246, baseEnd_233246] using wordTrace_append hprefix tailTrace_233246
  have hstable : (prefixWord ++ tailWord_233246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233246).length < 2 ^ (prefixWord ++ tailWord_233246).sum := by decide
  have hdescent : baseEnd_233246 < baseStart_233246 := by decide
  rcases family_descends (prefixWord ++ tailWord_233246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233252 : List Nat := [2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_233252 : Nat := 118140960795 + 233252 * 2 ^ 59
def prefixEnd_233252 : Nat := 4983230072969 + 3 ^ 40 * 233252 * 2
def baseEnd_233252 : Nat := 70975045702297264697659

theorem tailTrace_233252 : CollatzResearch.WordTrace tailWord_233252 prefixEnd_233252 70975045702297264697659 := by
  unfold tailWord_233252
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253699675487657557591005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5671599567316876743454673 4253699675487657557591005)
  ·
    refine ⟨1595137378307871584096627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4253699675487657557591005 1595137378307871584096627)
    ·
      refine ⟨2392706067461807376144941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595137378307871584096627 2392706067461807376144941)
      ·
        refine ⟨897264775298177766054353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2392706067461807376144941 897264775298177766054353)
        ·
          refine ⟨672948581473633324540765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897264775298177766054353 672948581473633324540765)
          ·
            refine ⟨252355718052612496702787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 672948581473633324540765 252355718052612496702787)
            ·
              refine ⟨378533577078918745054181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252355718052612496702787 378533577078918745054181)
              ·
                refine ⟨70975045702297264697659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378533577078918745054181 70975045702297264697659)
                ·
                  rfl

theorem cell19_233252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_233252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233252 prefixEnd_233252 := by exact prefixLift 233252
  have htrace : WordTrace (prefixWord ++ tailWord_233252) baseStart_233252 baseEnd_233252 := by
    simpa [prefixWord, tailWord_233252, baseEnd_233252] using wordTrace_append hprefix tailTrace_233252
  have hstable : (prefixWord ++ tailWord_233252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233252).length < 2 ^ (prefixWord ++ tailWord_233252).sum := by decide
  have hdescent : baseEnd_233252 < baseStart_233252 := by decide
  rcases family_descends (prefixWord ++ tailWord_233252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233292 : List Nat := [2, 2, 1, 3, 4, 1, 6]
def baseStart_233292 : Nat := 118140960795 + 233292 * 2 ^ 59
def prefixEnd_233292 : Nat := 4983230072969 + 3 ^ 40 * 233292 * 2
def baseEnd_233292 : Nat := 23662405698529674602887

theorem tailTrace_233292 : CollatzResearch.WordTrace tailWord_233292 prefixEnd_233292 23662405698529674602887 := by
  unfold tailWord_233292
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254429135415200973319065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5672572180553601297758753 4254429135415200973319065)
  ·
    refine ⟨3190821851561400729989299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4254429135415200973319065 3190821851561400729989299)
    ·
      refine ⟨4786232777342101094983949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190821851561400729989299 4786232777342101094983949)
      ·
        refine ⟨1794837291503287910618981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4786232777342101094983949 1794837291503287910618981)
        ·
          refine ⟨336531992156866483241059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1794837291503287910618981 336531992156866483241059)
          ·
            refine ⟨504797988235299724861589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336531992156866483241059 504797988235299724861589)
            ·
              refine ⟨23662405698529674602887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 504797988235299724861589 23662405698529674602887)
              ·
                rfl

theorem cell19_233292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_233292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233292 prefixEnd_233292 := by exact prefixLift 233292
  have htrace : WordTrace (prefixWord ++ tailWord_233292) baseStart_233292 baseEnd_233292 := by
    simpa [prefixWord, tailWord_233292, baseEnd_233292] using wordTrace_append hprefix tailTrace_233292
  have hstable : (prefixWord ++ tailWord_233292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233292).length < 2 ^ (prefixWord ++ tailWord_233292).sum := by decide
  have hdescent : baseEnd_233292 < baseStart_233292 := by decide
  rcases family_descends (prefixWord ++ tailWord_233292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233313 : List Nat := [1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_233313 : Nat := 118140960795 + 233313 * 2 ^ 59
def prefixEnd_233313 : Nat := 4983230072969 + 3 ^ 40 * 233313 * 2
def baseEnd_233313 : Nat := 70993607077067197341937

theorem tailTrace_233313 : CollatzResearch.WordTrace tailWord_233313 prefixEnd_233313 70993607077067197341937 := by
  unfold tailWord_233313
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509624203754322533152593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5673082802502881688768395 8509624203754322533152593)
  ·
    refine ⟨6382218152815741899864445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8509624203754322533152593 6382218152815741899864445)
    ·
      refine ⟨2393331807305903212449167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6382218152815741899864445 2393331807305903212449167)
      ·
        refine ⟨3589997710958854818673751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393331807305903212449167 3589997710958854818673751)
        ·
          refine ⟨5384996566438282228010627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589997710958854818673751 5384996566438282228010627)
          ·
            refine ⟨8077494849657423342015941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5384996566438282228010627 8077494849657423342015941)
            ·
              refine ⟨1514530284310766876627989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8077494849657423342015941 1514530284310766876627989)
              ·
                refine ⟨70993607077067197341937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1514530284310766876627989 70993607077067197341937)
                ·
                  rfl

theorem cell19_233313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_233313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233313 prefixEnd_233313 := by exact prefixLift 233313
  have htrace : WordTrace (prefixWord ++ tailWord_233313) baseStart_233313 baseEnd_233313 := by
    simpa [prefixWord, tailWord_233313, baseEnd_233313] using wordTrace_append hprefix tailTrace_233313
  have hstable : (prefixWord ++ tailWord_233313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233313).length < 2 ^ (prefixWord ++ tailWord_233313).sum := by decide
  have hdescent : baseEnd_233313 < baseStart_233313 := by decide
  rcases family_descends (prefixWord ++ tailWord_233313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233326 : List Nat := [4, 1, 2, 3, 1, 3, 2, 3]
def baseStart_233326 : Nat := 118140960795 + 233326 * 2 ^ 59
def prefixEnd_233326 : Nat := 4983230072969 + 3 ^ 40 * 233326 * 2
def baseEnd_233326 : Nat := 70997562779887019053013

theorem tailTrace_233326 : CollatzResearch.WordTrace tailWord_233326 prefixEnd_233326 70997562779887019053013 := by
  unfold tailWord_233326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063762294088403219171979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5673398901804817168917221 1063762294088403219171979)
  ·
    refine ⟨1595643441132604828757969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1063762294088403219171979 1595643441132604828757969)
    ·
      refine ⟨1196732580849453621568477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1595643441132604828757969 1196732580849453621568477)
      ·
        refine ⟨448774717818545108088179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1196732580849453621568477 448774717818545108088179)
        ·
          refine ⟨673162076727817662132269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448774717818545108088179 673162076727817662132269)
          ·
            refine ⟨252435778772931623299601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673162076727817662132269 252435778772931623299601)
            ·
              refine ⟨189326834079698717474701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252435778772931623299601 189326834079698717474701)
              ·
                refine ⟨70997562779887019053013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189326834079698717474701 70997562779887019053013)
                ·
                  rfl

theorem cell19_233326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_233326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233326 prefixEnd_233326 := by exact prefixLift 233326
  have htrace : WordTrace (prefixWord ++ tailWord_233326) baseStart_233326 baseEnd_233326 := by
    simpa [prefixWord, tailWord_233326, baseEnd_233326] using wordTrace_append hprefix tailTrace_233326
  have hstable : (prefixWord ++ tailWord_233326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233326).length < 2 ^ (prefixWord ++ tailWord_233326).sum := by decide
  have hdescent : baseEnd_233326 < baseStart_233326 := by decide
  rcases family_descends (prefixWord ++ tailWord_233326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233345 : List Nat := [1, 2, 4, 4, 2, 1, 5]
def baseStart_233345 : Nat := 118140960795 + 233345 * 2 ^ 59
def prefixEnd_233345 : Nat := 4983230072969 + 3 ^ 40 * 233345 * 2
def baseEnd_233345 : Nat := 23667781397233534876913

theorem tailTrace_233345 : CollatzResearch.WordTrace tailWord_233345 prefixEnd_233345 23667781397233534876913 := by
  unfold tailWord_233345
  simp only [CollatzResearch.WordTrace]
  refine ⟨8510791339638391998317489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5673860893092261332211659 8510791339638391998317489)
  ·
    refine ⟨6383093504728793998738117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8510791339638391998317489 6383093504728793998738117)
    ·
      refine ⟨1196830032136648874763397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6383093504728793998738117 1196830032136648874763397)
      ·
        refine ⟨224405631025621664018137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1196830032136648874763397 224405631025621664018137)
        ·
          refine ⟨168304223269216248013603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224405631025621664018137 168304223269216248013603)
          ·
            refine ⟨252456334903824372020405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168304223269216248013603 252456334903824372020405)
            ·
              refine ⟨23667781397233534876913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252456334903824372020405 23667781397233534876913)
              ·
                rfl

theorem cell19_233345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_233345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233345 prefixEnd_233345 := by exact prefixLift 233345
  have htrace : WordTrace (prefixWord ++ tailWord_233345) baseStart_233345 baseEnd_233345 := by
    simpa [prefixWord, tailWord_233345, baseEnd_233345] using wordTrace_append hprefix tailTrace_233345
  have hstable : (prefixWord ++ tailWord_233345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233345).length < 2 ^ (prefixWord ++ tailWord_233345).sum := by decide
  have hdescent : baseEnd_233345 < baseStart_233345 := by decide
  rcases family_descends (prefixWord ++ tailWord_233345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233404 : List Nat := [2, 2, 2, 5, 2, 6]
def baseStart_233404 : Nat := 118140960795 + 233404 * 2 ^ 59
def prefixEnd_233404 : Nat := 4983230072969 + 3 ^ 40 * 233404 * 2
def baseEnd_233404 : Nat := 7891255221867327702163

theorem tailTrace_233404 : CollatzResearch.WordTrace tailWord_233404 prefixEnd_233404 7891255221867327702163 := by
  unfold tailWord_233404
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256471623212322537357633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5675295497616430049810177 4256471623212322537357633)
  ·
    refine ⟨3192353717409241903018225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4256471623212322537357633 3192353717409241903018225)
    ·
      refine ⟨2394265288056931427263669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3192353717409241903018225 2394265288056931427263669)
      ·
        refine ⟨224462370755337321305969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2394265288056931427263669 224462370755337321305969)
        ·
          refine ⟨168346778066502990979477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224462370755337321305969 168346778066502990979477)
          ·
            refine ⟨7891255221867327702163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168346778066502990979477 7891255221867327702163)
            ·
              rfl

theorem cell19_233404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 6].length) (baseStart_233404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233404 prefixEnd_233404 := by exact prefixLift 233404
  have htrace : WordTrace (prefixWord ++ tailWord_233404) baseStart_233404 baseEnd_233404 := by
    simpa [prefixWord, tailWord_233404, baseEnd_233404] using wordTrace_append hprefix tailTrace_233404
  have hstable : (prefixWord ++ tailWord_233404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233404).length < 2 ^ (prefixWord ++ tailWord_233404).sum := by decide
  have hdescent : baseEnd_233404 < baseStart_233404 := by decide
  rcases family_descends (prefixWord ++ tailWord_233404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233444 : List Nat := [2, 3, 1, 1, 1, 1, 7, 3]
def baseStart_233444 : Nat := 118140960795 + 233444 * 2 ^ 59
def prefixEnd_233444 : Nat := 4983230072969 + 3 ^ 40 * 233444 * 2
def baseEnd_233444 : Nat := 71033468390097708430469

theorem tailTrace_233444 : CollatzResearch.WordTrace tailWord_233444 prefixEnd_233444 71033468390097708430469 := by
  unfold tailWord_233444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257201083139865953085693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5676268110853154604114257 4257201083139865953085693)
  ·
    refine ⟨1596450406177449732407135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4257201083139865953085693 1596450406177449732407135)
    ·
      refine ⟨2394675609266174598610703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596450406177449732407135 2394675609266174598610703)
      ·
        refine ⟨3592013413899261897916055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394675609266174598610703 3592013413899261897916055)
        ·
          refine ⟨5388020120848892846874083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3592013413899261897916055 5388020120848892846874083)
          ·
            refine ⟨8082030181273339270311125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5388020120848892846874083 8082030181273339270311125)
            ·
              refine ⟨189422582373593889147917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8082030181273339270311125 189422582373593889147917)
              ·
                refine ⟨71033468390097708430469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189422582373593889147917 71033468390097708430469)
                ·
                  rfl

theorem cell19_233444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_233444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233444 prefixEnd_233444 := by exact prefixLift 233444
  have htrace : WordTrace (prefixWord ++ tailWord_233444) baseStart_233444 baseEnd_233444 := by
    simpa [prefixWord, tailWord_233444, baseEnd_233444] using wordTrace_append hprefix tailTrace_233444
  have hstable : (prefixWord ++ tailWord_233444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233444).length < 2 ^ (prefixWord ++ tailWord_233444).sum := by decide
  have hdescent : baseEnd_233444 < baseStart_233444 := by decide
  rcases family_descends (prefixWord ++ tailWord_233444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233465 : List Nat := [1, 2, 1, 3, 1, 5, 6]
def baseStart_233465 : Nat := 118140960795 + 233465 * 2 ^ 59
def prefixEnd_233465 : Nat := 4983230072969 + 3 ^ 40 * 233465 * 2
def baseEnd_233465 : Nat := 23679952790525293987915

theorem tailTrace_233465 : CollatzResearch.WordTrace tailWord_233465 prefixEnd_233465 23679952790525293987915 := by
  unfold tailWord_233465
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515168099203652492685849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5676778732802434995123899 8515168099203652492685849)
  ·
    refine ⟨6386376074402739369514387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8515168099203652492685849 6386376074402739369514387)
    ·
      refine ⟨9579564111604109054271581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386376074402739369514387 9579564111604109054271581)
      ·
        refine ⟨3592336541851540895351843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9579564111604109054271581 3592336541851540895351843)
        ·
          refine ⟨5388504812777311343027765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3592336541851540895351843 5388504812777311343027765)
          ·
            refine ⟨505172326197872938408853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5388504812777311343027765 505172326197872938408853)
            ·
              refine ⟨23679952790525293987915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 505172326197872938408853 23679952790525293987915)
              ·
                rfl

theorem cell19_233465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_233465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233465 prefixEnd_233465 := by exact prefixLift 233465
  have htrace : WordTrace (prefixWord ++ tailWord_233465) baseStart_233465 baseEnd_233465 := by
    simpa [prefixWord, tailWord_233465, baseEnd_233465] using wordTrace_append hprefix tailTrace_233465
  have hstable : (prefixWord ++ tailWord_233465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233465).length < 2 ^ (prefixWord ++ tailWord_233465).sum := by decide
  have hdescent : baseEnd_233465 < baseStart_233465 := by decide
  rcases family_descends (prefixWord ++ tailWord_233465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233484 : List Nat := [2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_233484 : Nat := 118140960795 + 233484 * 2 ^ 59
def prefixEnd_233484 : Nat := 4983230072969 + 3 ^ 40 * 233484 * 2
def baseEnd_233484 : Nat := 71045639783389467541471

theorem tailTrace_233484 : CollatzResearch.WordTrace tailWord_233484 prefixEnd_233484 71045639783389467541471 := by
  unfold tailWord_233484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257930543067409368813753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5677240724089879158418337 4257930543067409368813753)
  ·
    refine ⟨3193447907300557026610315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4257930543067409368813753 3193447907300557026610315)
    ·
      refine ⟨4790171860950835539915473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3193447907300557026610315 4790171860950835539915473)
      ·
        refine ⟨3592628895713126654936605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4790171860950835539915473 3592628895713126654936605)
        ·
          refine ⟨1347235835892422495601227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3592628895713126654936605 1347235835892422495601227)
          ·
            refine ⟨2020853753838633743401841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347235835892422495601227 2020853753838633743401841)
            ·
              refine ⟨1515640315378975307551381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020853753838633743401841 1515640315378975307551381)
              ·
                refine ⟨71045639783389467541471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1515640315378975307551381 71045639783389467541471)
                ·
                  rfl

theorem cell19_233484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_233484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233484 prefixEnd_233484 := by exact prefixLift 233484
  have htrace : WordTrace (prefixWord ++ tailWord_233484) baseStart_233484 baseEnd_233484 := by
    simpa [prefixWord, tailWord_233484, baseEnd_233484] using wordTrace_append hprefix tailTrace_233484
  have hstable : (prefixWord ++ tailWord_233484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233484).length < 2 ^ (prefixWord ++ tailWord_233484).sum := by decide
  have hdescent : baseEnd_233484 < baseStart_233484 := by decide
  rcases family_descends (prefixWord ++ tailWord_233484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233501 : List Nat := [1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_233501 : Nat := 118140960795 + 233501 * 2 ^ 59
def prefixEnd_233501 : Nat := 4983230072969 + 3 ^ 40 * 233501 * 2
def baseEnd_233501 : Nat := 71050812625538465163647

theorem tailTrace_233501 : CollatzResearch.WordTrace tailWord_233501 prefixEnd_233501 71050812625538465163647 := by
  unfold tailWord_233501
  simp only [CollatzResearch.WordTrace]
  refine ⟨8516481127073230640996357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5677654084715487093997571 8516481127073230640996357)
  ·
    refine ⟨1596840211326230745186817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8516481127073230640996357 1596840211326230745186817)
    ·
      refine ⟨1197630158494673058890113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1596840211326230745186817 1197630158494673058890113)
      ·
        refine ⟨898222618871004794167585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1197630158494673058890113 898222618871004794167585)
        ·
          refine ⟨673666964153253595625689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898222618871004794167585 673666964153253595625689)
          ·
            refine ⟨505250223114940196719267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673666964153253595625689 505250223114940196719267)
            ·
              refine ⟨757875334672410295078901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505250223114940196719267 757875334672410295078901)
              ·
                refine ⟨71050812625538465163647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 757875334672410295078901 71050812625538465163647)
                ·
                  rfl

theorem cell19_233501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_233501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233501 prefixEnd_233501 := by exact prefixLift 233501
  have htrace : WordTrace (prefixWord ++ tailWord_233501) baseStart_233501 baseEnd_233501 := by
    simpa [prefixWord, tailWord_233501, baseEnd_233501] using wordTrace_append hprefix tailTrace_233501
  have hstable : (prefixWord ++ tailWord_233501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233501).length < 2 ^ (prefixWord ++ tailWord_233501).sum := by decide
  have hdescent : baseEnd_233501 < baseStart_233501 := by decide
  rcases family_descends (prefixWord ++ tailWord_233501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233503 : List Nat := [1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_233503 : Nat := 118140960795 + 233503 * 2 ^ 59
def prefixEnd_233503 : Nat := 4983230072969 + 3 ^ 40 * 233503 * 2
def baseEnd_233503 : Nat := 71051421195203053119197

theorem tailTrace_233503 : CollatzResearch.WordTrace tailWord_233503 prefixEnd_233503 71051421195203053119197 := by
  unfold tailWord_233503
  simp only [CollatzResearch.WordTrace]
  refine ⟨8516554073065984982569163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5677702715377323321712775 8516554073065984982569163)
  ·
    refine ⟨12774831109598977473853745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8516554073065984982569163 12774831109598977473853745)
    ·
      refine ⟨9581123332199233105390309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12774831109598977473853745 9581123332199233105390309)
      ·
        refine ⟨1796460624787356207260683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9581123332199233105390309 1796460624787356207260683)
        ·
          refine ⟨2694690937181034310891025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796460624787356207260683 2694690937181034310891025)
          ·
            refine ⟨2021018202885775733168269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694690937181034310891025 2021018202885775733168269)
            ·
              refine ⟨757881826082165899938101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2021018202885775733168269 757881826082165899938101)
              ·
                refine ⟨71051421195203053119197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 757881826082165899938101 71051421195203053119197)
                ·
                  rfl

theorem cell19_233503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_233503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233503 prefixEnd_233503 := by exact prefixLift 233503
  have htrace : WordTrace (prefixWord ++ tailWord_233503) baseStart_233503 baseEnd_233503 := by
    simpa [prefixWord, tailWord_233503, baseEnd_233503] using wordTrace_append hprefix tailTrace_233503
  have hstable : (prefixWord ++ tailWord_233503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233503).length < 2 ^ (prefixWord ++ tailWord_233503).sum := by decide
  have hdescent : baseEnd_233503 < baseStart_233503 := by decide
  rcases family_descends (prefixWord ++ tailWord_233503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233522 : List Nat := [3, 2, 1, 1, 2, 3, 7]
def baseStart_233522 : Nat := 118140960795 + 233522 * 2 ^ 59
def prefixEnd_233522 : Nat := 4983230072969 + 3 ^ 40 * 233522 * 2
def baseEnd_233522 : Nat := 23685734202338879565641

theorem tailTrace_233522 : CollatzResearch.WordTrace tailWord_233522 prefixEnd_233522 23685734202338879565641 := by
  unfold tailWord_233522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129311764999287806877705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5678164706664767485007213 2129311764999287806877705)
  ·
    refine ⟨1596983823749465855158279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2129311764999287806877705 1596983823749465855158279)
    ·
      refine ⟨2395475735624198782737419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596983823749465855158279 2395475735624198782737419)
      ·
        refine ⟨3593213603436298174106129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2395475735624198782737419 3593213603436298174106129)
        ·
          refine ⟨2694910202577223630579597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3593213603436298174106129 2694910202577223630579597)
          ·
            refine ⟨1010591325966458861467349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2694910202577223630579597 1010591325966458861467349)
            ·
              refine ⟨23685734202338879565641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1010591325966458861467349 23685734202338879565641)
              ·
                rfl

theorem cell19_233522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_233522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233522 prefixEnd_233522 := by exact prefixLift 233522
  have htrace : WordTrace (prefixWord ++ tailWord_233522) baseStart_233522 baseEnd_233522 := by
    simpa [prefixWord, tailWord_233522, baseEnd_233522] using wordTrace_append hprefix tailTrace_233522
  have hstable : (prefixWord ++ tailWord_233522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233522).length < 2 ^ (prefixWord ++ tailWord_233522).sum := by decide
  have hdescent : baseEnd_233522 < baseStart_233522 := by decide
  rcases family_descends (prefixWord ++ tailWord_233522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233560 : List Nat := [2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_233560 : Nat := 118140960795 + 233560 * 2 ^ 59
def prefixEnd_233560 : Nat := 4983230072969 + 3 ^ 40 * 233560 * 2
def baseEnd_233560 : Nat := 71068765430643809852375

theorem tailTrace_233560 : CollatzResearch.WordTrace tailWord_233560 prefixEnd_233560 71068765430643809852375 := by
  unfold tailWord_233560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259316516929741858697067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5679088689239655811596089 4259316516929741858697067)
  ·
    refine ⟨6388974775394612788045601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4259316516929741858697067 6388974775394612788045601)
    ·
      refine ⟨4791731081545959591034201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6388974775394612788045601 4791731081545959591034201)
      ·
        refine ⟨3593798311159469693275651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4791731081545959591034201 3593798311159469693275651)
        ·
          refine ⟨5390697466739204539913477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3593798311159469693275651 5390697466739204539913477)
          ·
            refine ⟨1010755775013600851233777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5390697466739204539913477 1010755775013600851233777)
            ·
              refine ⟨758066831260200638425333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010755775013600851233777 758066831260200638425333)
              ·
                refine ⟨71068765430643809852375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 758066831260200638425333 71068765430643809852375)
                ·
                  rfl

theorem cell19_233560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_233560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233560 prefixEnd_233560 := by exact prefixLift 233560
  have htrace : WordTrace (prefixWord ++ tailWord_233560) baseStart_233560 baseEnd_233560 := by
    simpa [prefixWord, tailWord_233560, baseEnd_233560] using wordTrace_append hprefix tailTrace_233560
  have hstable : (prefixWord ++ tailWord_233560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233560).length < 2 ^ (prefixWord ++ tailWord_233560).sum := by decide
  have hdescent : baseEnd_233560 < baseStart_233560 := by decide
  rcases family_descends (prefixWord ++ tailWord_233560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233596 : List Nat := [2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_233596 : Nat := 118140960795 + 233596 * 2 ^ 59
def prefixEnd_233596 : Nat := 4983230072969 + 3 ^ 40 * 233596 * 2
def baseEnd_233596 : Nat := 71079719684606393052277

theorem tailTrace_233596 : CollatzResearch.WordTrace tailWord_233596 prefixEnd_233596 71079719684606393052277 := by
  unfold tailWord_233596
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259973030864530932852321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5679964041152707910469761 4259973030864530932852321)
  ·
    refine ⟨3194979773148398199639241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4259973030864530932852321 3194979773148398199639241)
    ·
      refine ⟨2396234829861298649729431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3194979773148398199639241 2396234829861298649729431)
      ·
        refine ⟨3594352244791947974594147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396234829861298649729431 3594352244791947974594147)
        ·
          refine ⟨5391528367187921961891221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594352244791947974594147 5391528367187921961891221)
          ·
            refine ⟨252727892211933841963651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5391528367187921961891221 252727892211933841963651)
            ·
              refine ⟨379091838317900762945477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252727892211933841963651 379091838317900762945477)
              ·
                refine ⟨71079719684606393052277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379091838317900762945477 71079719684606393052277)
                ·
                  rfl

theorem cell19_233596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_233596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233596 prefixEnd_233596 := by exact prefixLift 233596
  have htrace : WordTrace (prefixWord ++ tailWord_233596) baseStart_233596 baseEnd_233596 := by
    simpa [prefixWord, tailWord_233596, baseEnd_233596] using wordTrace_append hprefix tailTrace_233596
  have hstable : (prefixWord ++ tailWord_233596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233596).length < 2 ^ (prefixWord ++ tailWord_233596).sum := by decide
  have hdescent : baseEnd_233596 < baseStart_233596 := by decide
  rcases family_descends (prefixWord ++ tailWord_233596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233634 : List Nat := [3, 3, 1, 3, 1, 2, 6]
def baseStart_233634 : Nat := 118140960795 + 233634 * 2 ^ 59
def prefixEnd_233634 : Nat := 4983230072969 + 3 ^ 40 * 233634 * 2
def baseEnd_233634 : Nat := 23697094169411188069243

theorem tailTrace_233634 : CollatzResearch.WordTrace tailWord_233634 prefixEnd_233634 23697094169411188069243 := by
  unfold tailWord_233634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130333008897848588896989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5680888023727596237058637 2130333008897848588896989)
  ·
    refine ⟨798874878336693220836371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2130333008897848588896989 798874878336693220836371)
    ·
      refine ⟨1198312317505039831254557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798874878336693220836371 1198312317505039831254557)
      ·
        refine ⟨449367119064389936720459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1198312317505039831254557 449367119064389936720459)
        ·
          refine ⟨674050678596584905080689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449367119064389936720459 674050678596584905080689)
          ·
            refine ⟨505538008947438678810517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674050678596584905080689 505538008947438678810517)
            ·
              refine ⟨23697094169411188069243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 505538008947438678810517 23697094169411188069243)
              ·
                rfl

theorem cell19_233634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_233634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233634 prefixEnd_233634 := by exact prefixLift 233634
  have htrace : WordTrace (prefixWord ++ tailWord_233634) baseStart_233634 baseEnd_233634 := by
    simpa [prefixWord, tailWord_233634, baseEnd_233634] using wordTrace_append hprefix tailTrace_233634
  have hstable : (prefixWord ++ tailWord_233634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233634).length < 2 ^ (prefixWord ++ tailWord_233634).sum := by decide
  have hdescent : baseEnd_233634 < baseStart_233634 := by decide
  rcases family_descends (prefixWord ++ tailWord_233634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233666 : List Nat := [3, 5, 1, 1, 1, 3, 2, 3]
def baseStart_233666 : Nat := 118140960795 + 233666 * 2 ^ 59
def prefixEnd_233666 : Nat := 4983230072969 + 3 ^ 40 * 233666 * 2
def baseEnd_233666 : Nat := 71101019622866971496531

theorem tailTrace_233666 : CollatzResearch.WordTrace tailWord_233666 prefixEnd_233666 71101019622866971496531 := by
  unfold tailWord_233666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130624792868865955188213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5681666114316975880501901 2130624792868865955188213)
  ·
    refine ⟨199746074331456183298895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2130624792868865955188213 199746074331456183298895)
    ·
      refine ⟨299619111497184274948343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199746074331456183298895 299619111497184274948343)
      ·
        refine ⟨449428667245776412422515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299619111497184274948343 449428667245776412422515)
        ·
          refine ⟨674143000868664618633773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449428667245776412422515 674143000868664618633773)
          ·
            refine ⟨252803625325749231987665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 674143000868664618633773 252803625325749231987665)
            ·
              refine ⟨189602718994311923990749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252803625325749231987665 189602718994311923990749)
              ·
                refine ⟨71101019622866971496531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189602718994311923990749 71101019622866971496531)
                ·
                  rfl

theorem cell19_233666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_233666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233666 prefixEnd_233666 := by exact prefixLift 233666
  have htrace : WordTrace (prefixWord ++ tailWord_233666) baseStart_233666 baseEnd_233666 := by
    simpa [prefixWord, tailWord_233666, baseEnd_233666] using wordTrace_append hprefix tailTrace_233666
  have hstable : (prefixWord ++ tailWord_233666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233666).length < 2 ^ (prefixWord ++ tailWord_233666).sum := by decide
  have hdescent : baseEnd_233666 < baseStart_233666 := by decide
  rcases family_descends (prefixWord ++ tailWord_233666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233674 : List Nat := [3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_233674 : Nat := 118140960795 + 233674 * 2 ^ 59
def prefixEnd_233674 : Nat := 4983230072969 + 3 ^ 40 * 233674 * 2
def baseEnd_233674 : Nat := 71103453901525323318731

theorem tailTrace_233674 : CollatzResearch.WordTrace tailWord_233674 prefixEnd_233674 71103453901525323318731 := by
  unfold tailWord_233674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130697738861620296761019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5681860636964320791362717 2130697738861620296761019)
  ·
    refine ⟨3196046608292430445141529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2130697738861620296761019 3196046608292430445141529)
    ·
      refine ⟨2397034956219322833856147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3196046608292430445141529 2397034956219322833856147)
      ·
        refine ⟨3595552434328984250784221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397034956219322833856147 3595552434328984250784221)
        ·
          refine ⟨1348332162873369094044083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3595552434328984250784221 1348332162873369094044083)
          ·
            refine ⟨2022498244310053641066125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348332162873369094044083 2022498244310053641066125)
            ·
              refine ⟨758436841616270115399797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2022498244310053641066125 758436841616270115399797)
              ·
                refine ⟨71103453901525323318731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 758436841616270115399797 71103453901525323318731)
                ·
                  rfl

theorem cell19_233674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_233674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233674 prefixEnd_233674 := by exact prefixLift 233674
  have htrace : WordTrace (prefixWord ++ tailWord_233674) baseStart_233674 baseEnd_233674 := by
    simpa [prefixWord, tailWord_233674, baseEnd_233674] using wordTrace_append hprefix tailTrace_233674
  have hstable : (prefixWord ++ tailWord_233674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233674).length < 2 ^ (prefixWord ++ tailWord_233674).sum := by decide
  have hdescent : baseEnd_233674 < baseStart_233674 := by decide
  rcases family_descends (prefixWord ++ tailWord_233674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233765 : List Nat := [1, 3, 1, 2, 6, 1, 1, 4]
def baseStart_233765 : Nat := 118140960795 + 233765 * 2 ^ 59
def prefixEnd_233765 : Nat := 4983230072969 + 3 ^ 40 * 233765 * 2
def baseEnd_233765 : Nat := 71131143821264075296261

theorem tailTrace_233765 : CollatzResearch.WordTrace tailWord_233765 prefixEnd_233765 71131143821264075296261 := by
  unfold tailWord_233765
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526109998116803728606749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5684073332077869152404499 8526109998116803728606749)
  ·
    refine ⟨3197291249293801398227531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8526109998116803728606749 3197291249293801398227531)
    ·
      refine ⟨4795936873940702097341297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197291249293801398227531 4795936873940702097341297)
      ·
        refine ⟨3596952655455526573005973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4795936873940702097341297 3596952655455526573005973)
        ·
          refine ⟨168607155724477808109655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3596952655455526573005973 168607155724477808109655)
          ·
            refine ⟨252910733586716712164483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168607155724477808109655 252910733586716712164483)
            ·
              refine ⟨379366100380075068246725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252910733586716712164483 379366100380075068246725)
              ·
                refine ⟨71131143821264075296261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379366100380075068246725 71131143821264075296261)
                ·
                  rfl

theorem cell19_233765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_233765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233765 prefixEnd_233765 := by exact prefixLift 233765
  have htrace : WordTrace (prefixWord ++ tailWord_233765) baseStart_233765 baseEnd_233765 := by
    simpa [prefixWord, tailWord_233765, baseEnd_233765] using wordTrace_append hprefix tailTrace_233765
  have hstable : (prefixWord ++ tailWord_233765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233765).length < 2 ^ (prefixWord ++ tailWord_233765).sum := by decide
  have hdescent : baseEnd_233765 < baseStart_233765 := by decide
  rcases family_descends (prefixWord ++ tailWord_233765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233786 : List Nat := [3, 1, 1, 1, 4, 3, 3, 3]
def baseStart_233786 : Nat := 118140960795 + 233786 * 2 ^ 59
def prefixEnd_233786 : Nat := 4983230072969 + 3 ^ 40 * 233786 * 2
def baseEnd_233786 : Nat := 71137533802742248829537

theorem tailTrace_233786 : CollatzResearch.WordTrace tailWord_233786 prefixEnd_233786 71137533802742248829537 := by
  unfold tailWord_233786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131718982760181078780303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5684583954027149543414141 2131718982760181078780303)
  ·
    refine ⟨3197578474140271618170455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2131718982760181078780303 3197578474140271618170455)
    ·
      refine ⟨4796367711210407427255683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197578474140271618170455 4796367711210407427255683)
      ·
        refine ⟨7194551566815611140883525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796367711210407427255683 7194551566815611140883525)
        ·
          refine ⟨1348978418777927088915661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7194551566815611140883525 1348978418777927088915661)
          ·
            refine ⟨505866907041722658343373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1348978418777927088915661 505866907041722658343373)
            ·
              refine ⟨189700090140645996878765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505866907041722658343373 189700090140645996878765)
              ·
                refine ⟨71137533802742248829537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189700090140645996878765 71137533802742248829537)
                ·
                  rfl

theorem cell19_233786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_233786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233786 prefixEnd_233786 := by exact prefixLift 233786
  have htrace : WordTrace (prefixWord ++ tailWord_233786) baseStart_233786 baseEnd_233786 := by
    simpa [prefixWord, tailWord_233786, baseEnd_233786] using wordTrace_append hprefix tailTrace_233786
  have hstable : (prefixWord ++ tailWord_233786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233786).length < 2 ^ (prefixWord ++ tailWord_233786).sum := by decide
  have hdescent : baseEnd_233786 < baseStart_233786 := by decide
  rcases family_descends (prefixWord ++ tailWord_233786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233858 : List Nat := [3, 4, 2, 1, 3, 1, 5]
def baseStart_233858 : Nat := 118140960795 + 233858 * 2 ^ 59
def prefixEnd_233858 : Nat := 4983230072969 + 3 ^ 40 * 233858 * 2
def baseEnd_233858 : Nat := 23719814103555805076447

theorem tailTrace_233858 : CollatzResearch.WordTrace tailWord_233858 prefixEnd_233858 23719814103555805076447 := by
  unfold tailWord_233858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132375496694970152935557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5686334657853253741161485 2132375496694970152935557)
  ·
    refine ⟨399820405630306903675417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2132375496694970152935557 399820405630306903675417)
    ·
      refine ⟨299865304222730177756563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399820405630306903675417 299865304222730177756563)
      ·
        refine ⟨449797956334095266634845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299865304222730177756563 449797956334095266634845)
        ·
          refine ⟨168674233625285724988067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449797956334095266634845 168674233625285724988067)
          ·
            refine ⟨253011350437928587482101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168674233625285724988067 253011350437928587482101)
            ·
              refine ⟨23719814103555805076447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253011350437928587482101 23719814103555805076447)
              ·
                rfl

theorem cell19_233858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_233858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_233858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_233858 prefixEnd_233858 := by exact prefixLift 233858
  have htrace : WordTrace (prefixWord ++ tailWord_233858) baseStart_233858 baseEnd_233858 := by
    simpa [prefixWord, tailWord_233858, baseEnd_233858] using wordTrace_append hprefix tailTrace_233858
  have hstable : (prefixWord ++ tailWord_233858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233858).length < 2 ^ (prefixWord ++ tailWord_233858).sum := by decide
  have hdescent : baseEnd_233858 < baseStart_233858 := by decide
  rcases family_descends (prefixWord ++ tailWord_233858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234029 : List Nat := [1, 5, 4, 1, 1, 2, 5]
def baseStart_234029 : Nat := 118140960795 + 234029 * 2 ^ 59
def prefixEnd_234029 : Nat := 4983230072969 + 3 ^ 40 * 234029 * 2
def baseEnd_234029 : Nat := 23737158338996561809625

theorem tailTrace_234029 : CollatzResearch.WordTrace tailWord_234029 prefixEnd_234029 23737158338996561809625 := by
  unfold tailWord_234029
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535738869160376816217141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5690492579440251210811427 8535738869160376816217141)
  ·
    refine ⟨800225518983785326520357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8535738869160376816217141 800225518983785326520357)
    ·
      refine ⟨150042284809459748722567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 800225518983785326520357 150042284809459748722567)
      ·
        refine ⟨225063427214189623083851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150042284809459748722567 225063427214189623083851)
        ·
          refine ⟨337595140821284434625777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225063427214189623083851 337595140821284434625777)
          ·
            refine ⟨253196355615963325969333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337595140821284434625777 253196355615963325969333)
            ·
              refine ⟨23737158338996561809625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253196355615963325969333 23737158338996561809625)
              ·
                rfl

theorem cell19_234029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_234029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234029 prefixEnd_234029 := by exact prefixLift 234029
  have htrace : WordTrace (prefixWord ++ tailWord_234029) baseStart_234029 baseEnd_234029 := by
    simpa [prefixWord, tailWord_234029, baseEnd_234029] using wordTrace_append hprefix tailTrace_234029
  have hstable : (prefixWord ++ tailWord_234029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234029).length < 2 ^ (prefixWord ++ tailWord_234029).sum := by decide
  have hdescent : baseEnd_234029 < baseStart_234029 := by decide
  rcases family_descends (prefixWord ++ tailWord_234029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234109 : List Nat := [1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_234109 : Nat := 118140960795 + 234109 * 2 ^ 59
def prefixEnd_234109 : Nat := 4983230072969 + 3 ^ 40 * 234109 * 2
def baseEnd_234109 : Nat := 71235817803573203650879

theorem tailTrace_234109 : CollatzResearch.WordTrace tailWord_234109 prefixEnd_234109 71235817803573203650879 := by
  unfold tailWord_234109
  simp only [CollatzResearch.WordTrace]
  refine ⟨8538656708870550479129381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5692437805913700319419587 8538656708870550479129381)
  ·
    refine ⟨1600998132913228214836759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8538656708870550479129381 1600998132913228214836759)
    ·
      refine ⟨2401497199369842322255139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600998132913228214836759 2401497199369842322255139)
      ·
        refine ⟨3602245799054763483382709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401497199369842322255139 3602245799054763483382709)
        ·
          refine ⟨337710543661384076567129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3602245799054763483382709 337710543661384076567129)
          ·
            refine ⟨253282907746038057425347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337710543661384076567129 253282907746038057425347)
            ·
              refine ⟨379924361619057086138021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253282907746038057425347 379924361619057086138021)
              ·
                refine ⟨71235817803573203650879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379924361619057086138021 71235817803573203650879)
                ·
                  rfl

theorem cell19_234109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_234109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234109 prefixEnd_234109 := by exact prefixLift 234109
  have htrace : WordTrace (prefixWord ++ tailWord_234109) baseStart_234109 baseEnd_234109 := by
    simpa [prefixWord, tailWord_234109, baseEnd_234109] using wordTrace_append hprefix tailTrace_234109
  have hstable : (prefixWord ++ tailWord_234109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234109).length < 2 ^ (prefixWord ++ tailWord_234109).sum := by decide
  have hdescent : baseEnd_234109 < baseStart_234109 := by decide
  rcases family_descends (prefixWord ++ tailWord_234109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234170 : List Nat := [3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_234170 : Nat := 118140960795 + 234170 * 2 ^ 59
def prefixEnd_234170 : Nat := 4983230072969 + 3 ^ 40 * 234170 * 2
def baseEnd_234170 : Nat := 71254379178343136295157

theorem tailTrace_234170 : CollatzResearch.WordTrace tailWord_234170 prefixEnd_234170 71254379178343136295157 := by
  unfold tailWord_234170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135220390412389474274991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5693921041099705264733309 2135220390412389474274991)
  ·
    refine ⟨3202830585618584211412487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2135220390412389474274991 3202830585618584211412487)
    ·
      refine ⟨4804245878427876317118731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202830585618584211412487 4804245878427876317118731)
      ·
        refine ⟨7206368817641814475678097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804245878427876317118731 7206368817641814475678097)
        ·
          refine ⟨5404776613231360856758573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7206368817641814475678097 5404776613231360856758573)
          ·
            refine ⟨2026791229961760321284465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5404776613231360856758573 2026791229961760321284465)
            ·
              refine ⟨1520093422471320240963349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026791229961760321284465 1520093422471320240963349)
              ·
                refine ⟨71254379178343136295157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1520093422471320240963349 71254379178343136295157)
                ·
                  rfl

theorem cell19_234170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_234170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234170 prefixEnd_234170 := by exact prefixLift 234170
  have htrace : WordTrace (prefixWord ++ tailWord_234170) baseStart_234170 baseEnd_234170 := by
    simpa [prefixWord, tailWord_234170, baseEnd_234170] using wordTrace_append hprefix tailTrace_234170
  have hstable : (prefixWord ++ tailWord_234170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234170).length < 2 ^ (prefixWord ++ tailWord_234170).sum := by decide
  have hdescent : baseEnd_234170 < baseStart_234170 := by decide
  rcases family_descends (prefixWord ++ tailWord_234170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234204 : List Nat := [2, 2, 5, 1, 1, 3, 5]
def baseStart_234204 : Nat := 118140960795 + 234204 * 2 ^ 59
def prefixEnd_234204 : Nat := 4983230072969 + 3 ^ 40 * 234204 * 2
def baseEnd_234204 : Nat := 23754908287547043846503

theorem tailTrace_234204 : CollatzResearch.WordTrace tailWord_234204 prefixEnd_234204 23754908287547043846503 := by
  unfold tailWord_234204
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271060821763190851918833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5694747762350921135891777 4271060821763190851918833)
  ·
    refine ⟨3203295616322393138939125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4271060821763190851918833 3203295616322393138939125)
    ·
      refine ⟨300308964030224356775543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3203295616322393138939125 300308964030224356775543)
      ·
        refine ⟨450463446045336535163315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300308964030224356775543 450463446045336535163315)
        ·
          refine ⟨675695169068004802744973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450463446045336535163315 675695169068004802744973)
          ·
            refine ⟨253385688400501801029365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675695169068004802744973 253385688400501801029365)
            ·
              refine ⟨23754908287547043846503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253385688400501801029365 23754908287547043846503)
              ·
                rfl

theorem cell19_234204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_234204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234204 prefixEnd_234204 := by exact prefixLift 234204
  have htrace : WordTrace (prefixWord ++ tailWord_234204) baseStart_234204 baseEnd_234204 := by
    simpa [prefixWord, tailWord_234204, baseEnd_234204] using wordTrace_append hprefix tailTrace_234204
  have hstable : (prefixWord ++ tailWord_234204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234204).length < 2 ^ (prefixWord ++ tailWord_234204).sum := by decide
  have hdescent : baseEnd_234204 < baseStart_234204 := by decide
  rcases family_descends (prefixWord ++ tailWord_234204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234263 : List Nat := [1, 1, 3, 4, 4, 6]
def baseStart_234263 : Nat := 118140960795 + 234263 * 2 ^ 59
def prefixEnd_234263 : Nat := 4983230072969 + 3 ^ 40 * 234263 * 2
def baseEnd_234263 : Nat := 7920297518638497358693

theorem tailTrace_234263 : CollatzResearch.WordTrace tailWord_234263 prefixEnd_234263 7920297518638497358693 := by
  unfold tailWord_234263
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544273550312634780235443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5696182366875089853490295 8544273550312634780235443)
  ·
    refine ⟨12816410325468952170353165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8544273550312634780235443 12816410325468952170353165)
    ·
      refine ⟨4806153872050857063882437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12816410325468952170353165 4806153872050857063882437)
      ·
        refine ⟨901153851009535699477957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4806153872050857063882437 901153851009535699477957)
        ·
          refine ⟨168966347064287943652117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 901153851009535699477957 168966347064287943652117)
          ·
            refine ⟨7920297518638497358693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168966347064287943652117 7920297518638497358693)
            ·
              rfl

theorem cell19_234263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 6].length) (baseStart_234263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234263 prefixEnd_234263 := by exact prefixLift 234263
  have htrace : WordTrace (prefixWord ++ tailWord_234263) baseStart_234263 baseEnd_234263 := by
    simpa [prefixWord, tailWord_234263, baseEnd_234263] using wordTrace_append hprefix tailTrace_234263
  have hstable : (prefixWord ++ tailWord_234263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234263).length < 2 ^ (prefixWord ++ tailWord_234263).sum := by decide
  have hdescent : baseEnd_234263 < baseStart_234263 := by decide
  rcases family_descends (prefixWord ++ tailWord_234263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234322 : List Nat := [3, 2, 2, 1, 1, 2, 8]
def baseStart_234322 : Nat := 118140960795 + 234322 * 2 ^ 59
def prefixEnd_234322 : Nat := 4983230072969 + 3 ^ 40 * 234322 * 2
def baseEnd_234322 : Nat := 23766876824283940305655

theorem tailTrace_234322 : CollatzResearch.WordTrace tailWord_234322 prefixEnd_234322 23766876824283940305655 := by
  unfold tailWord_234322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136606364274721964158305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5697616971399258571088813 2136606364274721964158305)
  ·
    refine ⟨1602454773206041473118729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2136606364274721964158305 1602454773206041473118729)
    ·
      refine ⟨1201841079904531104839047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1602454773206041473118729 1201841079904531104839047)
      ·
        refine ⟨1802761619856796657258571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201841079904531104839047 1802761619856796657258571)
        ·
          refine ⟨2704142429785194985887857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802761619856796657258571 2704142429785194985887857)
          ·
            refine ⟨2028106822338896239415893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704142429785194985887857 2028106822338896239415893)
            ·
              refine ⟨23766876824283940305655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2028106822338896239415893 23766876824283940305655)
              ·
                rfl

theorem cell19_234322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_234322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234322 prefixEnd_234322 := by exact prefixLift 234322
  have htrace : WordTrace (prefixWord ++ tailWord_234322) baseStart_234322 baseEnd_234322 := by
    simpa [prefixWord, tailWord_234322, baseEnd_234322] using wordTrace_append hprefix tailTrace_234322
  have hstable : (prefixWord ++ tailWord_234322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234322).length < 2 ^ (prefixWord ++ tailWord_234322).sum := by decide
  have hdescent : baseEnd_234322 < baseStart_234322 := by decide
  rcases family_descends (prefixWord ++ tailWord_234322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234445 : List Nat := [1, 6, 3, 1, 2, 1, 1, 4]
def baseStart_234445 : Nat := 118140960795 + 234445 * 2 ^ 59
def prefixEnd_234445 : Nat := 4983230072969 + 3 ^ 40 * 234445 * 2
def baseEnd_234445 : Nat := 71338057507223980183297

theorem tailTrace_234445 : CollatzResearch.WordTrace tailWord_234445 prefixEnd_234445 71338057507223980183297 := by
  unfold tailWord_234445
  simp only [CollatzResearch.WordTrace]
  refine ⟨8550911635653279863360789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5700607757102186575573859 8550911635653279863360789)
  ·
    refine ⟨400823982921247493595037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8550911635653279863360789 400823982921247493595037)
    ·
      refine ⟨150308993595467810098139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400823982921247493595037 150308993595467810098139)
      ·
        refine ⟨225463490393201715147209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150308993595467810098139 225463490393201715147209)
        ·
          refine ⟨169097617794901286360407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225463490393201715147209 169097617794901286360407)
          ·
            refine ⟨253646426692351929540611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169097617794901286360407 253646426692351929540611)
            ·
              refine ⟨380469640038527894310917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253646426692351929540611 380469640038527894310917)
              ·
                refine ⟨71338057507223980183297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380469640038527894310917 71338057507223980183297)
                ·
                  rfl

theorem cell19_234445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_234445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234445 prefixEnd_234445 := by exact prefixLift 234445
  have htrace : WordTrace (prefixWord ++ tailWord_234445) baseStart_234445 baseEnd_234445 := by
    simpa [prefixWord, tailWord_234445, baseEnd_234445] using wordTrace_append hprefix tailTrace_234445
  have hstable : (prefixWord ++ tailWord_234445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234445).length < 2 ^ (prefixWord ++ tailWord_234445).sum := by decide
  have hdescent : baseEnd_234445 < baseStart_234445 := by decide
  rcases family_descends (prefixWord ++ tailWord_234445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234525 : List Nat := [1, 4, 2, 2, 4, 1, 2, 3]
def baseStart_234525 : Nat := 118140960795 + 234525 * 2 ^ 59
def prefixEnd_234525 : Nat := 4983230072969 + 3 ^ 40 * 234525 * 2
def baseEnd_234525 : Nat := 71362400293807498405301

theorem tailTrace_234525 : CollatzResearch.WordTrace tailWord_234525 prefixEnd_234525 71362400293807498405301 := by
  unfold tailWord_234525
  simp only [CollatzResearch.WordTrace]
  refine ⟨8553829475363453526273029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5702552983575635684182019 8553829475363453526273029)
  ·
    refine ⟨1603843026630647536176193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8553829475363453526273029 1603843026630647536176193)
    ·
      refine ⟨1202882269972985652132145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1603843026630647536176193 1202882269972985652132145)
      ·
        refine ⟨902161702479739239099109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1202882269972985652132145 902161702479739239099109)
        ·
          refine ⟨169155319214951107331083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 902161702479739239099109 169155319214951107331083)
          ·
            refine ⟨253732978822426660996625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169155319214951107331083 253732978822426660996625)
            ·
              refine ⟨190299734116819995747469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253732978822426660996625 190299734116819995747469)
              ·
                refine ⟨71362400293807498405301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190299734116819995747469 71362400293807498405301)
                ·
                  rfl

theorem cell19_234525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_234525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234525 prefixEnd_234525 := by exact prefixLift 234525
  have htrace : WordTrace (prefixWord ++ tailWord_234525) baseStart_234525 baseEnd_234525 := by
    simpa [prefixWord, tailWord_234525, baseEnd_234525] using wordTrace_append hprefix tailTrace_234525
  have hstable : (prefixWord ++ tailWord_234525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234525).length < 2 ^ (prefixWord ++ tailWord_234525).sum := by decide
  have hdescent : baseEnd_234525 < baseStart_234525 := by decide
  rcases family_descends (prefixWord ++ tailWord_234525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234529 : List Nat := [1, 2, 3, 2, 3, 1, 4, 3]
def baseStart_234529 : Nat := 118140960795 + 234529 * 2 ^ 59
def prefixEnd_234529 : Nat := 4983230072969 + 3 ^ 40 * 234529 * 2
def baseEnd_234529 : Nat := 71363617433136674316401

theorem tailTrace_234529 : CollatzResearch.WordTrace tailWord_234529 prefixEnd_234529 71363617433136674316401 := by
  unfold tailWord_234529
  simp only [CollatzResearch.WordTrace]
  refine ⟨8553975367348962209418641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5702650244899308139612427 8553975367348962209418641)
  ·
    refine ⟨6415481525511721657063981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8553975367348962209418641 6415481525511721657063981)
    ·
      refine ⟨2405805572066895621398993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6415481525511721657063981 2405805572066895621398993)
      ·
        refine ⟨1804354179050171716049245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2405805572066895621398993 1804354179050171716049245)
        ·
          refine ⟨676632817143814393518467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1804354179050171716049245 676632817143814393518467)
          ·
            refine ⟨1014949225715721590277701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676632817143814393518467 1014949225715721590277701)
            ·
              refine ⟨190302979821697798177069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1014949225715721590277701 190302979821697798177069)
              ·
                refine ⟨71363617433136674316401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190302979821697798177069 71363617433136674316401)
                ·
                  rfl

theorem cell19_234529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_234529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234529 prefixEnd_234529 := by exact prefixLift 234529
  have htrace : WordTrace (prefixWord ++ tailWord_234529) baseStart_234529 baseEnd_234529 := by
    simpa [prefixWord, tailWord_234529, baseEnd_234529] using wordTrace_append hprefix tailTrace_234529
  have hstable : (prefixWord ++ tailWord_234529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234529).length < 2 ^ (prefixWord ++ tailWord_234529).sum := by decide
  have hdescent : baseEnd_234529 < baseStart_234529 := by decide
  rcases family_descends (prefixWord ++ tailWord_234529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234531 : List Nat := [1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_234531 : Nat := 118140960795 + 234531 * 2 ^ 59
def prefixEnd_234531 : Nat := 4983230072969 + 3 ^ 40 * 234531 * 2
def baseEnd_234531 : Nat := 71364226002801262271951

theorem tailTrace_234531 : CollatzResearch.WordTrace tailWord_234531 prefixEnd_234531 71364226002801262271951 := by
  unfold tailWord_234531
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554048313341716550991447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5702698875561144367327631 8554048313341716550991447)
  ·
    refine ⟨12831072470012574826487171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8554048313341716550991447 12831072470012574826487171)
    ·
      refine ⟨19246608705018862239730757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12831072470012574826487171 19246608705018862239730757)
      ·
        refine ⟨3608739132191036669949517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19246608705018862239730757 3608739132191036669949517)
        ·
          refine ⟨1353277174571638751231069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3608739132191036669949517 1353277174571638751231069)
          ·
            refine ⟨507478940464364531711651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1353277174571638751231069 507478940464364531711651)
            ·
              refine ⟨761218410696546797567477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507478940464364531711651 761218410696546797567477)
              ·
                refine ⟨71364226002801262271951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 761218410696546797567477 71364226002801262271951)
                ·
                  rfl

theorem cell19_234531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_234531 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234531 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234531 prefixEnd_234531 := by exact prefixLift 234531
  have htrace : WordTrace (prefixWord ++ tailWord_234531) baseStart_234531 baseEnd_234531 := by
    simpa [prefixWord, tailWord_234531, baseEnd_234531] using wordTrace_append hprefix tailTrace_234531
  have hstable : (prefixWord ++ tailWord_234531).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234531).length < 2 ^ (prefixWord ++ tailWord_234531).sum := by decide
  have hdescent : baseEnd_234531 < baseStart_234531 := by decide
  rcases family_descends (prefixWord ++ tailWord_234531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234548 : List Nat := [2, 5, 1, 2, 1, 1, 7]
def baseStart_234548 : Nat := 118140960795 + 234548 * 2 ^ 59
def prefixEnd_234548 : Nat := 4983230072969 + 3 ^ 40 * 234548 * 2
def baseEnd_234548 : Nat := 23789799614983419964709

theorem tailTrace_234548 : CollatzResearch.WordTrace tailWord_234548 prefixEnd_234548 23789799614983419964709 := by
  unfold tailWord_234548
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277334177140064227180149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5703112236186752302906865 4277334177140064227180149)
  ·
    refine ⟨401000079106881021298139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4277334177140064227180149 401000079106881021298139)
    ·
      refine ⟨601500118660321531947209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401000079106881021298139 601500118660321531947209)
      ·
        refine ⟨451125088995241148960407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601500118660321531947209 451125088995241148960407)
        ·
          refine ⟨676687633492861723440611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451125088995241148960407 676687633492861723440611)
          ·
            refine ⟨1015031450239292585160917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676687633492861723440611 1015031450239292585160917)
            ·
              refine ⟨23789799614983419964709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1015031450239292585160917 23789799614983419964709)
              ·
                rfl

theorem cell19_234548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_234548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234548 prefixEnd_234548 := by exact prefixLift 234548
  have htrace : WordTrace (prefixWord ++ tailWord_234548) baseStart_234548 baseEnd_234548 := by
    simpa [prefixWord, tailWord_234548, baseEnd_234548] using wordTrace_append hprefix tailTrace_234548
  have hstable : (prefixWord ++ tailWord_234548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234548).length < 2 ^ (prefixWord ++ tailWord_234548).sum := by decide
  have hdescent : baseEnd_234548 < baseStart_234548 := by decide
  rcases family_descends (prefixWord ++ tailWord_234548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234588 : List Nat := [2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_234588 : Nat := 118140960795 + 234588 * 2 ^ 59
def prefixEnd_234588 : Nat := 4983230072969 + 3 ^ 40 * 234588 * 2
def baseEnd_234588 : Nat := 71381570238242019005129

theorem tailTrace_234588 : CollatzResearch.WordTrace tailWord_234588 prefixEnd_234588 71381570238242019005129 := by
  unfold tailWord_234588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278063637067607642908209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5704084849423476857210945 4278063637067607642908209)
  ·
    refine ⟨3208547727800705732181157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4278063637067607642908209 3208547727800705732181157)
    ·
      refine ⟨601602698962632324783967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3208547727800705732181157 601602698962632324783967)
      ·
        refine ⟨902404048443948487175951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601602698962632324783967 902404048443948487175951)
        ·
          refine ⟨1353606072665922730763927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902404048443948487175951 1353606072665922730763927)
          ·
            refine ⟨2030409108998884096145891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353606072665922730763927 2030409108998884096145891)
            ·
              refine ⟨3045613663498326144218837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030409108998884096145891 3045613663498326144218837)
              ·
                refine ⟨71381570238242019005129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3045613663498326144218837 71381570238242019005129)
                ·
                  rfl

theorem cell19_234588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_234588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234588 prefixEnd_234588 := by exact prefixLift 234588
  have htrace : WordTrace (prefixWord ++ tailWord_234588) baseStart_234588 baseEnd_234588 := by
    simpa [prefixWord, tailWord_234588, baseEnd_234588] using wordTrace_append hprefix tailTrace_234588
  have hstable : (prefixWord ++ tailWord_234588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234588).length < 2 ^ (prefixWord ++ tailWord_234588).sum := by decide
  have hdescent : baseEnd_234588 < baseStart_234588 := by decide
  rcases family_descends (prefixWord ++ tailWord_234588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234717 : List Nat := [1, 4, 3, 2, 3, 1, 5]
def baseStart_234717 : Nat := 118140960795 + 234717 * 2 ^ 59
def prefixEnd_234717 : Nat := 4983230072969 + 3 ^ 40 * 234717 * 2
def baseEnd_234717 : Nat := 23806940993869314046037

theorem tailTrace_234717 : CollatzResearch.WordTrace tailWord_234717 prefixEnd_234717 23806940993869314046037 := by
  unfold tailWord_234717
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560832290667870317262405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5707221527111913544841603 8560832290667870317262405)
  ·
    refine ⟨1605156054500225684486701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8560832290667870317262405 1605156054500225684486701)
    ·
      refine ⟨601933520437584631682513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1605156054500225684486701 601933520437584631682513)
      ·
        refine ⟨451450140328188473761885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601933520437584631682513 451450140328188473761885)
        ·
          refine ⟨169293802623070677660707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451450140328188473761885 169293802623070677660707)
          ·
            refine ⟨253940703934606016491061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169293802623070677660707 253940703934606016491061)
            ·
              refine ⟨23806940993869314046037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253940703934606016491061 23806940993869314046037)
              ·
                rfl

theorem cell19_234717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_234717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234717 prefixEnd_234717 := by exact prefixLift 234717
  have htrace : WordTrace (prefixWord ++ tailWord_234717) baseStart_234717 baseEnd_234717 := by
    simpa [prefixWord, tailWord_234717, baseEnd_234717] using wordTrace_append hprefix tailTrace_234717
  have hstable : (prefixWord ++ tailWord_234717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234717).length < 2 ^ (prefixWord ++ tailWord_234717).sum := by decide
  have hdescent : baseEnd_234717 < baseStart_234717 := by decide
  rcases family_descends (prefixWord ++ tailWord_234717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234721 : List Nat := [1, 2, 3, 1, 3, 4, 5]
def baseStart_234721 : Nat := 118140960795 + 234721 * 2 ^ 59
def prefixEnd_234721 : Nat := 4983230072969 + 3 ^ 40 * 234721 * 2
def baseEnd_234721 : Nat := 23807346706979039349737

theorem tailTrace_234721 : CollatzResearch.WordTrace tailWord_234721 prefixEnd_234721 23807346706979039349737 := by
  unfold tailWord_234721
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560978182653379000408017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5707318788435586000272011 8560978182653379000408017)
  ·
    refine ⟨6420733636990034250306013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8560978182653379000408017 6420733636990034250306013)
    ·
      refine ⟨2407775113871262843864755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6420733636990034250306013 2407775113871262843864755)
      ·
        refine ⟨3611662670806894265797133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407775113871262843864755 3611662670806894265797133)
        ·
          refine ⟨1354373501552585349673925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3611662670806894265797133 1354373501552585349673925)
          ·
            refine ⟨253945031541109753063861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1354373501552585349673925 253945031541109753063861)
            ·
              refine ⟨23807346706979039349737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253945031541109753063861 23807346706979039349737)
              ·
                rfl

theorem cell19_234721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_234721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234721 prefixEnd_234721 := by exact prefixLift 234721
  have htrace : WordTrace (prefixWord ++ tailWord_234721) baseStart_234721 baseEnd_234721 := by
    simpa [prefixWord, tailWord_234721, baseEnd_234721] using wordTrace_append hprefix tailTrace_234721
  have hstable : (prefixWord ++ tailWord_234721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234721).length < 2 ^ (prefixWord ++ tailWord_234721).sum := by decide
  have hdescent : baseEnd_234721 < baseStart_234721 := by decide
  rcases family_descends (prefixWord ++ tailWord_234721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234738 : List Nat := [3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_234738 : Nat := 118140960795 + 234738 * 2 ^ 59
def prefixEnd_234738 : Nat := 4983230072969 + 3 ^ 40 * 234738 * 2
def baseEnd_234738 : Nat := 71427212963086115671387

theorem tailTrace_234738 : CollatzResearch.WordTrace tailWord_234738 prefixEnd_234738 71427212963086115671387 := by
  unfold tailWord_234738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140399555897947725944217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5707732149061193935851245 2140399555897947725944217)
  ·
    refine ⟨1605299666923460794458163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2140399555897947725944217 1605299666923460794458163)
    ·
      refine ⟨2407949500385191191687245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1605299666923460794458163 2407949500385191191687245)
      ·
        refine ⟨902981062644446696882717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2407949500385191191687245 902981062644446696882717)
        ·
          refine ⟨338617898491667511331019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902981062644446696882717 338617898491667511331019)
          ·
            refine ⟨507926847737501266996529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338617898491667511331019 507926847737501266996529)
            ·
              refine ⟨380945135803125950247397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507926847737501266996529 380945135803125950247397)
              ·
                refine ⟨71427212963086115671387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380945135803125950247397 71427212963086115671387)
                ·
                  rfl

theorem cell19_234738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_234738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234738 prefixEnd_234738 := by exact prefixLift 234738
  have htrace : WordTrace (prefixWord ++ tailWord_234738) baseStart_234738 baseEnd_234738 := by
    simpa [prefixWord, tailWord_234738, baseEnd_234738] using wordTrace_append hprefix tailTrace_234738
  have hstable : (prefixWord ++ tailWord_234738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234738).length < 2 ^ (prefixWord ++ tailWord_234738).sum := by decide
  have hdescent : baseEnd_234738 < baseStart_234738 := by decide
  rcases family_descends (prefixWord ++ tailWord_234738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234761 : List Nat := [1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_234761 : Nat := 118140960795 + 234761 * 2 ^ 59
def prefixEnd_234761 : Nat := 4983230072969 + 3 ^ 40 * 234761 * 2
def baseEnd_234761 : Nat := 71434211514228877160213

theorem tailTrace_234761 : CollatzResearch.WordTrace tailWord_234761 prefixEnd_234761 71434211514228877160213 := by
  unfold tailWord_234761
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562437102508465831864137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5708291401672310554576091 8562437102508465831864137)
  ·
    refine ⟨6421827826881349373898103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8562437102508465831864137 6421827826881349373898103)
    ·
      refine ⟨9632741740322024060847155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421827826881349373898103 9632741740322024060847155)
      ·
        refine ⟨14449112610483036091270733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632741740322024060847155 14449112610483036091270733)
        ·
          refine ⟨5418417228931138534226525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14449112610483036091270733 5418417228931138534226525)
          ·
            refine ⟨2031906460849176950334947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5418417228931138534226525 2031906460849176950334947)
            ·
              refine ⟨3047859691273765425502421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031906460849176950334947 3047859691273765425502421)
              ·
                refine ⟨71434211514228877160213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3047859691273765425502421 71434211514228877160213)
                ·
                  rfl

theorem cell19_234761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_234761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234761 prefixEnd_234761 := by exact prefixLift 234761
  have htrace : WordTrace (prefixWord ++ tailWord_234761) baseStart_234761 baseEnd_234761 := by
    simpa [prefixWord, tailWord_234761, baseEnd_234761] using wordTrace_append hprefix tailTrace_234761
  have hstable : (prefixWord ++ tailWord_234761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234761).length < 2 ^ (prefixWord ++ tailWord_234761).sum := by decide
  have hdescent : baseEnd_234761 < baseStart_234761 := by decide
  rcases family_descends (prefixWord ++ tailWord_234761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234814 : List Nat := [4, 2, 1, 2, 1, 1, 5, 3]
def baseStart_234814 : Nat := 118140960795 + 234814 * 2 ^ 59
def prefixEnd_234814 : Nat := 4983230072969 + 3 ^ 40 * 234814 * 2
def baseEnd_234814 : Nat := 71450338610340457982291

theorem tailTrace_234814 : CollatzResearch.WordTrace tailWord_234814 prefixEnd_234814 71450338610340457982291 := by
  unfold tailWord_234814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070546271414556985442937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5709580114210970589028997 1070546271414556985442937)
  ·
    refine ⟨802909703560917739082203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1070546271414556985442937 802909703560917739082203)
    ·
      refine ⟨1204364555341376608623305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802909703560917739082203 1204364555341376608623305)
      ·
        refine ⟨903273416506032456467479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204364555341376608623305 903273416506032456467479)
        ·
          refine ⟨1354910124759048684701219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903273416506032456467479 1354910124759048684701219)
          ·
            refine ⟨2032365187138573027051829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354910124759048684701219 2032365187138573027051829)
            ·
              refine ⟨190534236294241221286109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2032365187138573027051829 190534236294241221286109)
              ·
                refine ⟨71450338610340457982291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190534236294241221286109 71450338610340457982291)
                ·
                  rfl

theorem cell19_234814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_234814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234814 prefixEnd_234814 := by exact prefixLift 234814
  have htrace : WordTrace (prefixWord ++ tailWord_234814) baseStart_234814 baseEnd_234814 := by
    simpa [prefixWord, tailWord_234814, baseEnd_234814] using wordTrace_append hprefix tailTrace_234814
  have hstable : (prefixWord ++ tailWord_234814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234814).length < 2 ^ (prefixWord ++ tailWord_234814).sum := by decide
  have hdescent : baseEnd_234814 < baseStart_234814 := by decide
  rcases family_descends (prefixWord ++ tailWord_234814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234816 : List Nat := [2, 1, 1, 2, 2, 1, 7, 3]
def baseStart_234816 : Nat := 118140960795 + 234816 * 2 ^ 59
def prefixEnd_234816 : Nat := 4983230072969 + 3 ^ 40 * 234816 * 2
def baseEnd_234816 : Nat := 71450947180005045937841

theorem tailTrace_234816 : CollatzResearch.WordTrace tailWord_234816 prefixEnd_234816 71450947180005045937841 := by
  unfold tailWord_234816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282221558654605112558151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5709628744872806816744201 4282221558654605112558151)
  ·
    refine ⟨6423332337981907668837227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4282221558654605112558151 6423332337981907668837227)
    ·
      refine ⟨9634998506972861503255841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6423332337981907668837227 9634998506972861503255841)
      ·
        refine ⟨7226248880229646127441881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9634998506972861503255841 7226248880229646127441881)
        ·
          refine ⟨5419686660172234595581411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7226248880229646127441881 5419686660172234595581411)
          ·
            refine ⟨8129529990258351893372117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5419686660172234595581411 8129529990258351893372117)
            ·
              refine ⟨190535859146680122500909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8129529990258351893372117 190535859146680122500909)
              ·
                refine ⟨71450947180005045937841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190535859146680122500909 71450947180005045937841)
                ·
                  rfl

theorem cell19_234816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_234816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234816 prefixEnd_234816 := by exact prefixLift 234816
  have htrace : WordTrace (prefixWord ++ tailWord_234816) baseStart_234816 baseEnd_234816 := by
    simpa [prefixWord, tailWord_234816, baseEnd_234816] using wordTrace_append hprefix tailTrace_234816
  have hstable : (prefixWord ++ tailWord_234816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234816).length < 2 ^ (prefixWord ++ tailWord_234816).sum := by decide
  have hdescent : baseEnd_234816 < baseStart_234816 := by decide
  rcases family_descends (prefixWord ++ tailWord_234816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234869 : List Nat := [1, 3, 4, 1, 3, 2, 2, 3]
def baseStart_234869 : Nat := 118140960795 + 234869 * 2 ^ 59
def prefixEnd_234869 : Nat := 4983230072969 + 3 ^ 40 * 234869 * 2
def baseEnd_234869 : Nat := 71467074276116626759919

theorem tailTrace_234869 : CollatzResearch.WordTrace tailWord_234869 prefixEnd_234869 71467074276116626759919 := by
  unfold tailWord_234869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566376186117200276795661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5710917457411466851197107 8566376186117200276795661)
  ·
    refine ⟨3212391069793950103798373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8566376186117200276795661 3212391069793950103798373)
    ·
      refine ⟨602323325586365644462195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3212391069793950103798373 602323325586365644462195)
      ·
        refine ⟨903484988379548466693293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602323325586365644462195 903484988379548466693293)
        ·
          refine ⟨338806870642330675009985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 903484988379548466693293 338806870642330675009985)
          ·
            refine ⟨254105152981748006257489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338806870642330675009985 254105152981748006257489)
            ·
              refine ⟨190578864736311004693117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254105152981748006257489 190578864736311004693117)
              ·
                refine ⟨71467074276116626759919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190578864736311004693117 71467074276116626759919)
                ·
                  rfl

theorem cell19_234869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_234869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234869 prefixEnd_234869 := by exact prefixLift 234869
  have htrace : WordTrace (prefixWord ++ tailWord_234869) baseStart_234869 baseEnd_234869 := by
    simpa [prefixWord, tailWord_234869, baseEnd_234869] using wordTrace_append hprefix tailTrace_234869
  have hstable : (prefixWord ++ tailWord_234869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234869).length < 2 ^ (prefixWord ++ tailWord_234869).sum := by decide
  have hdescent : baseEnd_234869 < baseStart_234869 := by decide
  rcases family_descends (prefixWord ++ tailWord_234869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234873 : List Nat := [1, 2, 1, 3, 2, 1, 6, 3]
def baseStart_234873 : Nat := 118140960795 + 234873 * 2 ^ 59
def prefixEnd_234873 : Nat := 4983230072969 + 3 ^ 40 * 234873 * 2
def baseEnd_234873 : Nat := 71468291415445802671019

theorem tailTrace_234873 : CollatzResearch.WordTrace tailWord_234873 prefixEnd_234873 71468291415445802671019 := by
  unfold tailWord_234873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566522078102708959941273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5711014718735139306627515 8566522078102708959941273)
  ·
    refine ⟨6424891558577031719955955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8566522078102708959941273 6424891558577031719955955)
    ·
      refine ⟨9637337337865547579933933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424891558577031719955955 9637337337865547579933933)
      ·
        refine ⟨3614001501699580342475225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9637337337865547579933933 3614001501699580342475225)
        ·
          refine ⟨2710501126274685256856419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614001501699580342475225 2710501126274685256856419)
          ·
            refine ⟨4065751689412027885284629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710501126274685256856419 4065751689412027885284629)
            ·
              refine ⟨190582110441188807122717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4065751689412027885284629 190582110441188807122717)
              ·
                refine ⟨71468291415445802671019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190582110441188807122717 71468291415445802671019)
                ·
                  rfl

theorem cell19_234873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_234873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234873 prefixEnd_234873 := by exact prefixLift 234873
  have htrace : WordTrace (prefixWord ++ tailWord_234873) baseStart_234873 baseEnd_234873 := by
    simpa [prefixWord, tailWord_234873, baseEnd_234873] using wordTrace_append hprefix tailTrace_234873
  have hstable : (prefixWord ++ tailWord_234873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234873).length < 2 ^ (prefixWord ++ tailWord_234873).sum := by decide
  have hdescent : baseEnd_234873 < baseStart_234873 := by decide
  rcases family_descends (prefixWord ++ tailWord_234873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234875 : List Nat := [1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_234875 : Nat := 118140960795 + 234875 * 2 ^ 59
def prefixEnd_234875 : Nat := 4983230072969 + 3 ^ 40 * 234875 * 2
def baseEnd_234875 : Nat := 71468899985110390626569

theorem tailTrace_234875 : CollatzResearch.WordTrace tailWord_234875 prefixEnd_234875 71468899985110390626569 := by
  unfold tailWord_234875
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566595024095463301514079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5711063349396975534342719 8566595024095463301514079)
  ·
    refine ⟨12849892536143194952271119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8566595024095463301514079 12849892536143194952271119)
    ·
      refine ⟨19274838804214792428406679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12849892536143194952271119 19274838804214792428406679)
      ·
        refine ⟨28912258206322188642610019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19274838804214792428406679 28912258206322188642610019)
        ·
          refine ⟨43368387309483282963915029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28912258206322188642610019 43368387309483282963915029)
          ·
            refine ⟨2032893155132028888933517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43368387309483282963915029 2032893155132028888933517)
            ·
              refine ⟨762334933174510833350069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2032893155132028888933517 762334933174510833350069)
              ·
                refine ⟨71468899985110390626569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 762334933174510833350069 71468899985110390626569)
                ·
                  rfl

theorem cell19_234875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_234875 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234875 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234875 prefixEnd_234875 := by exact prefixLift 234875
  have htrace : WordTrace (prefixWord ++ tailWord_234875) baseStart_234875 baseEnd_234875 := by
    simpa [prefixWord, tailWord_234875, baseEnd_234875] using wordTrace_append hprefix tailTrace_234875
  have hstable : (prefixWord ++ tailWord_234875).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234875).length < 2 ^ (prefixWord ++ tailWord_234875).sum := by decide
  have hdescent : baseEnd_234875 < baseStart_234875 := by decide
  rcases family_descends (prefixWord ++ tailWord_234875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234911 : List Nat := [1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_234911 : Nat := 118140960795 + 234911 * 2 ^ 59
def prefixEnd_234911 : Nat := 4983230072969 + 3 ^ 40 * 234911 * 2
def baseEnd_234911 : Nat := 71479854239072973826471

theorem tailTrace_234911 : CollatzResearch.WordTrace tailWord_234911 prefixEnd_234911 71479854239072973826471 := by
  unfold tailWord_234911
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567908051965041449824587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5711938701310027633216391 8567908051965041449824587)
  ·
    refine ⟨12851862077947562174736881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8567908051965041449824587 12851862077947562174736881)
    ·
      refine ⟨9638896558460671631052661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12851862077947562174736881 9638896558460671631052661)
      ·
        refine ⟨903646552355687965411187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9638896558460671631052661 903646552355687965411187)
        ·
          refine ⟨1355469828533531948116781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903646552355687965411187 1355469828533531948116781)
          ·
            refine ⟨508301185700074480543793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1355469828533531948116781 508301185700074480543793)
            ·
              refine ⟨381225889275055860407845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508301185700074480543793 381225889275055860407845)
              ·
                refine ⟨71479854239072973826471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381225889275055860407845 71479854239072973826471)
                ·
                  rfl

theorem cell19_234911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_234911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234911 prefixEnd_234911 := by exact prefixLift 234911
  have htrace : WordTrace (prefixWord ++ tailWord_234911) baseStart_234911 baseEnd_234911 := by
    simpa [prefixWord, tailWord_234911, baseEnd_234911] using wordTrace_append hprefix tailTrace_234911
  have hstable : (prefixWord ++ tailWord_234911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234911).length < 2 ^ (prefixWord ++ tailWord_234911).sum := by decide
  have hdescent : baseEnd_234911 < baseStart_234911 := by decide
  rcases family_descends (prefixWord ++ tailWord_234911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234964 : List Nat := [2, 4, 1, 2, 4, 1, 1, 4]
def baseStart_234964 : Nat := 118140960795 + 234964 * 2 ^ 59
def prefixEnd_234964 : Nat := 4983230072969 + 3 ^ 40 * 234964 * 2
def baseEnd_234964 : Nat := 71495981335184554648549

theorem tailTrace_234964 : CollatzResearch.WordTrace tailWord_234964 prefixEnd_234964 71495981335184554648549 := by
  unfold tailWord_234964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284920560386515750751973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5713227413848687667669297 4284920560386515750751973)
  ·
    refine ⟨803422605072471703265995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4284920560386515750751973 803422605072471703265995)
    ·
      refine ⟨1205133907608707554898993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803422605072471703265995 1205133907608707554898993)
      ·
        refine ⟨903850430706530666174245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1205133907608707554898993 903850430706530666174245)
        ·
          refine ⟨169471955757474499907671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 903850430706530666174245 169471955757474499907671)
          ·
            refine ⟨254207933636211749861507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169471955757474499907671 254207933636211749861507)
            ·
              refine ⟨381311900454317624792261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254207933636211749861507 381311900454317624792261)
              ·
                refine ⟨71495981335184554648549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381311900454317624792261 71495981335184554648549)
                ·
                  rfl

theorem cell19_234964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_234964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234964 prefixEnd_234964 := by exact prefixLift 234964
  have htrace : WordTrace (prefixWord ++ tailWord_234964) baseStart_234964 baseEnd_234964 := by
    simpa [prefixWord, tailWord_234964, baseEnd_234964] using wordTrace_append hprefix tailTrace_234964
  have hstable : (prefixWord ++ tailWord_234964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234964).length < 2 ^ (prefixWord ++ tailWord_234964).sum := by decide
  have hdescent : baseEnd_234964 < baseStart_234964 := by decide
  rcases family_descends (prefixWord ++ tailWord_234964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234966 : List Nat := [5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_234966 : Nat := 118140960795 + 234966 * 2 ^ 59
def prefixEnd_234966 : Nat := 4983230072969 + 3 ^ 40 * 234966 * 2
def baseEnd_234966 : Nat := 71496589904849142604099

theorem tailTrace_234966 : CollatzResearch.WordTrace tailWord_234966 prefixEnd_234966 71496589904849142604099 := by
  unfold tailWord_234966
  simp only [CollatzResearch.WordTrace]
  refine ⟨535619629172861615192297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5713276044510523895384501 535619629172861615192297)
  ·
    refine ⟨401714721879646211394223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 535619629172861615192297 401714721879646211394223)
    ·
      refine ⟨602572082819469317091335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401714721879646211394223 602572082819469317091335)
      ·
        refine ⟨903858124229203975637003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602572082819469317091335 903858124229203975637003)
        ·
          refine ⟨1355787186343805963455505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903858124229203975637003 1355787186343805963455505)
          ·
            refine ⟨1016840389757854472591629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355787186343805963455505 1016840389757854472591629)
            ·
              refine ⟨381315146159195427221861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1016840389757854472591629 381315146159195427221861)
              ·
                refine ⟨71496589904849142604099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381315146159195427221861 71496589904849142604099)
                ·
                  rfl

theorem cell19_234966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_234966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_234966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_234966 prefixEnd_234966 := by exact prefixLift 234966
  have htrace : WordTrace (prefixWord ++ tailWord_234966) baseStart_234966 baseEnd_234966 := by
    simpa [prefixWord, tailWord_234966, baseEnd_234966] using wordTrace_append hprefix tailTrace_234966
  have hstable : (prefixWord ++ tailWord_234966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234966).length < 2 ^ (prefixWord ++ tailWord_234966).sum := by decide
  have hdescent : baseEnd_234966 < baseStart_234966 := by decide
  rcases family_descends (prefixWord ++ tailWord_234966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235038 : List Nat := [4, 3, 3, 1, 1, 1, 1, 5]
def baseStart_235038 : Nat := 118140960795 + 235038 * 2 ^ 59
def prefixEnd_235038 : Nat := 4983230072969 + 3 ^ 40 * 235038 * 2
def baseEnd_235038 : Nat := 71518498412774309003903

theorem tailTrace_235038 : CollatzResearch.WordTrace tailWord_235038 prefixEnd_235038 71518498412774309003903 := by
  unfold tailWord_235038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071567515313117767462221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5715026748336628093131845 1071567515313117767462221)
  ·
    refine ⟨401837818242419162798333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1071567515313117767462221 401837818242419162798333)
    ·
      refine ⟨150689181840907186049375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401837818242419162798333 150689181840907186049375)
      ·
        refine ⟨226033772761360779074063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150689181840907186049375 226033772761360779074063)
        ·
          refine ⟨339050659142041168611095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226033772761360779074063 339050659142041168611095)
          ·
            refine ⟨508575988713061752916643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339050659142041168611095 508575988713061752916643)
            ·
              refine ⟨762863983069592629374965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508575988713061752916643 762863983069592629374965)
              ·
                refine ⟨71518498412774309003903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 762863983069592629374965 71518498412774309003903)
                ·
                  rfl

theorem cell19_235038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_235038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235038 prefixEnd_235038 := by exact prefixLift 235038
  have htrace : WordTrace (prefixWord ++ tailWord_235038) baseStart_235038 baseEnd_235038 := by
    simpa [prefixWord, tailWord_235038, baseEnd_235038] using wordTrace_append hprefix tailTrace_235038
  have hstable : (prefixWord ++ tailWord_235038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235038).length < 2 ^ (prefixWord ++ tailWord_235038).sum := by decide
  have hdescent : baseEnd_235038 < baseStart_235038 := by decide
  rcases family_descends (prefixWord ++ tailWord_235038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235065 : List Nat := [1, 2, 1, 5, 1, 2, 7]
def baseStart_235065 : Nat := 118140960795 + 235065 * 2 ^ 59
def prefixEnd_235065 : Nat := 4983230072969 + 3 ^ 40 * 235065 * 2
def baseEnd_235065 : Nat := 23842238034415415467943

theorem tailTrace_235065 : CollatzResearch.WordTrace tailWord_235065 prefixEnd_235065 23842238034415415467943 := by
  unfold tailWord_235065
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573524893407125750930649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5715683262271417167287099 8573524893407125750930649)
  ·
    refine ⟨6430143670055344313197987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8573524893407125750930649 6430143670055344313197987)
    ·
      refine ⟨9645215505083016469796981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6430143670055344313197987 9645215505083016469796981)
      ·
        refine ⟨904238953601532794043467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9645215505083016469796981 904238953601532794043467)
        ·
          refine ⟨1356358430402299191065201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904238953601532794043467 1356358430402299191065201)
          ·
            refine ⟨1017268822801724393298901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356358430402299191065201 1017268822801724393298901)
            ·
              refine ⟨23842238034415415467943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1017268822801724393298901 23842238034415415467943)
              ·
                rfl

theorem cell19_235065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_235065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235065 prefixEnd_235065 := by exact prefixLift 235065
  have htrace : WordTrace (prefixWord ++ tailWord_235065) baseStart_235065 baseEnd_235065 := by
    simpa [prefixWord, tailWord_235065, baseEnd_235065] using wordTrace_append hprefix tailTrace_235065
  have hstable : (prefixWord ++ tailWord_235065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235065).length < 2 ^ (prefixWord ++ tailWord_235065).sum := by decide
  have hdescent : baseEnd_235065 < baseStart_235065 := by decide
  rcases family_descends (prefixWord ++ tailWord_235065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235078 : List Nat := [6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_235078 : Nat := 118140960795 + 235078 * 2 ^ 59
def prefixEnd_235078 : Nat := 4983230072969 + 3 ^ 40 * 235078 * 2
def baseEnd_235078 : Nat := 71530669806066068114905

theorem tailTrace_235078 : CollatzResearch.WordTrace tailWord_235078 prefixEnd_235078 71530669806066068114905 := by
  unfold tailWord_235078
  simp only [CollatzResearch.WordTrace]
  refine ⟨267937470073750905348559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5715999361573352647435925 267937470073750905348559)
  ·
    refine ⟨401906205110626358022839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267937470073750905348559 401906205110626358022839)
    ·
      refine ⟨602859307665939537034259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401906205110626358022839 602859307665939537034259)
      ·
        refine ⟨904288961498909305551389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602859307665939537034259 904288961498909305551389)
        ·
          refine ⟨339108360562090989581771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904288961498909305551389 339108360562090989581771)
          ·
            refine ⟨508662540843136484372657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339108360562090989581771 508662540843136484372657)
            ·
              refine ⟨381496905632352363279493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508662540843136484372657 381496905632352363279493)
              ·
                refine ⟨71530669806066068114905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381496905632352363279493 71530669806066068114905)
                ·
                  rfl

theorem cell19_235078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_235078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235078 prefixEnd_235078 := by exact prefixLift 235078
  have htrace : WordTrace (prefixWord ++ tailWord_235078) baseStart_235078 baseEnd_235078 := by
    simpa [prefixWord, tailWord_235078, baseEnd_235078] using wordTrace_append hprefix tailTrace_235078
  have hstable : (prefixWord ++ tailWord_235078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235078).length < 2 ^ (prefixWord ++ tailWord_235078).sum := by decide
  have hdescent : baseEnd_235078 < baseStart_235078 := by decide
  rcases family_descends (prefixWord ++ tailWord_235078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235084 : List Nat := [2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_235084 : Nat := 118140960795 + 235084 * 2 ^ 59
def prefixEnd_235084 : Nat := 4983230072969 + 3 ^ 40 * 235084 * 2
def baseEnd_235084 : Nat := 71532495515059831981555

theorem tailTrace_235084 : CollatzResearch.WordTrace tailWord_235084 prefixEnd_235084 71532495515059831981555 := by
  unfold tailWord_235084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287108940169145997936153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5716145253558861330581537 4287108940169145997936153)
  ·
    refine ⟨3215331705126859498452115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4287108940169145997936153 3215331705126859498452115)
    ·
      refine ⟨4822997557690289247678173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215331705126859498452115 4822997557690289247678173)
      ·
        refine ⟨1808624084133858467879315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4822997557690289247678173 1808624084133858467879315)
        ·
          refine ⟨2712936126200787701818973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808624084133858467879315 2712936126200787701818973)
          ·
            refine ⟨1017351047325295388182115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2712936126200787701818973 1017351047325295388182115)
            ·
              refine ⟨1526026570987943082273173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017351047325295388182115 1526026570987943082273173)
              ·
                refine ⟨71532495515059831981555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1526026570987943082273173 71532495515059831981555)
                ·
                  rfl

theorem cell19_235084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_235084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235084 prefixEnd_235084 := by exact prefixLift 235084
  have htrace : WordTrace (prefixWord ++ tailWord_235084) baseStart_235084 baseEnd_235084 := by
    simpa [prefixWord, tailWord_235084, baseEnd_235084] using wordTrace_append hprefix tailTrace_235084
  have hstable : (prefixWord ++ tailWord_235084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235084).length < 2 ^ (prefixWord ++ tailWord_235084).sum := by decide
  have hdescent : baseEnd_235084 < baseStart_235084 := by decide
  rcases family_descends (prefixWord ++ tailWord_235084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235122 : List Nat := [3, 2, 1, 2, 3, 8]
def baseStart_235122 : Nat := 118140960795 + 235122 * 2 ^ 59
def prefixEnd_235122 : Nat := 4983230072969 + 3 ^ 40 * 235122 * 2
def baseEnd_235122 : Nat := 7949339815409667015223

theorem tailTrace_235122 : CollatzResearch.WordTrace tailWord_235122 prefixEnd_235122 7949339815409667015223 := by
  unfold tailWord_235122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143900963550156121438905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5717069236133749657170413 2143900963550156121438905)
  ·
    refine ⟨1607925722662617091079179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2143900963550156121438905 1607925722662617091079179)
    ·
      refine ⟨2411888583993925636618769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1607925722662617091079179 2411888583993925636618769)
      ·
        refine ⟨1808916437995444227464077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2411888583993925636618769 1808916437995444227464077)
        ·
          refine ⟨678343664248291585299029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1808916437995444227464077 678343664248291585299029)
          ·
            refine ⟨7949339815409667015223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 678343664248291585299029 7949339815409667015223)
            ·
              rfl

theorem cell19_235122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_235122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235122 prefixEnd_235122 := by exact prefixLift 235122
  have htrace : WordTrace (prefixWord ++ tailWord_235122) baseStart_235122 baseEnd_235122 := by
    simpa [prefixWord, tailWord_235122, baseEnd_235122] using wordTrace_append hprefix tailTrace_235122
  have hstable : (prefixWord ++ tailWord_235122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235122).length < 2 ^ (prefixWord ++ tailWord_235122).sum := by decide
  have hdescent : baseEnd_235122 < baseStart_235122 := by decide
  rcases family_descends (prefixWord ++ tailWord_235122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235213 : List Nat := [1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_235213 : Nat := 118140960795 + 235213 * 2 ^ 59
def prefixEnd_235213 : Nat := 4983230072969 + 3 ^ 40 * 235213 * 2
def baseEnd_235213 : Nat := 71571748258425755114537

theorem tailTrace_235213 : CollatzResearch.WordTrace tailWord_235213 prefixEnd_235213 71571748258425755114537 := by
  unfold tailWord_235213
  simp only [CollatzResearch.WordTrace]
  refine ⟨8578922896870947027318293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5719281931247298018212195 8578922896870947027318293)
  ·
    refine ⟨402137010790825641905545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8578922896870947027318293 402137010790825641905545)
    ·
      refine ⟨301602758093119231429159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402137010790825641905545 301602758093119231429159)
      ·
        refine ⟨452404137139678847143739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301602758093119231429159 452404137139678847143739)
        ·
          refine ⟨678606205709518270715609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452404137139678847143739 678606205709518270715609)
          ·
            refine ⟨508954654282138703036707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678606205709518270715609 508954654282138703036707)
            ·
              refine ⟨763431981423208054555061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508954654282138703036707 763431981423208054555061)
              ·
                refine ⟨71571748258425755114537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 763431981423208054555061 71571748258425755114537)
                ·
                  rfl

theorem cell19_235213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_235213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235213 prefixEnd_235213 := by exact prefixLift 235213
  have htrace : WordTrace (prefixWord ++ tailWord_235213) baseStart_235213 baseEnd_235213 := by
    simpa [prefixWord, tailWord_235213, baseEnd_235213] using wordTrace_append hprefix tailTrace_235213
  have hstable : (prefixWord ++ tailWord_235213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235213).length < 2 ^ (prefixWord ++ tailWord_235213).sum := by decide
  have hdescent : baseEnd_235213 < baseStart_235213 := by decide
  rcases family_descends (prefixWord ++ tailWord_235213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235217 : List Nat := [1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_235217 : Nat := 118140960795 + 235217 * 2 ^ 59
def prefixEnd_235217 : Nat := 4983230072969 + 3 ^ 40 * 235217 * 2
def baseEnd_235217 : Nat := 71572965397754931025637

theorem tailTrace_235217 : CollatzResearch.WordTrace tailWord_235217 prefixEnd_235217 71572965397754931025637 := by
  unfold tailWord_235217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8579068788856455710463905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5719379192570970473642603 8579068788856455710463905)
  ·
    refine ⟨6434301591642341782847929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8579068788856455710463905 6434301591642341782847929)
    ·
      refine ⟨4825726193731756337135947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6434301591642341782847929 4825726193731756337135947)
      ·
        refine ⟨7238589290597634505703921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4825726193731756337135947 7238589290597634505703921)
        ·
          refine ⟨5428941967948225879277941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7238589290597634505703921 5428941967948225879277941)
          ·
            refine ⟨508963309495146176182307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5428941967948225879277941 508963309495146176182307)
            ·
              refine ⟨763444964242719264273461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508963309495146176182307 763444964242719264273461)
              ·
                refine ⟨71572965397754931025637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 763444964242719264273461 71572965397754931025637)
                ·
                  rfl

theorem cell19_235217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_235217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235217 prefixEnd_235217 := by exact prefixLift 235217
  have htrace : WordTrace (prefixWord ++ tailWord_235217) baseStart_235217 baseEnd_235217 := by
    simpa [prefixWord, tailWord_235217, baseEnd_235217] using wordTrace_append hprefix tailTrace_235217
  have hstable : (prefixWord ++ tailWord_235217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235217).length < 2 ^ (prefixWord ++ tailWord_235217).sum := by decide
  have hdescent : baseEnd_235217 < baseStart_235217 := by decide
  rcases family_descends (prefixWord ++ tailWord_235217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235274 : List Nat := [3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_235274 : Nat := 118140960795 + 235274 * 2 ^ 59
def prefixEnd_235274 : Nat := 4983230072969 + 3 ^ 40 * 235274 * 2
def baseEnd_235274 : Nat := 71590309633195687758815

theorem tailTrace_235274 : CollatzResearch.WordTrace tailWord_235274 prefixEnd_235274 71590309633195687758815 := by
  unfold tailWord_235274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2145286937412488611322219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5720765166433302963525917 2145286937412488611322219)
  ·
    refine ⟨3217930406118732916983329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2145286937412488611322219 3217930406118732916983329)
    ·
      refine ⟨2413447804589049687737497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3217930406118732916983329 2413447804589049687737497)
      ·
        refine ⟨1810085853441787265803123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2413447804589049687737497 1810085853441787265803123)
        ·
          refine ⟨2715128780162680898704685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810085853441787265803123 2715128780162680898704685)
          ·
            refine ⟨1018173292561005337014257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2715128780162680898704685 1018173292561005337014257)
            ·
              refine ⟨763629969420754002760693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018173292561005337014257 763629969420754002760693)
              ·
                refine ⟨71590309633195687758815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 763629969420754002760693 71590309633195687758815)
                ·
                  rfl

theorem cell19_235274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_235274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235274 prefixEnd_235274 := by exact prefixLift 235274
  have htrace : WordTrace (prefixWord ++ tailWord_235274) baseStart_235274 baseEnd_235274 := by
    simpa [prefixWord, tailWord_235274, baseEnd_235274] using wordTrace_append hprefix tailTrace_235274
  have hstable : (prefixWord ++ tailWord_235274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235274).length < 2 ^ (prefixWord ++ tailWord_235274).sum := by decide
  have hdescent : baseEnd_235274 < baseStart_235274 := by decide
  rcases family_descends (prefixWord ++ tailWord_235274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235371 : List Nat := [1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_235371 : Nat := 118140960795 + 235371 * 2 ^ 59
def prefixEnd_235371 : Nat := 4983230072969 + 3 ^ 40 * 235371 * 2
def baseEnd_235371 : Nat := 71619825261928203602995

theorem tailTrace_235371 : CollatzResearch.WordTrace tailWord_235371 prefixEnd_235371 71619825261928203602995 := by
  unfold tailWord_235371
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584685630298540011569967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5723123753532360007713311 8584685630298540011569967)
  ·
    refine ⟨12877028445447810017354951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8584685630298540011569967 12877028445447810017354951)
    ·
      refine ⟨19315542668171715026032427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12877028445447810017354951 19315542668171715026032427)
      ·
        refine ⟨28973314002257572539048641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19315542668171715026032427 28973314002257572539048641)
        ·
          refine ⟨21729985501693179404286481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28973314002257572539048641 21729985501693179404286481)
          ·
            refine ⟨16297489126269884553214861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21729985501693179404286481 16297489126269884553214861)
            ·
              refine ⟨6111558422351206707455573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16297489126269884553214861 6111558422351206707455573)
              ·
                refine ⟨71619825261928203602995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6111558422351206707455573 71619825261928203602995)
                ·
                  rfl

theorem cell19_235371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_235371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235371 prefixEnd_235371 := by exact prefixLift 235371
  have htrace : WordTrace (prefixWord ++ tailWord_235371) baseStart_235371 baseEnd_235371 := by
    simpa [prefixWord, tailWord_235371, baseEnd_235371] using wordTrace_append hprefix tailTrace_235371
  have hstable : (prefixWord ++ tailWord_235371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235371).length < 2 ^ (prefixWord ++ tailWord_235371).sum := by decide
  have hdescent : baseEnd_235371 < baseStart_235371 := by decide
  rcases family_descends (prefixWord ++ tailWord_235371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235382 : List Nat := [5, 1, 1, 3, 2, 2, 2, 3]
def baseStart_235382 : Nat := 118140960795 + 235382 * 2 ^ 59
def prefixEnd_235382 : Nat := 4983230072969 + 3 ^ 40 * 235382 * 2
def baseEnd_235382 : Nat := 71623172395083437358521

theorem tailTrace_235382 : CollatzResearch.WordTrace tailWord_235382 prefixEnd_235382 71623172395083437358521 := by
  unfold tailWord_235382
  simp only [CollatzResearch.WordTrace]
  refine ⟨536567927078668055638775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5723391222172459260146933 536567927078668055638775)
  ·
    refine ⟨804851890618002083458163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536567927078668055638775 804851890618002083458163)
    ·
      refine ⟨1207277835927003125187245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804851890618002083458163 1207277835927003125187245)
      ·
        refine ⟨452729188472626171945217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1207277835927003125187245 452729188472626171945217)
        ·
          refine ⟨339546891354469628958913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452729188472626171945217 339546891354469628958913)
          ·
            refine ⟨254660168515852221719185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339546891354469628958913 254660168515852221719185)
            ·
              refine ⟨190995126386889166289389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254660168515852221719185 190995126386889166289389)
              ·
                refine ⟨71623172395083437358521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190995126386889166289389 71623172395083437358521)
                ·
                  rfl

theorem cell19_235382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_235382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235382 prefixEnd_235382 := by exact prefixLift 235382
  have htrace : WordTrace (prefixWord ++ tailWord_235382) baseStart_235382 baseEnd_235382 := by
    simpa [prefixWord, tailWord_235382, baseEnd_235382] using wordTrace_append hprefix tailTrace_235382
  have hstable : (prefixWord ++ tailWord_235382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235382).length < 2 ^ (prefixWord ++ tailWord_235382).sum := by decide
  have hdescent : baseEnd_235382 < baseStart_235382 := by decide
  rcases family_descends (prefixWord ++ tailWord_235382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235409 : List Nat := [1, 2, 2, 1, 1, 1, 11]
def baseStart_235409 : Nat := 118140960795 + 235409 * 2 ^ 59
def prefixEnd_235409 : Nat := 4983230072969 + 3 ^ 40 * 235409 * 2
def baseEnd_235409 : Nat := 23877129361851791586149

theorem tailTrace_235409 : CollatzResearch.WordTrace tailWord_235409 prefixEnd_235409 23877129361851791586149 := by
  unfold tailWord_235409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586071604160872501453281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5724047736107248334302187 8586071604160872501453281)
  ·
    refine ⟨6439553703120654376089961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8586071604160872501453281 6439553703120654376089961)
    ·
      refine ⟨4829665277340490782067471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6439553703120654376089961 4829665277340490782067471)
      ·
        refine ⟨7244497916010736173101207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829665277340490782067471 7244497916010736173101207)
        ·
          refine ⟨10866746874016104259651811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244497916010736173101207 10866746874016104259651811)
          ·
            refine ⟨16300120311024156389477717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866746874016104259651811 16300120311024156389477717)
            ·
              refine ⟨23877129361851791586149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16300120311024156389477717 23877129361851791586149)
              ·
                rfl

theorem cell19_235409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_235409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235409 prefixEnd_235409 := by exact prefixLift 235409
  have htrace : WordTrace (prefixWord ++ tailWord_235409) baseStart_235409 baseEnd_235409 := by
    simpa [prefixWord, tailWord_235409, baseEnd_235409] using wordTrace_append hprefix tailTrace_235409
  have hstable : (prefixWord ++ tailWord_235409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235409).length < 2 ^ (prefixWord ++ tailWord_235409).sum := by decide
  have hdescent : baseEnd_235409 < baseStart_235409 := by decide
  rcases family_descends (prefixWord ++ tailWord_235409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235445 : List Nat := [1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_235445 : Nat := 118140960795 + 235445 * 2 ^ 59
def prefixEnd_235445 : Nat := 4983230072969 + 3 ^ 40 * 235445 * 2
def baseEnd_235445 : Nat := 71642342339517957958349

theorem tailTrace_235445 : CollatzResearch.WordTrace tailWord_235445 prefixEnd_235445 71642342339517957958349 := by
  unfold tailWord_235445
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587384632030450649763789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5724923088020300433175859 8587384632030450649763789)
  ·
    refine ⟨3220269237011418993661421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8587384632030450649763789 3220269237011418993661421)
    ·
      refine ⟨1207600963879282122623033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3220269237011418993661421 1207600963879282122623033)
      ·
        refine ⟨905700722909461591967275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1207600963879282122623033 905700722909461591967275)
        ·
          refine ⟨1358551084364192387950913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905700722909461591967275 1358551084364192387950913)
          ·
            refine ⟨1018913313273144290963185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358551084364192387950913 1018913313273144290963185)
            ·
              refine ⟨764184984954858218222389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018913313273144290963185 764184984954858218222389)
              ·
                refine ⟨71642342339517957958349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 764184984954858218222389 71642342339517957958349)
                ·
                  rfl

theorem cell19_235445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_235445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235445 prefixEnd_235445 := by exact prefixLift 235445
  have htrace : WordTrace (prefixWord ++ tailWord_235445) baseStart_235445 baseEnd_235445 := by
    simpa [prefixWord, tailWord_235445, baseEnd_235445] using wordTrace_append hprefix tailTrace_235445
  have hstable : (prefixWord ++ tailWord_235445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235445).length < 2 ^ (prefixWord ++ tailWord_235445).sum := by decide
  have hdescent : baseEnd_235445 < baseStart_235445 := by decide
  rcases family_descends (prefixWord ++ tailWord_235445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235481 : List Nat := [1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_235481 : Nat := 118140960795 + 235481 * 2 ^ 59
def prefixEnd_235481 : Nat := 4983230072969 + 3 ^ 40 * 235481 * 2
def baseEnd_235481 : Nat := 71653296593480541158251

theorem tailTrace_235481 : CollatzResearch.WordTrace tailWord_235481 prefixEnd_235481 71653296593480541158251 := by
  unfold tailWord_235481
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588697659900028798074297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5725798439933352532049531 8588697659900028798074297)
  ·
    refine ⟨6441523244925021598555723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8588697659900028798074297 6441523244925021598555723)
    ·
      refine ⟨9662284867387532397833585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441523244925021598555723 9662284867387532397833585)
      ·
        refine ⟨7246713650540649298375189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9662284867387532397833585 7246713650540649298375189)
        ·
          refine ⟨339689702369092935861337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7246713650540649298375189 339689702369092935861337)
          ·
            refine ⟨254767276776819701896003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339689702369092935861337 254767276776819701896003)
            ·
              refine ⟨382150915165229552844005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254767276776819701896003 382150915165229552844005)
              ·
                refine ⟨71653296593480541158251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382150915165229552844005 71653296593480541158251)
                ·
                  rfl

theorem cell19_235481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_235481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235481 prefixEnd_235481 := by exact prefixLift 235481
  have htrace : WordTrace (prefixWord ++ tailWord_235481) baseStart_235481 baseEnd_235481 := by
    simpa [prefixWord, tailWord_235481, baseEnd_235481] using wordTrace_append hprefix tailTrace_235481
  have hstable : (prefixWord ++ tailWord_235481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235481).length < 2 ^ (prefixWord ++ tailWord_235481).sum := by decide
  have hdescent : baseEnd_235481 < baseStart_235481 := by decide
  rcases family_descends (prefixWord ++ tailWord_235481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235504 : List Nat := [2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_235504 : Nat := 118140960795 + 235504 * 2 ^ 59
def prefixEnd_235504 : Nat := 4983230072969 + 3 ^ 40 * 235504 * 2
def baseEnd_235504 : Nat := 71660295144623302647077

theorem tailTrace_235504 : CollatzResearch.WordTrace tailWord_235504 prefixEnd_235504 71660295144623302647077 := by
  unfold tailWord_235504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294768269408351863080783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5726357692544469150774377 4294768269408351863080783)
  ·
    refine ⟨6442152404112527794621175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294768269408351863080783 6442152404112527794621175)
    ·
      refine ⟨9663228606168791691931763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442152404112527794621175 9663228606168791691931763)
      ·
        refine ⟨14494842909253187537897645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9663228606168791691931763 14494842909253187537897645)
        ·
          refine ⟨5435566090969945326711617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14494842909253187537897645 5435566090969945326711617)
          ·
            refine ⟨4076674568227458995033713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435566090969945326711617 4076674568227458995033713)
            ·
              refine ⟨3057505926170594246275285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076674568227458995033713 3057505926170594246275285)
              ·
                refine ⟨71660295144623302647077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3057505926170594246275285 71660295144623302647077)
                ·
                  rfl

theorem cell19_235504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_235504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235504 prefixEnd_235504 := by exact prefixLift 235504
  have htrace : WordTrace (prefixWord ++ tailWord_235504) baseStart_235504 baseEnd_235504 := by
    simpa [prefixWord, tailWord_235504, baseEnd_235504] using wordTrace_append hprefix tailTrace_235504
  have hstable : (prefixWord ++ tailWord_235504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235504).length < 2 ^ (prefixWord ++ tailWord_235504).sum := by decide
  have hdescent : baseEnd_235504 < baseStart_235504 := by decide
  rcases family_descends (prefixWord ++ tailWord_235504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235557 : List Nat := [1, 3, 1, 2, 2, 5, 2, 3]
def baseStart_235557 : Nat := 118140960795 + 235557 * 2 ^ 59
def prefixEnd_235557 : Nat := 4983230072969 + 3 ^ 40 * 235557 * 2
def baseEnd_235557 : Nat := 71676422240734883469155

theorem tailTrace_235557 : CollatzResearch.WordTrace tailWord_235557 prefixEnd_235557 71676422240734883469155 := by
  unfold tailWord_235557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591469607624693777840925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5727646405083129185227283 8591469607624693777840925)
  ·
    refine ⟨3221801102859260166690347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8591469607624693777840925 3221801102859260166690347)
    ·
      refine ⟨4832701654288890250035521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3221801102859260166690347 4832701654288890250035521)
      ·
        refine ⟨3624526240716667687526641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4832701654288890250035521 3624526240716667687526641)
        ·
          refine ⟨2718394680537500765644981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624526240716667687526641 2718394680537500765644981)
          ·
            refine ⟨254849501300390696779217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2718394680537500765644981 254849501300390696779217)
            ·
              refine ⟨191137125975293022584413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254849501300390696779217 191137125975293022584413)
              ·
                refine ⟨71676422240734883469155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191137125975293022584413 71676422240734883469155)
                ·
                  rfl

theorem cell19_235557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_235557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235557 prefixEnd_235557 := by exact prefixLift 235557
  have htrace : WordTrace (prefixWord ++ tailWord_235557) baseStart_235557 baseEnd_235557 := by
    simpa [prefixWord, tailWord_235557, baseEnd_235557] using wordTrace_append hprefix tailTrace_235557
  have hstable : (prefixWord ++ tailWord_235557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235557).length < 2 ^ (prefixWord ++ tailWord_235557).sum := by decide
  have hdescent : baseEnd_235557 < baseStart_235557 := by decide
  rcases family_descends (prefixWord ++ tailWord_235557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235576 : List Nat := [2, 1, 2, 1, 7, 1, 5]
def baseStart_235576 : Nat := 118140960795 + 235576 * 2 ^ 59
def prefixEnd_235576 : Nat := 4983230072969 + 3 ^ 40 * 235576 * 2
def baseEnd_235576 : Nat := 23894067884182823015627

theorem tailTrace_235576 : CollatzResearch.WordTrace tailWord_235576 prefixEnd_235576 23894067884182823015627 := by
  unfold tailWord_235576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296081297277930011391291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5728108396370573348521721 4296081297277930011391291)
  ·
    refine ⟨6444121945916895017086937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296081297277930011391291 6444121945916895017086937)
    ·
      refine ⟨4833091459437671262815203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6444121945916895017086937 4833091459437671262815203)
      ·
        refine ⟨7249637189156506894222805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833091459437671262815203 7249637189156506894222805)
        ·
          refine ⟨169913371620855630333347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7249637189156506894222805 169913371620855630333347)
          ·
            refine ⟨254870057431283445500021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169913371620855630333347 254870057431283445500021)
            ·
              refine ⟨23894067884182823015627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254870057431283445500021 23894067884182823015627)
              ·
                rfl

theorem cell19_235576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_235576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235576 prefixEnd_235576 := by exact prefixLift 235576
  have htrace : WordTrace (prefixWord ++ tailWord_235576) baseStart_235576 baseEnd_235576 := by
    simpa [prefixWord, tailWord_235576, baseEnd_235576] using wordTrace_append hprefix tailTrace_235576
  have hstable : (prefixWord ++ tailWord_235576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235576).length < 2 ^ (prefixWord ++ tailWord_235576).sum := by decide
  have hdescent : baseEnd_235576 < baseStart_235576 := by decide
  rcases family_descends (prefixWord ++ tailWord_235576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235637 : List Nat := [1, 3, 4, 11]
def baseStart_235637 : Nat := 118140960795 + 235637 * 2 ^ 59
def prefixEnd_235637 : Nat := 4983230072969 + 3 ^ 40 * 235637 * 2
def baseEnd_235637 : Nat := 885194629966893848039

theorem tailTrace_235637 : CollatzResearch.WordTrace tailWord_235637 prefixEnd_235637 885194629966893848039 := by
  unfold tailWord_235637
  simp only [CollatzResearch.WordTrace]
  refine ⟨8594387447334867440753165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5729591631556578293835443 8594387447334867440753165)
  ·
    refine ⟨3222895292750575290282437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8594387447334867440753165 3222895292750575290282437)
    ·
      refine ⟨604292867390732866927957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3222895292750575290282437 604292867390732866927957)
      ·
        refine ⟨885194629966893848039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 604292867390732866927957 885194629966893848039)
        ·
          rfl

theorem cell19_235637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 11].length) (baseStart_235637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235637 prefixEnd_235637 := by exact prefixLift 235637
  have htrace : WordTrace (prefixWord ++ tailWord_235637) baseStart_235637 baseEnd_235637 := by
    simpa [prefixWord, tailWord_235637, baseEnd_235637] using wordTrace_append hprefix tailTrace_235637
  have hstable : (prefixWord ++ tailWord_235637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235637).length < 2 ^ (prefixWord ++ tailWord_235637).sum := by decide
  have hdescent : baseEnd_235637 < baseStart_235637 := by decide
  rcases family_descends (prefixWord ++ tailWord_235637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235671 : List Nat := [1, 1, 3, 3, 4, 1, 3, 3]
def baseStart_235671 : Nat := 118140960795 + 235671 * 2 ^ 59
def prefixEnd_235671 : Nat := 4983230072969 + 3 ^ 40 * 235671 * 2
def baseEnd_235671 : Nat := 71711110711616396935511

theorem tailTrace_235671 : CollatzResearch.WordTrace tailWord_235671 prefixEnd_235671 71711110711616396935511 := by
  unfold tailWord_235671
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595627529211691247490867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5730418352807794164993911 8595627529211691247490867)
  ·
    refine ⟨12893441293817536871236301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8595627529211691247490867 12893441293817536871236301)
    ·
      refine ⟨4835040485181576326713613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12893441293817536871236301 4835040485181576326713613)
      ·
        refine ⟨1813140181943091122517605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4835040485181576326713613 1813140181943091122517605)
        ·
          refine ⟨339963784114329585472051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1813140181943091122517605 339963784114329585472051)
          ·
            refine ⟨509945676171494378208077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339963784114329585472051 509945676171494378208077)
            ·
              refine ⟨191229628564310391828029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509945676171494378208077 191229628564310391828029)
              ·
                refine ⟨71711110711616396935511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191229628564310391828029 71711110711616396935511)
                ·
                  rfl

theorem cell19_235671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_235671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235671 prefixEnd_235671 := by exact prefixLift 235671
  have htrace : WordTrace (prefixWord ++ tailWord_235671) baseStart_235671 baseEnd_235671 := by
    simpa [prefixWord, tailWord_235671, baseEnd_235671] using wordTrace_append hprefix tailTrace_235671
  have hstable : (prefixWord ++ tailWord_235671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235671).length < 2 ^ (prefixWord ++ tailWord_235671).sum := by decide
  have hdescent : baseEnd_235671 < baseStart_235671 := by decide
  rcases family_descends (prefixWord ++ tailWord_235671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235690 : List Nat := [3, 1, 5, 1, 2, 1, 6]
def baseStart_235690 : Nat := 118140960795 + 235690 * 2 ^ 59
def prefixEnd_235690 : Nat := 4983230072969 + 3 ^ 40 * 235690 * 2
def baseEnd_235690 : Nat := 23905630707809994171079

theorem tailTrace_235690 : CollatzResearch.WordTrace tailWord_235690 prefixEnd_235690 23905630707809994171079 := by
  unfold tailWord_235690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149080129035714373108131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5730880344095238328288349 2149080129035714373108131)
  ·
    refine ⟨3223620193553571559662197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149080129035714373108131 3223620193553571559662197)
    ·
      refine ⟨302214393145647333718331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3223620193553571559662197 302214393145647333718331)
      ·
        refine ⟨453321589718471000577497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302214393145647333718331 453321589718471000577497)
        ·
          refine ⟨339991192288853250433123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453321589718471000577497 339991192288853250433123)
          ·
            refine ⟨509986788433279875649685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339991192288853250433123 509986788433279875649685)
            ·
              refine ⟨23905630707809994171079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 509986788433279875649685 23905630707809994171079)
              ·
                rfl

theorem cell19_235690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_235690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235690 prefixEnd_235690 := by exact prefixLift 235690
  have htrace : WordTrace (prefixWord ++ tailWord_235690) baseStart_235690 baseEnd_235690 := by
    simpa [prefixWord, tailWord_235690, baseEnd_235690] using wordTrace_append hprefix tailTrace_235690
  have hstable : (prefixWord ++ tailWord_235690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235690).length < 2 ^ (prefixWord ++ tailWord_235690).sum := by decide
  have hdescent : baseEnd_235690 < baseStart_235690 := by decide
  rcases family_descends (prefixWord ++ tailWord_235690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235724 : List Nat := [2, 2, 1, 6, 2, 1, 2, 3]
def baseStart_235724 : Nat := 118140960795 + 235724 * 2 ^ 59
def prefixEnd_235724 : Nat := 4983230072969 + 3 ^ 40 * 235724 * 2
def baseEnd_235724 : Nat := 71727237807727977757589

theorem tailTrace_235724 : CollatzResearch.WordTrace tailWord_235724 prefixEnd_235724 71727237807727977757589 := by
  unfold tailWord_235724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298780299009840649585113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5731707065346454199446817 4298780299009840649585113)
  ·
    refine ⟨3224085224257380487188835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4298780299009840649585113 3224085224257380487188835)
    ·
      refine ⟨4836127836386070730783253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224085224257380487188835 4836127836386070730783253)
      ·
        refine ⟨226693492330597065505465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4836127836386070730783253 226693492330597065505465)
        ·
          refine ⟨170020119247947799129099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226693492330597065505465 170020119247947799129099)
          ·
            refine ⟨255030178871921698693649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170020119247947799129099 255030178871921698693649)
            ·
              refine ⟨191272634153941274020237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255030178871921698693649 191272634153941274020237)
              ·
                refine ⟨71727237807727977757589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191272634153941274020237 71727237807727977757589)
                ·
                  rfl

theorem cell19_235724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_235724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235724 prefixEnd_235724 := by exact prefixLift 235724
  have htrace : WordTrace (prefixWord ++ tailWord_235724) baseStart_235724 baseEnd_235724 := by
    simpa [prefixWord, tailWord_235724, baseEnd_235724] using wordTrace_append hprefix tailTrace_235724
  have hstable : (prefixWord ++ tailWord_235724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235724).length < 2 ^ (prefixWord ++ tailWord_235724).sum := by decide
  have hdescent : baseEnd_235724 < baseStart_235724 := by decide
  rcases family_descends (prefixWord ++ tailWord_235724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235730 : List Nat := [3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_235730 : Nat := 118140960795 + 235730 * 2 ^ 59
def prefixEnd_235730 : Nat := 4983230072969 + 3 ^ 40 * 235730 * 2
def baseEnd_235730 : Nat := 71729063516721741624239

theorem tailTrace_235730 : CollatzResearch.WordTrace tailWord_235730 prefixEnd_235730 71729063516721741624239 := by
  unfold tailWord_235730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149444858999486080972161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5731852957331962882592429 2149444858999486080972161)
  ·
    refine ⟨1612083644249614560729121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2149444858999486080972161 1612083644249614560729121)
    ·
      refine ⟨1209062733187210920546841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612083644249614560729121 1209062733187210920546841)
      ·
        refine ⟨906797049890408190410131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1209062733187210920546841 906797049890408190410131)
        ·
          refine ⟨1360195574835612285615197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906797049890408190410131 1360195574835612285615197)
          ·
            refine ⟨510073340563354607105699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1360195574835612285615197 510073340563354607105699)
            ·
              refine ⟨765110010845031910658549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510073340563354607105699 765110010845031910658549)
              ·
                refine ⟨71729063516721741624239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 765110010845031910658549 71729063516721741624239)
                ·
                  rfl

theorem cell19_235730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_235730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235730 prefixEnd_235730 := by exact prefixLift 235730
  have htrace : WordTrace (prefixWord ++ tailWord_235730) baseStart_235730 baseEnd_235730 := by
    simpa [prefixWord, tailWord_235730, baseEnd_235730] using wordTrace_append hprefix tailTrace_235730
  have hstable : (prefixWord ++ tailWord_235730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235730).length < 2 ^ (prefixWord ++ tailWord_235730).sum := by decide
  have hdescent : baseEnd_235730 < baseStart_235730 := by decide
  rcases family_descends (prefixWord ++ tailWord_235730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235747 : List Nat := [1, 1, 1, 8, 1, 2, 5]
def baseStart_235747 : Nat := 118140960795 + 235747 * 2 ^ 59
def prefixEnd_235747 : Nat := 4983230072969 + 3 ^ 40 * 235747 * 2
def baseEnd_235747 : Nat := 23911412119623579748805

theorem tailTrace_235747 : CollatzResearch.WordTrace tailWord_235747 prefixEnd_235747 23911412119623579748805 := by
  unfold tailWord_235747
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598399476936356227257495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5732266317957570818171663 8598399476936356227257495)
  ·
    refine ⟨12897599215404534340886243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8598399476936356227257495 12897599215404534340886243)
    ·
      refine ⟨19346398823106801511329365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12897599215404534340886243 19346398823106801511329365)
      ·
        refine ⟨226715611208282830210891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 19346398823106801511329365 226715611208282830210891)
        ·
          refine ⟨340073416812424245316337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226715611208282830210891 340073416812424245316337)
          ·
            refine ⟨255055062609318183987253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340073416812424245316337 255055062609318183987253)
            ·
              refine ⟨23911412119623579748805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255055062609318183987253 23911412119623579748805)
              ·
                rfl

theorem cell19_235747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_235747 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235747 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235747 prefixEnd_235747 := by exact prefixLift 235747
  have htrace : WordTrace (prefixWord ++ tailWord_235747) baseStart_235747 baseEnd_235747 := by
    simpa [prefixWord, tailWord_235747, baseEnd_235747] using wordTrace_append hprefix tailTrace_235747
  have hstable : (prefixWord ++ tailWord_235747).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235747).length < 2 ^ (prefixWord ++ tailWord_235747).sum := by decide
  have hdescent : baseEnd_235747 < baseStart_235747 := by decide
  rcases family_descends (prefixWord ++ tailWord_235747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235749 : List Nat := [1, 3, 1, 4, 2, 3, 5]
def baseStart_235749 : Nat := 118140960795 + 235749 * 2 ^ 59
def prefixEnd_235749 : Nat := 4983230072969 + 3 ^ 40 * 235749 * 2
def baseEnd_235749 : Nat := 23911614976178442400655

theorem tailTrace_235749 : CollatzResearch.WordTrace tailWord_235749 prefixEnd_235749 23911614976178442400655 := by
  unfold tailWord_235749
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598472422929110568830301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5732314948619407045886867 8598472422929110568830301)
  ·
    refine ⟨3224427158598416463311363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8598472422929110568830301 3224427158598416463311363)
    ·
      refine ⟨4836640737897624694967045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224427158598416463311363 4836640737897624694967045)
      ·
        refine ⟨906870138355804630306321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4836640737897624694967045 906870138355804630306321)
        ·
          refine ⟨680152603766853472729741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906870138355804630306321 680152603766853472729741)
          ·
            refine ⟨255057226412570052273653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 680152603766853472729741 255057226412570052273653)
            ·
              refine ⟨23911614976178442400655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255057226412570052273653 23911614976178442400655)
              ·
                rfl

theorem cell19_235749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_235749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235749 prefixEnd_235749 := by exact prefixLift 235749
  have htrace : WordTrace (prefixWord ++ tailWord_235749) baseStart_235749 baseEnd_235749 := by
    simpa [prefixWord, tailWord_235749, baseEnd_235749] using wordTrace_append hprefix tailTrace_235749
  have hstable : (prefixWord ++ tailWord_235749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235749).length < 2 ^ (prefixWord ++ tailWord_235749).sum := by decide
  have hdescent : baseEnd_235749 < baseStart_235749 := by decide
  rcases family_descends (prefixWord ++ tailWord_235749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235770 : List Nat := [3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_235770 : Nat := 118140960795 + 235770 * 2 ^ 59
def prefixEnd_235770 : Nat := 4983230072969 + 3 ^ 40 * 235770 * 2
def baseEnd_235770 : Nat := 71741234910013500735241

theorem tailTrace_235770 : CollatzResearch.WordTrace tailWord_235770 prefixEnd_235770 71741234910013500735241 := by
  unfold tailWord_235770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149809588963257788836191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5732825570568687436896509 2149809588963257788836191)
  ·
    refine ⟨3224714383444886683254287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149809588963257788836191 3224714383444886683254287)
    ·
      refine ⟨4837071575167330024881431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224714383444886683254287 4837071575167330024881431)
      ·
        refine ⟨7255607362750995037322147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837071575167330024881431 7255607362750995037322147)
        ·
          refine ⟨10883411044126492555983221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7255607362750995037322147 10883411044126492555983221)
          ·
            refine ⟨1020319785386858677123427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10883411044126492555983221 1020319785386858677123427)
            ·
              refine ⟨1530479678080288015685141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020319785386858677123427 1530479678080288015685141)
              ·
                refine ⟨71741234910013500735241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1530479678080288015685141 71741234910013500735241)
                ·
                  rfl

theorem cell19_235770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_235770 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235770 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235770 prefixEnd_235770 := by exact prefixLift 235770
  have htrace : WordTrace (prefixWord ++ tailWord_235770) baseStart_235770 baseEnd_235770 := by
    simpa [prefixWord, tailWord_235770, baseEnd_235770] using wordTrace_append hprefix tailTrace_235770
  have hstable : (prefixWord ++ tailWord_235770).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235770).length < 2 ^ (prefixWord ++ tailWord_235770).sum := by decide
  have hdescent : baseEnd_235770 < baseStart_235770 := by decide
  rcases family_descends (prefixWord ++ tailWord_235770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235808 : List Nat := [2, 1, 1, 5, 2, 8]
def baseStart_235808 : Nat := 118140960795 + 235808 * 2 ^ 59
def prefixEnd_235808 : Nat := 4983230072969 + 3 ^ 40 * 235808 * 2
def baseEnd_235808 : Nat := 7972533081515630210077

theorem tailTrace_235808 : CollatzResearch.WordTrace tailWord_235808 prefixEnd_235808 7972533081515630210077 := by
  unfold tailWord_235808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300312164857681822614039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5733749553143575763485385 4300312164857681822614039)
  ·
    refine ⟨6450468247286522733921059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4300312164857681822614039 6450468247286522733921059)
    ·
      refine ⟨9675702370929784100881589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450468247286522733921059 9675702370929784100881589)
      ·
        refine ⟨907097097274667259457649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9675702370929784100881589 907097097274667259457649)
        ·
          refine ⟨680322822956000444593237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907097097274667259457649 680322822956000444593237)
          ·
            refine ⟨7972533081515630210077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 680322822956000444593237 7972533081515630210077)
            ·
              rfl

theorem cell19_235808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_235808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235808 prefixEnd_235808 := by exact prefixLift 235808
  have htrace : WordTrace (prefixWord ++ tailWord_235808) baseStart_235808 baseEnd_235808 := by
    simpa [prefixWord, tailWord_235808, baseEnd_235808] using wordTrace_append hprefix tailTrace_235808
  have hstable : (prefixWord ++ tailWord_235808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235808).length < 2 ^ (prefixWord ++ tailWord_235808).sum := by decide
  have hdescent : baseEnd_235808 < baseStart_235808 := by decide
  rcases family_descends (prefixWord ++ tailWord_235808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235821 : List Nat := [1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_235821 : Nat := 118140960795 + 235821 * 2 ^ 59
def prefixEnd_235821 : Nat := 4983230072969 + 3 ^ 40 * 235821 * 2
def baseEnd_235821 : Nat := 71756753436460493601769

theorem tailTrace_235821 : CollatzResearch.WordTrace tailWord_235821 prefixEnd_235821 71756753436460493601769 := by
  unfold tailWord_235821
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601098478668266865451317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5734065652445511243634211 8601098478668266865451317)
  ·
    refine ⟨806352982375150018636061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8601098478668266865451317 806352982375150018636061)
    ·
      refine ⟨302382368390681256988523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 806352982375150018636061 302382368390681256988523)
      ·
        refine ⟨453573552586021885482785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302382368390681256988523 453573552586021885482785)
        ·
          refine ⟨340180164439516414112089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453573552586021885482785 340180164439516414112089)
          ·
            refine ⟨255135123329637310584067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340180164439516414112089 255135123329637310584067)
            ·
              refine ⟨382702684994455965876101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255135123329637310584067 382702684994455965876101)
              ·
                refine ⟨71756753436460493601769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382702684994455965876101 71756753436460493601769)
                ·
                  rfl

theorem cell19_235821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_235821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235821 prefixEnd_235821 := by exact prefixLift 235821
  have htrace : WordTrace (prefixWord ++ tailWord_235821) baseStart_235821 baseEnd_235821 := by
    simpa [prefixWord, tailWord_235821, baseEnd_235821] using wordTrace_append hprefix tailTrace_235821
  have hstable : (prefixWord ++ tailWord_235821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235821).length < 2 ^ (prefixWord ++ tailWord_235821).sum := by decide
  have hdescent : baseEnd_235821 < baseStart_235821 := by decide
  rcases family_descends (prefixWord ++ tailWord_235821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235901 : List Nat := [1, 4, 1, 1, 2, 3, 4, 3]
def baseStart_235901 : Nat := 118140960795 + 235901 * 2 ^ 59
def prefixEnd_235901 : Nat := 4983230072969 + 3 ^ 40 * 235901 * 2
def baseEnd_235901 : Nat := 71781096223044011823773

theorem tailTrace_235901 : CollatzResearch.WordTrace tailWord_235901 prefixEnd_235901 71781096223044011823773 := by
  unfold tailWord_235901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8604016318378440528363557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5736010878918960352242371 8604016318378440528363557)
  ·
    refine ⟨1613253059695957599068167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8604016318378440528363557 1613253059695957599068167)
    ·
      refine ⟨2419879589543936398602251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613253059695957599068167 2419879589543936398602251)
      ·
        refine ⟨3629819384315904597903377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419879589543936398602251 3629819384315904597903377)
        ·
          refine ⟨2722364538236928448427533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3629819384315904597903377 2722364538236928448427533)
          ·
            refine ⟨1020886701838848168160325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2722364538236928448427533 1020886701838848168160325)
            ·
              refine ⟨191416256594784031530061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1020886701838848168160325 191416256594784031530061)
              ·
                refine ⟨71781096223044011823773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191416256594784031530061 71781096223044011823773)
                ·
                  rfl

theorem cell19_235901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_235901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235901 prefixEnd_235901 := by exact prefixLift 235901
  have htrace : WordTrace (prefixWord ++ tailWord_235901) baseStart_235901 baseEnd_235901 := by
    simpa [prefixWord, tailWord_235901, baseEnd_235901] using wordTrace_append hprefix tailTrace_235901
  have hstable : (prefixWord ++ tailWord_235901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235901).length < 2 ^ (prefixWord ++ tailWord_235901).sum := by decide
  have hdescent : baseEnd_235901 < baseStart_235901 := by decide
  rcases family_descends (prefixWord ++ tailWord_235901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235937 : List Nat := [1, 2, 3, 5, 1, 1, 2, 4]
def baseStart_235937 : Nat := 118140960795 + 235937 * 2 ^ 59
def prefixEnd_235937 : Nat := 4983230072969 + 3 ^ 40 * 235937 * 2
def baseEnd_235937 : Nat := 71792050477006595023675

theorem tailTrace_235937 : CollatzResearch.WordTrace tailWord_235937 prefixEnd_235937 71792050477006595023675 := by
  unfold tailWord_235937
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605329346248018676674065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5736886230832012451116043 8605329346248018676674065)
  ·
    refine ⟨6453997009686014007505549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8605329346248018676674065 6453997009686014007505549)
    ·
      refine ⟨2420248878632255252814581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6453997009686014007505549 2420248878632255252814581)
      ·
        refine ⟨226898332371773929951367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2420248878632255252814581 226898332371773929951367)
        ·
          refine ⟨340347498557660894927051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226898332371773929951367 340347498557660894927051)
          ·
            refine ⟨510521247836491342390577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340347498557660894927051 510521247836491342390577)
            ·
              refine ⟨382890935877368506792933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510521247836491342390577 382890935877368506792933)
              ·
                refine ⟨71792050477006595023675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382890935877368506792933 71792050477006595023675)
                ·
                  rfl

theorem cell19_235937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_235937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235937 prefixEnd_235937 := by exact prefixLift 235937
  have htrace : WordTrace (prefixWord ++ tailWord_235937) baseStart_235937 baseEnd_235937 := by
    simpa [prefixWord, tailWord_235937, baseEnd_235937] using wordTrace_append hprefix tailTrace_235937
  have hstable : (prefixWord ++ tailWord_235937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235937).length < 2 ^ (prefixWord ++ tailWord_235937).sum := by decide
  have hdescent : baseEnd_235937 < baseStart_235937 := by decide
  rcases family_descends (prefixWord ++ tailWord_235937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235941 : List Nat := [1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_235941 : Nat := 118140960795 + 235941 * 2 ^ 59
def prefixEnd_235941 : Nat := 4983230072969 + 3 ^ 40 * 235941 * 2
def baseEnd_235941 : Nat := 71793267616335770934775

theorem tailTrace_235941 : CollatzResearch.WordTrace tailWord_235941 prefixEnd_235941 71793267616335770934775 := by
  unfold tailWord_235941
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605475238233527359819677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5736983492155684906546451 8605475238233527359819677)
  ·
    refine ⟨3227053214337572759932379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8605475238233527359819677 3227053214337572759932379)
    ·
      refine ⟨4840579821506359139898569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227053214337572759932379 4840579821506359139898569)
      ·
        refine ⟨3630434866129769354923927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4840579821506359139898569 3630434866129769354923927)
        ·
          refine ⟨5445652299194654032385891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630434866129769354923927 5445652299194654032385891)
          ·
            refine ⟨8168478448791981048578837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5445652299194654032385891 8168478448791981048578837)
            ·
              refine ⟨382897427287124111652133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8168478448791981048578837 382897427287124111652133)
              ·
                refine ⟨71793267616335770934775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382897427287124111652133 71793267616335770934775)
                ·
                  rfl

theorem cell19_235941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_235941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_235941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_235941 prefixEnd_235941 := by exact prefixLift 235941
  have htrace : WordTrace (prefixWord ++ tailWord_235941) baseStart_235941 baseEnd_235941 := by
    simpa [prefixWord, tailWord_235941, baseEnd_235941] using wordTrace_append hprefix tailTrace_235941
  have hstable : (prefixWord ++ tailWord_235941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235941).length < 2 ^ (prefixWord ++ tailWord_235941).sum := by decide
  have hdescent : baseEnd_235941 < baseStart_235941 := by decide
  rcases family_descends (prefixWord ++ tailWord_235941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236013 : List Nat := [1, 5, 1, 3, 1, 2, 3, 3]
def baseStart_236013 : Nat := 118140960795 + 236013 * 2 ^ 59
def prefixEnd_236013 : Nat := 4983230072969 + 3 ^ 40 * 236013 * 2
def baseEnd_236013 : Nat := 71815176124260937334579

theorem tailTrace_236013 : CollatzResearch.WordTrace tailWord_236013 prefixEnd_236013 71815176124260937334579 := by
  unfold tailWord_236013
  simp only [CollatzResearch.WordTrace]
  refine ⟨8608101293972683656440693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5738734195981789104293795 8608101293972683656440693)
  ·
    refine ⟨807009496309939092791315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8608101293972683656440693 807009496309939092791315)
    ·
      refine ⟨1210514244464908639186973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807009496309939092791315 1210514244464908639186973)
      ·
        refine ⟨453942841674340739695115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1210514244464908639186973 453942841674340739695115)
        ·
          refine ⟨680914262511511109542673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453942841674340739695115 680914262511511109542673)
          ·
            refine ⟨510685696883633332157005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680914262511511109542673 510685696883633332157005)
            ·
              refine ⟨191507136331362499558877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510685696883633332157005 191507136331362499558877)
              ·
                refine ⟨71815176124260937334579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191507136331362499558877 71815176124260937334579)
                ·
                  rfl

theorem cell19_236013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_236013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236013 prefixEnd_236013 := by exact prefixLift 236013
  have htrace : WordTrace (prefixWord ++ tailWord_236013) baseStart_236013 baseEnd_236013 := by
    simpa [prefixWord, tailWord_236013, baseEnd_236013] using wordTrace_append hprefix tailTrace_236013
  have hstable : (prefixWord ++ tailWord_236013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236013).length < 2 ^ (prefixWord ++ tailWord_236013).sum := by decide
  have hdescent : baseEnd_236013 < baseStart_236013 := by decide
  rcases family_descends (prefixWord ++ tailWord_236013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236068 : List Nat := [2, 3, 1, 5, 1, 2, 2, 3]
def baseStart_236068 : Nat := 118140960795 + 236068 * 2 ^ 59
def prefixEnd_236068 : Nat := 4983230072969 + 3 ^ 40 * 236068 * 2
def baseEnd_236068 : Nat := 71831911790037106112207

theorem tailTrace_236068 : CollatzResearch.WordTrace tailWord_236068 prefixEnd_236068 71831911790037106112207 := by
  unfold tailWord_236068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4305053654386714024846429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5740071539182285366461905 4305053654386714024846429)
  ·
    refine ⟨1614395120395017759317411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4305053654386714024846429 1614395120395017759317411)
    ·
      refine ⟨2421592680592526638976117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614395120395017759317411 2421592680592526638976117)
      ·
        refine ⟨227024313805549372404011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2421592680592526638976117 227024313805549372404011)
        ·
          refine ⟨340536470708324058606017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227024313805549372404011 340536470708324058606017)
          ·
            refine ⟨255402353031243043954513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340536470708324058606017 255402353031243043954513)
            ·
              refine ⟨191551764773432282965885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255402353031243043954513 191551764773432282965885)
              ·
                refine ⟨71831911790037106112207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191551764773432282965885 71831911790037106112207)
                ·
                  rfl

theorem cell19_236068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_236068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236068 prefixEnd_236068 := by exact prefixLift 236068
  have htrace : WordTrace (prefixWord ++ tailWord_236068) baseStart_236068 baseEnd_236068 := by
    simpa [prefixWord, tailWord_236068, baseEnd_236068] using wordTrace_append hprefix tailTrace_236068
  have hstable : (prefixWord ++ tailWord_236068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236068).length < 2 ^ (prefixWord ++ tailWord_236068).sum := by decide
  have hdescent : baseEnd_236068 < baseStart_236068 := by decide
  rcases family_descends (prefixWord ++ tailWord_236068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236072 : List Nat := [2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_236072 : Nat := 118140960795 + 236072 * 2 ^ 59
def prefixEnd_236072 : Nat := 4983230072969 + 3 ^ 40 * 236072 * 2
def baseEnd_236072 : Nat := 71833128929366282023307

theorem tailTrace_236072 : CollatzResearch.WordTrace tailWord_236072 prefixEnd_236072 71833128929366282023307 := by
  unfold tailWord_236072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4305126600379468366419235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5740168800505957821892313 4305126600379468366419235)
  ·
    refine ⟨6457689900569202549628853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4305126600379468366419235 6457689900569202549628853)
    ·
      refine ⟨605408428178362739027705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6457689900569202549628853 605408428178362739027705)
      ·
        refine ⟨454056321133772054270779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605408428178362739027705 454056321133772054270779)
        ·
          refine ⟨681084481700658081406169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454056321133772054270779 681084481700658081406169)
          ·
            refine ⟨510813361275493561054627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681084481700658081406169 510813361275493561054627)
            ·
              refine ⟨766220041913240341581941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510813361275493561054627 766220041913240341581941)
              ·
                refine ⟨71833128929366282023307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 766220041913240341581941 71833128929366282023307)
                ·
                  rfl

theorem cell19_236072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_236072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236072 prefixEnd_236072 := by exact prefixLift 236072
  have htrace : WordTrace (prefixWord ++ tailWord_236072) baseStart_236072 baseEnd_236072 := by
    simpa [prefixWord, tailWord_236072, baseEnd_236072] using wordTrace_append hprefix tailTrace_236072
  have hstable : (prefixWord ++ tailWord_236072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236072).length < 2 ^ (prefixWord ++ tailWord_236072).sum := by decide
  have hdescent : baseEnd_236072 < baseStart_236072 := by decide
  rcases family_descends (prefixWord ++ tailWord_236072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236093 : List Nat := [1, 4, 1, 3, 2, 1, 7]
def baseStart_236093 : Nat := 118140960795 + 236093 * 2 ^ 59
def prefixEnd_236093 : Nat := 4983230072969 + 3 ^ 40 * 236093 * 2
def baseEnd_236093 : Nat := 23946506303614818518861

theorem tailTrace_236093 : CollatzResearch.WordTrace tailWord_236093 prefixEnd_236093 23946506303614818518861 := by
  unfold tailWord_236093
  simp only [CollatzResearch.WordTrace]
  refine ⟨8611019133682857319352933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5740679422455238212901955 8611019133682857319352933)
  ·
    refine ⟨1614566087565535747378675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8611019133682857319352933 1614566087565535747378675)
    ·
      refine ⟨2421849131348303621068013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614566087565535747378675 2421849131348303621068013)
      ·
        refine ⟨908193424255613857900505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2421849131348303621068013 908193424255613857900505)
        ·
          refine ⟨681145068191710393425379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908193424255613857900505 681145068191710393425379)
          ·
            refine ⟨1021717602287565590138069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681145068191710393425379 1021717602287565590138069)
            ·
              refine ⟨23946506303614818518861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1021717602287565590138069 23946506303614818518861)
              ·
                rfl

theorem cell19_236093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_236093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236093 prefixEnd_236093 := by exact prefixLift 236093
  have htrace : WordTrace (prefixWord ++ tailWord_236093) baseStart_236093 baseEnd_236093 := by
    simpa [prefixWord, tailWord_236093, baseEnd_236093] using wordTrace_append hprefix tailTrace_236093
  have hstable : (prefixWord ++ tailWord_236093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236093).length < 2 ^ (prefixWord ++ tailWord_236093).sum := by decide
  have hdescent : baseEnd_236093 < baseStart_236093 := by decide
  rcases family_descends (prefixWord ++ tailWord_236093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236150 : List Nat := [5, 1, 1, 2, 10]
def baseStart_236150 : Nat := 118140960795 + 236150 * 2 ^ 59
def prefixEnd_236150 : Nat := 4983230072969 + 3 ^ 40 * 236150 * 2
def baseEnd_236150 : Nat := 2661365301714267121843

theorem tailTrace_236150 : CollatzResearch.WordTrace tailWord_236150 prefixEnd_236150 2661365301714267121843 := by
  unfold tailWord_236150
  simp only [CollatzResearch.WordTrace]
  refine ⟨538318630904772253386119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5742065396317570702785269 538318630904772253386119)
  ·
    refine ⟨807477946357158380079179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538318630904772253386119 807477946357158380079179)
    ·
      refine ⟨1211216919535737570118769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807477946357158380079179 1211216919535737570118769)
      ·
        refine ⟨908412689651803177589077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211216919535737570118769 908412689651803177589077)
        ·
          refine ⟨2661365301714267121843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 908412689651803177589077 2661365301714267121843)
          ·
            rfl

theorem cell19_236150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 10].length) (baseStart_236150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236150 prefixEnd_236150 := by exact prefixLift 236150
  have htrace : WordTrace (prefixWord ++ tailWord_236150) baseStart_236150 baseEnd_236150 := by
    simpa [prefixWord, tailWord_236150, baseEnd_236150] using wordTrace_append hprefix tailTrace_236150
  have hstable : (prefixWord ++ tailWord_236150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236150).length < 2 ^ (prefixWord ++ tailWord_236150).sum := by decide
  have hdescent : baseEnd_236150 < baseStart_236150 := by decide
  rcases family_descends (prefixWord ++ tailWord_236150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236171 : List Nat := [1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_236171 : Nat := 118140960795 + 236171 * 2 ^ 59
def prefixEnd_236171 : Nat := 4983230072969 + 3 ^ 40 * 236171 * 2
def baseEnd_236171 : Nat := 71863253127763385823037

theorem tailTrace_236171 : CollatzResearch.WordTrace tailWord_236171 prefixEnd_236171 71863253127763385823037 := by
  unfold tailWord_236171
  simp only [CollatzResearch.WordTrace]
  refine ⟨8613864027400276640692367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5742576018266851093794911 8613864027400276640692367)
  ·
    refine ⟨12920796041100414961038551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8613864027400276640692367 12920796041100414961038551)
    ·
      refine ⟨19381194061650622441557827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12920796041100414961038551 19381194061650622441557827)
      ·
        refine ⟨29071791092475933662336741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19381194061650622441557827 29071791092475933662336741)
        ·
          refine ⟨5450960829839237561688139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29071791092475933662336741 5450960829839237561688139)
          ·
            refine ⟨8176441244758856342532209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450960829839237561688139 8176441244758856342532209)
            ·
              refine ⟨6132330933569142256899157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8176441244758856342532209 6132330933569142256899157)
              ·
                refine ⟨71863253127763385823037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6132330933569142256899157 71863253127763385823037)
                ·
                  rfl

theorem cell19_236171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_236171 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236171 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236171 prefixEnd_236171 := by exact prefixLift 236171
  have htrace : WordTrace (prefixWord ++ tailWord_236171) baseStart_236171 baseEnd_236171 := by
    simpa [prefixWord, tailWord_236171, baseEnd_236171] using wordTrace_append hprefix tailTrace_236171
  have hstable : (prefixWord ++ tailWord_236171).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236171).length < 2 ^ (prefixWord ++ tailWord_236171).sum := by decide
  have hdescent : baseEnd_236171 < baseStart_236171 := by decide
  rcases family_descends (prefixWord ++ tailWord_236171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236237 : List Nat := [1, 6, 2, 1, 3, 1, 2, 3]
def baseStart_236237 : Nat := 118140960795 + 236237 * 2 ^ 59
def prefixEnd_236237 : Nat := 4983230072969 + 3 ^ 40 * 236237 * 2
def baseEnd_236237 : Nat := 71883335926694788356191

theorem tailTrace_236237 : CollatzResearch.WordTrace tailWord_236237 prefixEnd_236237 71883335926694788356191 := by
  unfold tailWord_236237
  simp only [CollatzResearch.WordTrace]
  refine ⟨8616271245161169912594965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5744180830107446608396643 8616271245161169912594965)
  ·
    refine ⟨403887714616929839652889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8616271245161169912594965 403887714616929839652889)
    ·
      refine ⟨302915785962697379739667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403887714616929839652889 302915785962697379739667)
      ·
        refine ⟨454373678944046069609501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302915785962697379739667 454373678944046069609501)
        ·
          refine ⟨170390129604017276103563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454373678944046069609501 170390129604017276103563)
          ·
            refine ⟨255585194406025914155345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170390129604017276103563 255585194406025914155345)
            ·
              refine ⟨191688895804519435616509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255585194406025914155345 191688895804519435616509)
              ·
                refine ⟨71883335926694788356191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191688895804519435616509 71883335926694788356191)
                ·
                  rfl

theorem cell19_236237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_236237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236237 prefixEnd_236237 := by exact prefixLift 236237
  have htrace : WordTrace (prefixWord ++ tailWord_236237) baseStart_236237 baseEnd_236237 := by
    simpa [prefixWord, tailWord_236237, baseEnd_236237] using wordTrace_append hprefix tailTrace_236237
  have hstable : (prefixWord ++ tailWord_236237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236237).length < 2 ^ (prefixWord ++ tailWord_236237).sum := by decide
  have hdescent : baseEnd_236237 < baseStart_236237 := by decide
  rcases family_descends (prefixWord ++ tailWord_236237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236277 : List Nat := [1, 3, 6, 1, 1, 1, 2, 4]
def baseStart_236277 : Nat := 118140960795 + 236277 * 2 ^ 59
def prefixEnd_236277 : Nat := 4983230072969 + 3 ^ 40 * 236277 * 2
def baseEnd_236277 : Nat := 71895507319986547467193

theorem tailTrace_236277 : CollatzResearch.WordTrace tailWord_236277 prefixEnd_236277 71895507319986547467193 := by
  unfold tailWord_236277
  simp only [CollatzResearch.WordTrace]
  refine ⟨8617730165016256744051085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5745153443344171162700723 8617730165016256744051085)
  ·
    refine ⟨3231648811881096279019157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8617730165016256744051085 3231648811881096279019157)
    ·
      refine ⟨151483538056926388079023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3231648811881096279019157 151483538056926388079023)
      ·
        refine ⟨227225307085389582118535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151483538056926388079023 227225307085389582118535)
        ·
          refine ⟨340837960628084373177803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227225307085389582118535 340837960628084373177803)
          ·
            refine ⟨511256940942126559766705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340837960628084373177803 511256940942126559766705)
            ·
              refine ⟨383442705706594919825029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511256940942126559766705 383442705706594919825029)
              ·
                refine ⟨71895507319986547467193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383442705706594919825029 71895507319986547467193)
                ·
                  rfl

theorem cell19_236277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_236277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236277 prefixEnd_236277 := by exact prefixLift 236277
  have htrace : WordTrace (prefixWord ++ tailWord_236277) baseStart_236277 baseEnd_236277 := by
    simpa [prefixWord, tailWord_236277, baseEnd_236277] using wordTrace_append hprefix tailTrace_236277
  have hstable : (prefixWord ++ tailWord_236277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236277).length < 2 ^ (prefixWord ++ tailWord_236277).sum := by decide
  have hdescent : baseEnd_236277 < baseStart_236277 := by decide
  rcases family_descends (prefixWord ++ tailWord_236277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236437 : List Nat := [1, 3, 2, 1, 1, 4, 7]
def baseStart_236437 : Nat := 118140960795 + 236437 * 2 ^ 59
def prefixEnd_236437 : Nat := 4983230072969 + 3 ^ 40 * 236437 * 2
def baseEnd_236437 : Nat := 23981397631051194637067

theorem tailTrace_236437 : CollatzResearch.WordTrace tailWord_236437 prefixEnd_236437 23981397631051194637067 := by
  unfold tailWord_236437
  simp only [CollatzResearch.WordTrace]
  refine ⟨8623565844436604069875565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5749043896291069379917043 8623565844436604069875565)
  ·
    refine ⟨3233837191663726526203337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8623565844436604069875565 3233837191663726526203337)
    ·
      refine ⟨2425377893747794894652503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233837191663726526203337 2425377893747794894652503)
      ·
        refine ⟨3638066840621692341978755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425377893747794894652503 3638066840621692341978755)
        ·
          refine ⟨5457100260932538512968133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638066840621692341978755 5457100260932538512968133)
          ·
            refine ⟨1023206298924850971181525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5457100260932538512968133 1023206298924850971181525)
            ·
              refine ⟨23981397631051194637067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1023206298924850971181525 23981397631051194637067)
              ·
                rfl

theorem cell19_236437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_236437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236437 prefixEnd_236437 := by exact prefixLift 236437
  have htrace : WordTrace (prefixWord ++ tailWord_236437) baseStart_236437 baseEnd_236437 := by
    simpa [prefixWord, tailWord_236437, baseEnd_236437] using wordTrace_append hprefix tailTrace_236437
  have hstable : (prefixWord ++ tailWord_236437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236437).length < 2 ^ (prefixWord ++ tailWord_236437).sum := by decide
  have hdescent : baseEnd_236437 < baseStart_236437 := by decide
  rcases family_descends (prefixWord ++ tailWord_236437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236486 : List Nat := [6, 1, 3, 1, 1, 7]
def baseStart_236486 : Nat := 118140960795 + 236486 * 2 ^ 59
def prefixEnd_236486 : Nat := 4983230072969 + 3 ^ 40 * 236486 * 2
def baseEnd_236486 : Nat := 7995455872215109869131

theorem tailTrace_236486 : CollatzResearch.WordTrace tailWord_236486 prefixEnd_236486 7995455872215109869131 := by
  unfold tailWord_236486
  simp only [CollatzResearch.WordTrace]
  refine ⟨269542281914346419950291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5750235347506056958939541 269542281914346419950291)
  ·
    refine ⟨404313422871519629925437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269542281914346419950291 404313422871519629925437)
    ·
      refine ⟨151617533576819861222039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404313422871519629925437 151617533576819861222039)
      ·
        refine ⟨227426300365229791833059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151617533576819861222039 227426300365229791833059)
        ·
          refine ⟨341139450547844687749589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227426300365229791833059 341139450547844687749589)
          ·
            refine ⟨7995455872215109869131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 341139450547844687749589 7995455872215109869131)
            ·
              rfl

theorem cell19_236486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 7].length) (baseStart_236486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236486 prefixEnd_236486 := by exact prefixLift 236486
  have htrace : WordTrace (prefixWord ++ tailWord_236486) baseStart_236486 baseEnd_236486 := by
    simpa [prefixWord, tailWord_236486, baseEnd_236486] using wordTrace_append hprefix tailTrace_236486
  have hstable : (prefixWord ++ tailWord_236486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236486).length < 2 ^ (prefixWord ++ tailWord_236486).sum := by decide
  have hdescent : baseEnd_236486 < baseStart_236486 := by decide
  rcases family_descends (prefixWord ++ tailWord_236486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236494 : List Nat := [4, 1, 1, 1, 2, 10]
def baseStart_236494 : Nat := 118140960795 + 236494 * 2 ^ 59
def prefixEnd_236494 : Nat := 4983230072969 + 3 ^ 40 * 236494 * 2
def baseEnd_236494 : Nat := 7995726347621593404931

theorem tailTrace_236494 : CollatzResearch.WordTrace tailWord_236494 prefixEnd_236494 7995726347621593404931 := by
  unfold tailWord_236494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078205600653762850587567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5750429870153401869800357 1078205600653762850587567)
  ·
    refine ⟨1617308400980644275881351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1078205600653762850587567 1617308400980644275881351)
    ·
      refine ⟨2425962601470966413822027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1617308400980644275881351 2425962601470966413822027)
      ·
        refine ⟨3638943902206449620733041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425962601470966413822027 3638943902206449620733041)
        ·
          refine ⟨2729207926654837215549781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638943902206449620733041 2729207926654837215549781)
          ·
            refine ⟨7995726347621593404931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2729207926654837215549781 7995726347621593404931)
            ·
              rfl

theorem cell19_236494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_236494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236494 prefixEnd_236494 := by exact prefixLift 236494
  have htrace : WordTrace (prefixWord ++ tailWord_236494) baseStart_236494 baseEnd_236494 := by
    simpa [prefixWord, tailWord_236494, baseEnd_236494] using wordTrace_append hprefix tailTrace_236494
  have hstable : (prefixWord ++ tailWord_236494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236494).length < 2 ^ (prefixWord ++ tailWord_236494).sum := by decide
  have hdescent : baseEnd_236494 < baseStart_236494 := by decide
  rcases family_descends (prefixWord ++ tailWord_236494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236509 : List Nat := [1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_236509 : Nat := 118140960795 + 236509 * 2 ^ 59
def prefixEnd_236509 : Nat := 4983230072969 + 3 ^ 40 * 236509 * 2
def baseEnd_236509 : Nat := 71966101401078750311005

theorem tailTrace_236509 : CollatzResearch.WordTrace tailWord_236509 prefixEnd_236509 71966101401078750311005 := by
  unfold tailWord_236509
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626191900175760366496581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5750794600117173577664387 8626191900175760366496581)
  ·
    refine ⟨1617410981282955068718109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8626191900175760366496581 1617410981282955068718109)
    ·
      refine ⟨606529117981108150769291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1617410981282955068718109 606529117981108150769291)
      ·
        refine ⟨909793676971662226153937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606529117981108150769291 909793676971662226153937)
        ·
          refine ⟨682345257728746669615453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909793676971662226153937 682345257728746669615453)
          ·
            refine ⟨255879471648280001105795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682345257728746669615453 255879471648280001105795)
            ·
              refine ⟨383819207472420001658693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255879471648280001105795 383819207472420001658693)
              ·
                refine ⟨71966101401078750311005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383819207472420001658693 71966101401078750311005)
                ·
                  rfl

theorem cell19_236509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_236509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236509 prefixEnd_236509 := by exact prefixLift 236509
  have htrace : WordTrace (prefixWord ++ tailWord_236509) baseStart_236509 baseEnd_236509 := by
    simpa [prefixWord, tailWord_236509, baseEnd_236509] using wordTrace_append hprefix tailTrace_236509
  have hstable : (prefixWord ++ tailWord_236509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236509).length < 2 ^ (prefixWord ++ tailWord_236509).sum := by decide
  have hdescent : baseEnd_236509 < baseStart_236509 := by decide
  rcases family_descends (prefixWord ++ tailWord_236509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236551 : List Nat := [1, 1, 4, 3, 1, 1, 8]
def baseStart_236551 : Nat := 118140960795 + 236551 * 2 ^ 59
def prefixEnd_236551 : Nat := 4983230072969 + 3 ^ 40 * 236551 * 2
def baseEnd_236551 : Nat := 23992960454678365792519

theorem tailTrace_236551 : CollatzResearch.WordTrace tailWord_236551 prefixEnd_236551 23992960454678365792519 := by
  unfold tailWord_236551
  simp only [CollatzResearch.WordTrace]
  refine ⟨8627723766023601539525507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5751815844015734359683671 8627723766023601539525507)
  ·
    refine ⟨12941585649035402309288261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8627723766023601539525507 12941585649035402309288261)
    ·
      refine ⟨2426547309194137932991549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12941585649035402309288261 2426547309194137932991549)
      ·
        refine ⟨909955240947801724871831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2426547309194137932991549 909955240947801724871831)
        ·
          refine ⟨1364932861421702587307747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909955240947801724871831 1364932861421702587307747)
          ·
            refine ⟨2047399292132553880961621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364932861421702587307747 2047399292132553880961621)
            ·
              refine ⟨23992960454678365792519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2047399292132553880961621 23992960454678365792519)
              ·
                rfl

theorem cell19_236551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_236551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236551 prefixEnd_236551 := by exact prefixLift 236551
  have htrace : WordTrace (prefixWord ++ tailWord_236551) baseStart_236551 baseEnd_236551 := by
    simpa [prefixWord, tailWord_236551, baseEnd_236551] using wordTrace_append hprefix tailTrace_236551
  have hstable : (prefixWord ++ tailWord_236551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236551).length < 2 ^ (prefixWord ++ tailWord_236551).sum := by decide
  have hdescent : baseEnd_236551 < baseStart_236551 := by decide
  rcases family_descends (prefixWord ++ tailWord_236551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236570 : List Nat := [3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_236570 : Nat := 118140960795 + 236570 * 2 ^ 59
def prefixEnd_236570 : Nat := 4983230072969 + 3 ^ 40 * 236570 * 2
def baseEnd_236570 : Nat := 71984662775848682955283

theorem tailTrace_236570 : CollatzResearch.WordTrace tailWord_236570 prefixEnd_236570 71984662775848682955283 := by
  unfold tailWord_236570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157104188238691946116791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5752277835303178522978109 2157104188238691946116791)
  ·
    refine ⟨3235656282358037919175187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157104188238691946116791 3235656282358037919175187)
    ·
      refine ⟨4853484423537056878762781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235656282358037919175187 4853484423537056878762781)
      ·
        refine ⟨1820056658826396329536043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4853484423537056878762781 1820056658826396329536043)
        ·
          refine ⟨2730084988239594494304065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820056658826396329536043 2730084988239594494304065)
          ·
            refine ⟨2047563741179695870728049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730084988239594494304065 2047563741179695870728049)
            ·
              refine ⟨1535672805884771903046037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047563741179695870728049 1535672805884771903046037)
              ·
                refine ⟨71984662775848682955283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1535672805884771903046037 71984662775848682955283)
                ·
                  rfl

theorem cell19_236570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_236570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236570 prefixEnd_236570 := by exact prefixLift 236570
  have htrace : WordTrace (prefixWord ++ tailWord_236570) baseStart_236570 baseEnd_236570 := by
    simpa [prefixWord, tailWord_236570, baseEnd_236570] using wordTrace_append hprefix tailTrace_236570
  have hstable : (prefixWord ++ tailWord_236570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236570).length < 2 ^ (prefixWord ++ tailWord_236570).sum := by decide
  have hdescent : baseEnd_236570 < baseStart_236570 := by decide
  rcases family_descends (prefixWord ++ tailWord_236570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236583 : List Nat := [1, 1, 7, 1, 1, 3, 2, 3]
def baseStart_236583 : Nat := 118140960795 + 236583 * 2 ^ 59
def prefixEnd_236583 : Nat := 4983230072969 + 3 ^ 40 * 236583 * 2
def baseEnd_236583 : Nat := 71988618478668504666359

theorem tailTrace_236583 : CollatzResearch.WordTrace tailWord_236583 prefixEnd_236583 71988618478668504666359 := by
  unfold tailWord_236583
  simp only [CollatzResearch.WordTrace]
  refine ⟨8628890901907671004690403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5752593934605114003126935 8628890901907671004690403)
  ·
    refine ⟨12943336352861506507035605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8628890901907671004690403 12943336352861506507035605)
    ·
      refine ⟨303359445770191558758647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12943336352861506507035605 303359445770191558758647)
      ·
        refine ⟨455039168655287338137971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303359445770191558758647 455039168655287338137971)
        ·
          refine ⟨682558752982931007206957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455039168655287338137971 682558752982931007206957)
          ·
            refine ⟨255959532368599127702609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682558752982931007206957 255959532368599127702609)
            ·
              refine ⟨191969649276449345776957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255959532368599127702609 191969649276449345776957)
              ·
                refine ⟨71988618478668504666359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191969649276449345776957 71988618478668504666359)
                ·
                  rfl

theorem cell19_236583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_236583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236583 prefixEnd_236583 := by exact prefixLift 236583
  have htrace : WordTrace (prefixWord ++ tailWord_236583) baseStart_236583 baseEnd_236583 := by
    simpa [prefixWord, tailWord_236583, baseEnd_236583] using wordTrace_append hprefix tailTrace_236583
  have hstable : (prefixWord ++ tailWord_236583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236583).length < 2 ^ (prefixWord ++ tailWord_236583).sum := by decide
  have hdescent : baseEnd_236583 < baseStart_236583 := by decide
  rcases family_descends (prefixWord ++ tailWord_236583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236606 : List Nat := [4, 2, 1, 3, 1, 1, 7]
def baseStart_236606 : Nat := 118140960795 + 236606 * 2 ^ 59
def prefixEnd_236606 : Nat := 4983230072969 + 3 ^ 40 * 236606 * 2
def baseEnd_236606 : Nat := 23998539009937088718395

theorem tailTrace_236606 : CollatzResearch.WordTrace tailWord_236606 prefixEnd_236606 23998539009937088718395 := by
  unfold tailWord_236606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078716222603043241597209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5753153187216230621851781 1078716222603043241597209)
  ·
    refine ⟨809037166952282431197907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1078716222603043241597209 809037166952282431197907)
    ·
      refine ⟨1213555750428423646796861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809037166952282431197907 1213555750428423646796861)
      ·
        refine ⟨455083406410658867548823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1213555750428423646796861 455083406410658867548823)
        ·
          refine ⟨682625109615988301323235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455083406410658867548823 682625109615988301323235)
          ·
            refine ⟨1023937664423982451984853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682625109615988301323235 1023937664423982451984853)
            ·
              refine ⟨23998539009937088718395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1023937664423982451984853 23998539009937088718395)
              ·
                rfl

theorem cell19_236606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_236606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236606 prefixEnd_236606 := by exact prefixLift 236606
  have htrace : WordTrace (prefixWord ++ tailWord_236606) baseStart_236606 baseEnd_236606 := by
    simpa [prefixWord, tailWord_236606, baseEnd_236606] using wordTrace_append hprefix tailTrace_236606
  have hstable : (prefixWord ++ tailWord_236606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236606).length < 2 ^ (prefixWord ++ tailWord_236606).sum := by decide
  have hdescent : baseEnd_236606 < baseStart_236606 := by decide
  rcases family_descends (prefixWord ++ tailWord_236606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236661 : List Nat := [1, 3, 4, 3, 2, 6]
def baseStart_236661 : Nat := 118140960795 + 236661 * 2 ^ 59
def prefixEnd_236661 : Nat := 4983230072969 + 3 ^ 40 * 236661 * 2
def baseEnd_236661 : Nat := 8001372521731937214757

theorem tailTrace_236661 : CollatzResearch.WordTrace tailWord_236661 prefixEnd_236661 8001372521731937214757 := by
  unfold tailWord_236661
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631735795625090326029837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5754490530416726884019891 8631735795625090326029837)
  ·
    refine ⟨3236900923359408872261189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8631735795625090326029837 3236900923359408872261189)
    ·
      refine ⟨606918923129889163548973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3236900923359408872261189 606918923129889163548973)
      ·
        refine ⟨227594596173708436330865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606918923129889163548973 227594596173708436330865)
        ·
          refine ⟨170695947130281327248149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227594596173708436330865 170695947130281327248149)
          ·
            refine ⟨8001372521731937214757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170695947130281327248149 8001372521731937214757)
            ·
              rfl

theorem cell19_236661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 6].length) (baseStart_236661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236661 prefixEnd_236661 := by exact prefixLift 236661
  have htrace : WordTrace (prefixWord ++ tailWord_236661) baseStart_236661 baseEnd_236661 := by
    simpa [prefixWord, tailWord_236661, baseEnd_236661] using wordTrace_append hprefix tailTrace_236661
  have hstable : (prefixWord ++ tailWord_236661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236661).length < 2 ^ (prefixWord ++ tailWord_236661).sum := by decide
  have hdescent : baseEnd_236661 < baseStart_236661 := by decide
  rcases family_descends (prefixWord ++ tailWord_236661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236665 : List Nat := [1, 2, 1, 3, 5, 7]
def baseStart_236665 : Nat := 118140960795 + 236665 * 2 ^ 59
def prefixEnd_236665 : Nat := 4983230072969 + 3 ^ 40 * 236665 * 2
def baseEnd_236665 : Nat := 8001507759435178982657

theorem tailTrace_236665 : CollatzResearch.WordTrace tailWord_236665 prefixEnd_236665 8001507759435178982657 := by
  unfold tailWord_236665
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631881687610599009175449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5754587791740399339450299 8631881687610599009175449)
  ·
    refine ⟨6473911265707949256881587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8631881687610599009175449 6473911265707949256881587)
    ·
      refine ⟨9710866898561923885322381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473911265707949256881587 9710866898561923885322381)
      ·
        refine ⟨3641575086960721456995893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9710866898561923885322381 3641575086960721456995893)
        ·
          refine ⟨341397664402567636593365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3641575086960721456995893 341397664402567636593365)
          ·
            refine ⟨8001507759435178982657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 341397664402567636593365 8001507759435178982657)
            ·
              rfl

theorem cell19_236665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_236665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236665 prefixEnd_236665 := by exact prefixLift 236665
  have htrace : WordTrace (prefixWord ++ tailWord_236665) baseStart_236665 baseEnd_236665 := by
    simpa [prefixWord, tailWord_236665, baseEnd_236665] using wordTrace_append hprefix tailTrace_236665
  have hstable : (prefixWord ++ tailWord_236665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236665).length < 2 ^ (prefixWord ++ tailWord_236665).sum := by decide
  have hdescent : baseEnd_236665 < baseStart_236665 := by decide
  rcases family_descends (prefixWord ++ tailWord_236665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236680 : List Nat := [2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_236680 : Nat := 118140960795 + 236680 * 2 ^ 59
def prefixEnd_236680 : Nat := 4983230072969 + 3 ^ 40 * 236680 * 2
def baseEnd_236680 : Nat := 72018134107401020510539

theorem tailTrace_236680 : CollatzResearch.WordTrace tailWord_236680 prefixEnd_236680 72018134107401020510539 := by
  unfold tailWord_236680
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316214391278128285485747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5754952521704171047314329 4316214391278128285485747)
  ·
    refine ⟨6474321586917192428228621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4316214391278128285485747 6474321586917192428228621)
    ·
      refine ⟨2427870595093947160585733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6474321586917192428228621 2427870595093947160585733)
      ·
        refine ⟨455225736580115092609825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2427870595093947160585733 455225736580115092609825)
        ·
          refine ⟨341419302435086319457369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455225736580115092609825 341419302435086319457369)
          ·
            refine ⟨256064476826314739593027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341419302435086319457369 256064476826314739593027)
            ·
              refine ⟨384096715239472109389541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256064476826314739593027 384096715239472109389541)
              ·
                refine ⟨72018134107401020510539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384096715239472109389541 72018134107401020510539)
                ·
                  rfl

theorem cell19_236680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_236680 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236680 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236680 prefixEnd_236680 := by exact prefixLift 236680
  have htrace : WordTrace (prefixWord ++ tailWord_236680) baseStart_236680 baseEnd_236680 := by
    simpa [prefixWord, tailWord_236680, baseEnd_236680] using wordTrace_append hprefix tailTrace_236680
  have hstable : (prefixWord ++ tailWord_236680).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236680).length < 2 ^ (prefixWord ++ tailWord_236680).sum := by decide
  have hdescent : baseEnd_236680 < baseStart_236680 := by decide
  rcases family_descends (prefixWord ++ tailWord_236680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236701 : List Nat := [1, 4, 2, 1, 1, 2, 5, 3]
def baseStart_236701 : Nat := 118140960795 + 236701 * 2 ^ 59
def prefixEnd_236701 : Nat := 4983230072969 + 3 ^ 40 * 236701 * 2
def baseEnd_236701 : Nat := 72024524088879194043815

theorem tailTrace_236701 : CollatzResearch.WordTrace tailWord_236701 prefixEnd_236701 72024524088879194043815 := by
  unfold tailWord_236701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8633194715480177157485957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5755463143653451438323971 8633194715480177157485957)
  ·
    refine ⟨1618724009152533217028617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8633194715480177157485957 1618724009152533217028617)
    ·
      refine ⟨1214043006864399912771463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1618724009152533217028617 1214043006864399912771463)
      ·
        refine ⟨1821064510296599869157195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214043006864399912771463 1821064510296599869157195)
        ·
          refine ⟨2731596765444899803735793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821064510296599869157195 2731596765444899803735793)
          ·
            refine ⟨2048697574083674852801845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731596765444899803735793 2048697574083674852801845)
            ·
              refine ⟨192065397570344517450173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2048697574083674852801845 192065397570344517450173)
              ·
                refine ⟨72024524088879194043815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192065397570344517450173 72024524088879194043815)
                ·
                  rfl

theorem cell19_236701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_236701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236701 prefixEnd_236701 := by exact prefixLift 236701
  have htrace : WordTrace (prefixWord ++ tailWord_236701) baseStart_236701 baseEnd_236701 := by
    simpa [prefixWord, tailWord_236701, baseEnd_236701] using wordTrace_append hprefix tailTrace_236701
  have hstable : (prefixWord ++ tailWord_236701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236701).length < 2 ^ (prefixWord ++ tailWord_236701).sum := by decide
  have hdescent : baseEnd_236701 < baseStart_236701 := by decide
  rcases family_descends (prefixWord ++ tailWord_236701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236722 : List Nat := [3, 2, 1, 1, 1, 5, 6]
def baseStart_236722 : Nat := 118140960795 + 236722 * 2 ^ 59
def prefixEnd_236722 : Nat := 4983230072969 + 3 ^ 40 * 236722 * 2
def baseEnd_236722 : Nat := 24010304690119122525697

theorem tailTrace_236722 : CollatzResearch.WordTrace tailWord_236722 prefixEnd_236722 24010304690119122525697 := by
  unfold tailWord_236722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158490162101024436000105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5755973765602731829333613 2158490162101024436000105)
  ·
    refine ⟨1618867621575768327000079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2158490162101024436000105 1618867621575768327000079)
    ·
      refine ⟨2428301432363652490500119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618867621575768327000079 2428301432363652490500119)
      ·
        refine ⟨3642452148545478735750179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428301432363652490500119 3642452148545478735750179)
        ·
          refine ⟨5463678222818218103625269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642452148545478735750179 5463678222818218103625269)
          ·
            refine ⟨512219833389207947214869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5463678222818218103625269 512219833389207947214869)
            ·
              refine ⟨24010304690119122525697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 512219833389207947214869 24010304690119122525697)
              ·
                rfl

theorem cell19_236722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_236722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236722 prefixEnd_236722 := by exact prefixLift 236722
  have htrace : WordTrace (prefixWord ++ tailWord_236722) baseStart_236722 baseEnd_236722 := by
    simpa [prefixWord, tailWord_236722, baseEnd_236722] using wordTrace_append hprefix tailTrace_236722
  have hstable : (prefixWord ++ tailWord_236722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236722).length < 2 ^ (prefixWord ++ tailWord_236722).sum := by decide
  have hdescent : baseEnd_236722 < baseStart_236722 := by decide
  rcases family_descends (prefixWord ++ tailWord_236722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236756 : List Nat := [2, 4, 1, 4, 1, 1, 1, 5]
def baseStart_236756 : Nat := 118140960795 + 236756 * 2 ^ 59
def prefixEnd_236756 : Nat := 4983230072969 + 3 ^ 40 * 236756 * 2
def baseEnd_236756 : Nat := 72041259754655362821443

theorem tailTrace_236756 : CollatzResearch.WordTrace tailWord_236756 prefixEnd_236756 72041259754655362821443 := by
  unfold tailWord_236756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317600365140460775369061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5756800486853947700492081 4317600365140460775369061)
  ·
    refine ⟨809550068463836395381699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4317600365140460775369061 809550068463836395381699)
    ·
      refine ⟨1214325102695754593072549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809550068463836395381699 1214325102695754593072549)
      ·
        refine ⟨227685956755453986201103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1214325102695754593072549 227685956755453986201103)
        ·
          refine ⟨341528935133180979301655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227685956755453986201103 341528935133180979301655)
          ·
            refine ⟨512293402699771468952483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341528935133180979301655 512293402699771468952483)
            ·
              refine ⟨768440104049657203428725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512293402699771468952483 768440104049657203428725)
              ·
                refine ⟨72041259754655362821443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 768440104049657203428725 72041259754655362821443)
                ·
                  rfl

theorem cell19_236756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_236756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236756 prefixEnd_236756 := by exact prefixLift 236756
  have htrace : WordTrace (prefixWord ++ tailWord_236756) baseStart_236756 baseEnd_236756 := by
    simpa [prefixWord, tailWord_236756, baseEnd_236756] using wordTrace_append hprefix tailTrace_236756
  have hstable : (prefixWord ++ tailWord_236756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236756).length < 2 ^ (prefixWord ++ tailWord_236756).sum := by decide
  have hdescent : baseEnd_236756 < baseStart_236756 := by decide
  rcases family_descends (prefixWord ++ tailWord_236756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236775 : List Nat := [1, 1, 5, 3, 3, 1, 5]
def baseStart_236775 : Nat := 118140960795 + 236775 * 2 ^ 59
def prefixEnd_236775 : Nat := 4983230072969 + 3 ^ 40 * 236775 * 2
def baseEnd_236775 : Nat := 24015680388822982799723

theorem tailTrace_236775 : CollatzResearch.WordTrace tailWord_236775 prefixEnd_236775 24015680388822982799723 := by
  unfold tailWord_236775
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635893717212087795679779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5757262478141391863786519 8635893717212087795679779)
  ·
    refine ⟨12953840575818131693519669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8635893717212087795679779 12953840575818131693519669)
    ·
      refine ⟨1214422553982949846267469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12953840575818131693519669 1214422553982949846267469)
      ·
        refine ⟨455408457743606192350301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1214422553982949846267469 455408457743606192350301)
        ·
          refine ⟨170778171653852322131363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455408457743606192350301 170778171653852322131363)
          ·
            refine ⟨256167257480778483197045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170778171653852322131363 256167257480778483197045)
            ·
              refine ⟨24015680388822982799723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256167257480778483197045 24015680388822982799723)
              ·
                rfl

theorem cell19_236775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_236775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236775 prefixEnd_236775 := by exact prefixLift 236775
  have htrace : WordTrace (prefixWord ++ tailWord_236775) baseStart_236775 baseEnd_236775 := by
    simpa [prefixWord, tailWord_236775, baseEnd_236775] using wordTrace_append hprefix tailTrace_236775
  have hstable : (prefixWord ++ tailWord_236775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236775).length < 2 ^ (prefixWord ++ tailWord_236775).sum := by decide
  have hdescent : baseEnd_236775 < baseStart_236775 := by decide
  rcases family_descends (prefixWord ++ tailWord_236775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236779 : List Nat := [1, 1, 1, 1, 2, 8, 5]
def baseStart_236779 : Nat := 118140960795 + 236779 * 2 ^ 59
def prefixEnd_236779 : Nat := 4983230072969 + 3 ^ 40 * 236779 * 2
def baseEnd_236779 : Nat := 24016086101932708103423

theorem tailTrace_236779 : CollatzResearch.WordTrace tailWord_236779 prefixEnd_236779 24016086101932708103423 := by
  unfold tailWord_236779
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636039609197596478825391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5757359739465064319216927 8636039609197596478825391)
  ·
    refine ⟨12954059413796394718238087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8636039609197596478825391 12954059413796394718238087)
    ·
      refine ⟨19431089120694592077357131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12954059413796394718238087 19431089120694592077357131)
      ·
        refine ⟨29146633681041888116035697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19431089120694592077357131 29146633681041888116035697)
        ·
          refine ⟨21859975260781416087026773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29146633681041888116035697 21859975260781416087026773)
          ·
            refine ⟨256171585087282219769845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 21859975260781416087026773 256171585087282219769845)
            ·
              refine ⟨24016086101932708103423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256171585087282219769845 24016086101932708103423)
              ·
                rfl

theorem cell19_236779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_236779 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236779 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236779 prefixEnd_236779 := by exact prefixLift 236779
  have htrace : WordTrace (prefixWord ++ tailWord_236779) baseStart_236779 baseEnd_236779 := by
    simpa [prefixWord, tailWord_236779, baseEnd_236779] using wordTrace_append hprefix tailTrace_236779
  have hstable : (prefixWord ++ tailWord_236779).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236779).length < 2 ^ (prefixWord ++ tailWord_236779).sum := by decide
  have hdescent : baseEnd_236779 < baseStart_236779 := by decide
  rcases family_descends (prefixWord ++ tailWord_236779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236796 : List Nat := [2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_236796 : Nat := 118140960795 + 236796 * 2 ^ 59
def prefixEnd_236796 : Nat := 4983230072969 + 3 ^ 40 * 236796 * 2
def baseEnd_236796 : Nat := 72053431147947121932445

theorem tailTrace_236796 : CollatzResearch.WordTrace tailWord_236796 prefixEnd_236796 72053431147947121932445 := by
  unfold tailWord_236796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318329825068004191097121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5757773100090672254796161 4318329825068004191097121)
  ·
    refine ⟨3238747368801003143322841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4318329825068004191097121 3238747368801003143322841)
    ·
      refine ⟨2429060526600752357492131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3238747368801003143322841 2429060526600752357492131)
      ·
        refine ⟨3643590789901128536238197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429060526600752357492131 3643590789901128536238197)
        ·
          refine ⟨341586636553230800272331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3643590789901128536238197 341586636553230800272331)
          ·
            refine ⟨512379954829846200408497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341586636553230800272331 512379954829846200408497)
            ·
              refine ⟨384284966122384650306373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512379954829846200408497 384284966122384650306373)
              ·
                refine ⟨72053431147947121932445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384284966122384650306373 72053431147947121932445)
                ·
                  rfl

theorem cell19_236796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_236796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236796 prefixEnd_236796 := by exact prefixLift 236796
  have htrace : WordTrace (prefixWord ++ tailWord_236796) baseStart_236796 baseEnd_236796 := by
    simpa [prefixWord, tailWord_236796, baseEnd_236796] using wordTrace_append hprefix tailTrace_236796
  have hstable : (prefixWord ++ tailWord_236796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236796).length < 2 ^ (prefixWord ++ tailWord_236796).sum := by decide
  have hdescent : baseEnd_236796 < baseStart_236796 := by decide
  rcases family_descends (prefixWord ++ tailWord_236796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236834 : List Nat := [3, 3, 1, 1, 5, 6]
def baseStart_236834 : Nat := 118140960795 + 236834 * 2 ^ 59
def prefixEnd_236834 : Nat := 4983230072969 + 3 ^ 40 * 236834 * 2
def baseEnd_236834 : Nat := 8007221552397143676433

theorem tailTrace_236834 : CollatzResearch.WordTrace tailWord_236834 prefixEnd_236834 8007221552397143676433 := by
  unfold tailWord_236834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159511405999585218019389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5758697082665560581385037 2159511405999585218019389)
  ·
    refine ⟨809816777249844456757271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2159511405999585218019389 809816777249844456757271)
    ·
      refine ⟨1214725165874766685135907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809816777249844456757271 1214725165874766685135907)
      ·
        refine ⟨1822087748812150027703861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214725165874766685135907 1822087748812150027703861)
        ·
          refine ⟨170820726451139065097237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1822087748812150027703861 170820726451139065097237)
          ·
            refine ⟨8007221552397143676433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170820726451139065097237 8007221552397143676433)
            ·
              rfl

theorem cell19_236834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 6].length) (baseStart_236834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236834 prefixEnd_236834 := by exact prefixLift 236834
  have htrace : WordTrace (prefixWord ++ tailWord_236834) baseStart_236834 baseEnd_236834 := by
    simpa [prefixWord, tailWord_236834, baseEnd_236834] using wordTrace_append hprefix tailTrace_236834
  have hstable : (prefixWord ++ tailWord_236834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236834).length < 2 ^ (prefixWord ++ tailWord_236834).sum := by decide
  have hdescent : baseEnd_236834 < baseStart_236834 := by decide
  rcases family_descends (prefixWord ++ tailWord_236834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236853 : List Nat := [1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_236853 : Nat := 118140960795 + 236853 * 2 ^ 59
def prefixEnd_236853 : Nat := 4983230072969 + 3 ^ 40 * 236853 * 2
def baseEnd_236853 : Nat := 72070775383387878665623

theorem tailTrace_236853 : CollatzResearch.WordTrace tailWord_236853 prefixEnd_236853 72070775383387878665623 := by
  unfold tailWord_236853
  simp only [CollatzResearch.WordTrace]
  refine ⟨8638738610929507117019213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5759159073953004744679475 8638738610929507117019213)
  ·
    refine ⟨3239526979098565168882205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8638738610929507117019213 3239526979098565168882205)
    ·
      refine ⟨1214822617161961938330827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3239526979098565168882205 1214822617161961938330827)
      ·
        refine ⟨1822233925742942907496241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214822617161961938330827 1822233925742942907496241)
        ·
          refine ⟨1366675444307207180622181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822233925742942907496241 1366675444307207180622181)
          ·
            refine ⟨256251645807601346366659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1366675444307207180622181 256251645807601346366659)
            ·
              refine ⟨384377468711402019549989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256251645807601346366659 384377468711402019549989)
              ·
                refine ⟨72070775383387878665623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384377468711402019549989 72070775383387878665623)
                ·
                  rfl

theorem cell19_236853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_236853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236853 prefixEnd_236853 := by exact prefixLift 236853
  have htrace : WordTrace (prefixWord ++ tailWord_236853) baseStart_236853 baseEnd_236853 := by
    simpa [prefixWord, tailWord_236853, baseEnd_236853] using wordTrace_append hprefix tailTrace_236853
  have hstable : (prefixWord ++ tailWord_236853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236853).length < 2 ^ (prefixWord ++ tailWord_236853).sum := by decide
  have hdescent : baseEnd_236853 < baseStart_236853 := by decide
  rcases family_descends (prefixWord ++ tailWord_236853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236929 : List Nat := [1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_236929 : Nat := 118140960795 + 236929 * 2 ^ 59
def prefixEnd_236929 : Nat := 4983230072969 + 3 ^ 40 * 236929 * 2
def baseEnd_236929 : Nat := 72093901030642220976527

theorem tailTrace_236929 : CollatzResearch.WordTrace tailWord_236929 prefixEnd_236929 72093901030642220976527 := by
  unfold tailWord_236929
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641510558654172096785841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5761007039102781397857227 8641510558654172096785841)
  ·
    refine ⟨6481132918990629072589381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8641510558654172096785841 6481132918990629072589381)
    ·
      refine ⟨1215212422310742951110509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6481132918990629072589381 1215212422310742951110509)
      ·
        refine ⟨455704658366528606666441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1215212422310742951110509 455704658366528606666441)
        ·
          refine ⟨341778493774896454999831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455704658366528606666441 341778493774896454999831)
          ·
            refine ⟨512667740662344682499747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341778493774896454999831 512667740662344682499747)
            ·
              refine ⟨769001610993517023749621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512667740662344682499747 769001610993517023749621)
              ·
                refine ⟨72093901030642220976527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 769001610993517023749621 72093901030642220976527)
                ·
                  rfl

theorem cell19_236929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_236929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236929 prefixEnd_236929 := by exact prefixLift 236929
  have htrace : WordTrace (prefixWord ++ tailWord_236929) baseStart_236929 baseEnd_236929 := by
    simpa [prefixWord, tailWord_236929, baseEnd_236929] using wordTrace_append hprefix tailTrace_236929
  have hstable : (prefixWord ++ tailWord_236929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236929).length < 2 ^ (prefixWord ++ tailWord_236929).sum := by decide
  have hdescent : baseEnd_236929 < baseStart_236929 := by decide
  rcases family_descends (prefixWord ++ tailWord_236929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236931 : List Nat := [1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_236931 : Nat := 118140960795 + 236931 * 2 ^ 59
def prefixEnd_236931 : Nat := 4983230072969 + 3 ^ 40 * 236931 * 2
def baseEnd_236931 : Nat := 72094509600306808932077

theorem tailTrace_236931 : CollatzResearch.WordTrace tailWord_236931 prefixEnd_236931 72094509600306808932077 := by
  unfold tailWord_236931
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641583504646926438358647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5761055669764617625572431 8641583504646926438358647)
  ·
    refine ⟨12962375256970389657537971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8641583504646926438358647 12962375256970389657537971)
    ·
      refine ⟨19443562885455584486306957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12962375256970389657537971 19443562885455584486306957)
      ·
        refine ⟨7291336082045844182365109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19443562885455584486306957 7291336082045844182365109)
        ·
          refine ⟨683562757691797892096729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7291336082045844182365109 683562757691797892096729)
          ·
            refine ⟨512672068268848419072547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683562757691797892096729 512672068268848419072547)
            ·
              refine ⟨769008102403272628608821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512672068268848419072547 769008102403272628608821)
              ·
                refine ⟨72094509600306808932077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 769008102403272628608821 72094509600306808932077)
                ·
                  rfl

theorem cell19_236931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_236931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236931 prefixEnd_236931 := by exact prefixLift 236931
  have htrace : WordTrace (prefixWord ++ tailWord_236931) baseStart_236931 baseEnd_236931 := by
    simpa [prefixWord, tailWord_236931, baseEnd_236931] using wordTrace_append hprefix tailTrace_236931
  have hstable : (prefixWord ++ tailWord_236931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236931).length < 2 ^ (prefixWord ++ tailWord_236931).sum := by decide
  have hdescent : baseEnd_236931 < baseStart_236931 := by decide
  rcases family_descends (prefixWord ++ tailWord_236931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236946 : List Nat := [3, 2, 3, 3, 1, 2, 5]
def baseStart_236946 : Nat := 118140960795 + 236946 * 2 ^ 59
def prefixEnd_236946 : Nat := 4983230072969 + 3 ^ 40 * 236946 * 2
def baseEnd_236946 : Nat := 24033024624263739532901

theorem tailTrace_236946 : CollatzResearch.WordTrace tailWord_236946 prefixEnd_236946 24033024624263739532901 := by
  unfold tailWord_236946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160532649898146000038673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5761420399728389333436461 2160532649898146000038673)
  ·
    refine ⟨1620399487423609500029005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2160532649898146000038673 1620399487423609500029005)
    ·
      refine ⟨607649807783853562510877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1620399487423609500029005 607649807783853562510877)
      ·
        refine ⟨227868677918945085941579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607649807783853562510877 227868677918945085941579)
        ·
          refine ⟨341803016878417628912369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227868677918945085941579 341803016878417628912369)
          ·
            refine ⟨256352262658813221684277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341803016878417628912369 256352262658813221684277)
            ·
              refine ⟨24033024624263739532901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256352262658813221684277 24033024624263739532901)
              ·
                rfl

theorem cell19_236946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_236946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236946 prefixEnd_236946 := by exact prefixLift 236946
  have htrace : WordTrace (prefixWord ++ tailWord_236946) baseStart_236946 baseEnd_236946 := by
    simpa [prefixWord, tailWord_236946, baseEnd_236946] using wordTrace_append hprefix tailTrace_236946
  have hstable : (prefixWord ++ tailWord_236946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236946).length < 2 ^ (prefixWord ++ tailWord_236946).sum := by decide
  have hdescent : baseEnd_236946 < baseStart_236946 := by decide
  rcases family_descends (prefixWord ++ tailWord_236946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236948 : List Nat := [2, 4, 2, 1, 2, 3, 5]
def baseStart_236948 : Nat := 118140960795 + 236948 * 2 ^ 59
def prefixEnd_236948 : Nat := 4983230072969 + 3 ^ 40 * 236948 * 2
def baseEnd_236948 : Nat := 24033227480818602184751

theorem tailTrace_236948 : CollatzResearch.WordTrace tailWord_236948 prefixEnd_236948 24033227480818602184751 := by
  unfold tailWord_236948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321101772792669170863749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5761469030390225561151665 4321101772792669170863749)
  ·
    refine ⟨810206582398625469536953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4321101772792669170863749 810206582398625469536953)
    ·
      refine ⟨607654936798969102152715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 810206582398625469536953 607654936798969102152715)
      ·
        refine ⟨911482405198453653229073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607654936798969102152715 911482405198453653229073)
        ·
          refine ⟨683611803898840239921805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911482405198453653229073 683611803898840239921805)
          ·
            refine ⟨256354426462065089970677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683611803898840239921805 256354426462065089970677)
            ·
              refine ⟨24033227480818602184751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256354426462065089970677 24033227480818602184751)
              ·
                rfl

theorem cell19_236948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_236948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_236948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_236948 prefixEnd_236948 := by exact prefixLift 236948
  have htrace : WordTrace (prefixWord ++ tailWord_236948) baseStart_236948 baseEnd_236948 := by
    simpa [prefixWord, tailWord_236948, baseEnd_236948] using wordTrace_append hprefix tailTrace_236948
  have hstable : (prefixWord ++ tailWord_236948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236948).length < 2 ^ (prefixWord ++ tailWord_236948).sum := by decide
  have hdescent : baseEnd_236948 < baseStart_236948 := by decide
  rcases family_descends (prefixWord ++ tailWord_236948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237096 : List Nat := [2, 1, 5, 2, 3, 1, 2, 3]
def baseStart_237096 : Nat := 118140960795 + 237096 * 2 ^ 59
def prefixEnd_237096 : Nat := 4983230072969 + 3 ^ 40 * 237096 * 2
def baseEnd_237096 : Nat := 72144716597635315264961

theorem tailTrace_237096 : CollatzResearch.WordTrace tailWord_237096 prefixEnd_237096 72144716597635315264961 := by
  unfold tailWord_237096
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323800774524579809057571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5765067699366106412076761 4323800774524579809057571)
  ·
    refine ⟨6485701161786869713586357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4323800774524579809057571 6485701161786869713586357)
    ·
      refine ⟨608034483917519035648721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6485701161786869713586357 608034483917519035648721)
      ·
        refine ⟨456025862938139276736541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608034483917519035648721 456025862938139276736541)
        ·
          refine ⟨171009698601802228776203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456025862938139276736541 171009698601802228776203)
          ·
            refine ⟨256514547902703343164305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171009698601802228776203 256514547902703343164305)
            ·
              refine ⟨192385910927027507373229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256514547902703343164305 192385910927027507373229)
              ·
                refine ⟨72144716597635315264961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192385910927027507373229 72144716597635315264961)
                ·
                  rfl

theorem cell19_237096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_237096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237096 prefixEnd_237096 := by exact prefixLift 237096
  have htrace : WordTrace (prefixWord ++ tailWord_237096) baseStart_237096 baseEnd_237096 := by
    simpa [prefixWord, tailWord_237096, baseEnd_237096] using wordTrace_append hprefix tailTrace_237096
  have hstable : (prefixWord ++ tailWord_237096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237096).length < 2 ^ (prefixWord ++ tailWord_237096).sum := by decide
  have hdescent : baseEnd_237096 < baseStart_237096 := by decide
  rcases family_descends (prefixWord ++ tailWord_237096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237140 : List Nat := [2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_237140 : Nat := 118140960795 + 237140 * 2 ^ 59
def prefixEnd_237140 : Nat := 4983230072969 + 3 ^ 40 * 237140 * 2
def baseEnd_237140 : Nat := 72158105130256250287063

theorem tailTrace_237140 : CollatzResearch.WordTrace tailWord_237140 prefixEnd_237140 72158105130256250287063 := by
  unfold tailWord_237140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324603180444877566358437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5766137573926503421811249 4324603180444877566358437)
  ·
    refine ⟨810863096333414543692207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4324603180444877566358437 810863096333414543692207)
    ·
      refine ⟨1216294644500121815538311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810863096333414543692207 1216294644500121815538311)
      ·
        refine ⟨1824441966750182723307467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216294644500121815538311 1824441966750182723307467)
        ·
          refine ⟨2736662950125274084961201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824441966750182723307467 2736662950125274084961201)
          ·
            refine ⟨2052497212593955563720901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736662950125274084961201 2052497212593955563720901)
            ·
              refine ⟨384843227361366668197669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2052497212593955563720901 384843227361366668197669)
              ·
                refine ⟨72158105130256250287063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384843227361366668197669 72158105130256250287063)
                ·
                  rfl

theorem cell19_237140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_237140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237140 prefixEnd_237140 := by exact prefixLift 237140
  have htrace : WordTrace (prefixWord ++ tailWord_237140) baseStart_237140 baseEnd_237140 := by
    simpa [prefixWord, tailWord_237140, baseEnd_237140] using wordTrace_append hprefix tailTrace_237140
  have hstable : (prefixWord ++ tailWord_237140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237140).length < 2 ^ (prefixWord ++ tailWord_237140).sum := by decide
  have hdescent : baseEnd_237140 < baseStart_237140 := by decide
  rcases family_descends (prefixWord ++ tailWord_237140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237161 : List Nat := [1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_237161 : Nat := 118140960795 + 237161 * 2 ^ 59
def prefixEnd_237161 : Nat := 4983230072969 + 3 ^ 40 * 237161 * 2
def baseEnd_237161 : Nat := 72164495111734423820339

theorem tailTrace_237161 : CollatzResearch.WordTrace tailWord_237161 prefixEnd_237161 72164495111734423820339 := by
  unfold tailWord_237161
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649972293813675719231337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5766648195875783812820891 8649972293813675719231337)
  ·
    refine ⟨6487479220360256789423503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8649972293813675719231337 6487479220360256789423503)
    ·
      refine ⟨9731218830540385184135255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6487479220360256789423503 9731218830540385184135255)
      ·
        refine ⟨14596828245810577776202883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731218830540385184135255 14596828245810577776202883)
        ·
          refine ⟨21895242368715866664304325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14596828245810577776202883 21895242368715866664304325)
          ·
            refine ⟨4105357944134224999557061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21895242368715866664304325 4105357944134224999557061)
            ·
              refine ⟨769754614525167187416949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4105357944134224999557061 769754614525167187416949)
              ·
                refine ⟨72164495111734423820339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 769754614525167187416949 72164495111734423820339)
                ·
                  rfl

theorem cell19_237161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_237161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237161 prefixEnd_237161 := by exact prefixLift 237161
  have htrace : WordTrace (prefixWord ++ tailWord_237161) baseStart_237161 baseEnd_237161 := by
    simpa [prefixWord, tailWord_237161, baseEnd_237161] using wordTrace_append hprefix tailTrace_237161
  have hstable : (prefixWord ++ tailWord_237161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237161).length < 2 ^ (prefixWord ++ tailWord_237161).sum := by decide
  have hdescent : baseEnd_237161 < baseStart_237161 := by decide
  rcases family_descends (prefixWord ++ tailWord_237161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237256 : List Nat := [2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_237256 : Nat := 118140960795 + 237256 * 2 ^ 59
def prefixEnd_237256 : Nat := 4983230072969 + 3 ^ 40 * 237256 * 2
def baseEnd_237256 : Nat := 72193402170802351708969

theorem tailTrace_237256 : CollatzResearch.WordTrace tailWord_237256 prefixEnd_237256 72193402170802351708969 := by
  unfold tailWord_237256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326718614234753471969811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5768958152313004629293081 4326718614234753471969811)
  ·
    refine ⟨6490077921352130207954717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4326718614234753471969811 6490077921352130207954717)
    ·
      refine ⟨2433779220507048827983019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6490077921352130207954717 2433779220507048827983019)
      ·
        refine ⟨3650668830760573241974529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433779220507048827983019 3650668830760573241974529)
        ·
          refine ⟨2738001623070429931480897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650668830760573241974529 2738001623070429931480897)
          ·
            refine ⟨2053501217302822448610673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738001623070429931480897 2053501217302822448610673)
            ·
              refine ⟨1540125912977116836458005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053501217302822448610673 1540125912977116836458005)
              ·
                refine ⟨72193402170802351708969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1540125912977116836458005 72193402170802351708969)
                ·
                  rfl

theorem cell19_237256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_237256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237256 prefixEnd_237256 := by exact prefixLift 237256
  have htrace : WordTrace (prefixWord ++ tailWord_237256) baseStart_237256 baseEnd_237256 := by
    simpa [prefixWord, tailWord_237256, baseEnd_237256] using wordTrace_append hprefix tailTrace_237256
  have hstable : (prefixWord ++ tailWord_237256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237256).length < 2 ^ (prefixWord ++ tailWord_237256).sum := by decide
  have hdescent : baseEnd_237256 < baseStart_237256 := by decide
  rcases family_descends (prefixWord ++ tailWord_237256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237273 : List Nat := [1, 2, 1, 2, 3, 3, 4, 3]
def baseStart_237273 : Nat := 118140960795 + 237273 * 2 ^ 59
def prefixEnd_237273 : Nat := 4983230072969 + 3 ^ 40 * 237273 * 2
def baseEnd_237273 : Nat := 72198575012951349331145

theorem tailTrace_237273 : CollatzResearch.WordTrace tailWord_237273 prefixEnd_237273 72198575012951349331145 := by
  unfold tailWord_237273
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654057269407918847308473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5769371512938612564872315 8654057269407918847308473)
  ·
    refine ⟨6490542952055939135481355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8654057269407918847308473 6490542952055939135481355)
    ·
      refine ⟨9735814428083908703222033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490542952055939135481355 9735814428083908703222033)
      ·
        refine ⟨7301860821062931527416525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9735814428083908703222033 7301860821062931527416525)
        ·
          refine ⟨2738197807898599322781197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7301860821062931527416525 2738197807898599322781197)
          ·
            refine ⟨1026824177961974746042949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2738197807898599322781197 1026824177961974746042949)
            ·
              refine ⟨192529533367870264883053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1026824177961974746042949 192529533367870264883053)
              ·
                refine ⟨72198575012951349331145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192529533367870264883053 72198575012951349331145)
                ·
                  rfl

theorem cell19_237273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_237273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237273 prefixEnd_237273 := by exact prefixLift 237273
  have htrace : WordTrace (prefixWord ++ tailWord_237273) baseStart_237273 baseEnd_237273 := by
    simpa [prefixWord, tailWord_237273, baseEnd_237273] using wordTrace_append hprefix tailTrace_237273
  have hstable : (prefixWord ++ tailWord_237273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237273).length < 2 ^ (prefixWord ++ tailWord_237273).sum := by decide
  have hdescent : baseEnd_237273 < baseStart_237273 := by decide
  rcases family_descends (prefixWord ++ tailWord_237273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237313 : List Nat := [1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_237313 : Nat := 118140960795 + 237313 * 2 ^ 59
def prefixEnd_237313 : Nat := 4983230072969 + 3 ^ 40 * 237313 * 2
def baseEnd_237313 : Nat := 72210746406243108442147

theorem tailTrace_237313 : CollatzResearch.WordTrace tailWord_237313 prefixEnd_237313 72210746406243108442147 := by
  unfold tailWord_237313
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655516189263005678764593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5770344126175337119176395 8655516189263005678764593)
  ·
    refine ⟨6491637141947254259073445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8655516189263005678764593 6491637141947254259073445)
    ·
      refine ⟨1217181964115110173576271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6491637141947254259073445 1217181964115110173576271)
      ·
        refine ⟨1825772946172665260364407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217181964115110173576271 1825772946172665260364407)
        ·
          refine ⟨2738659419258997890546611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825772946172665260364407 2738659419258997890546611)
          ·
            refine ⟨4107989128888496835819917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738659419258997890546611 4107989128888496835819917)
            ·
              refine ⟨1540495923333186313432469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4107989128888496835819917 1540495923333186313432469)
              ·
                refine ⟨72210746406243108442147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1540495923333186313432469 72210746406243108442147)
                ·
                  rfl

theorem cell19_237313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_237313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237313 prefixEnd_237313 := by exact prefixLift 237313
  have htrace : WordTrace (prefixWord ++ tailWord_237313) baseStart_237313 baseEnd_237313 := by
    simpa [prefixWord, tailWord_237313, baseEnd_237313] using wordTrace_append hprefix tailTrace_237313
  have hstable : (prefixWord ++ tailWord_237313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237313).length < 2 ^ (prefixWord ++ tailWord_237313).sum := by decide
  have hdescent : baseEnd_237313 < baseStart_237313 := by decide
  rcases family_descends (prefixWord ++ tailWord_237313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237366 : List Nat := [5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_237366 : Nat := 118140960795 + 237366 * 2 ^ 59
def prefixEnd_237366 : Nat := 4983230072969 + 3 ^ 40 * 237366 * 2
def baseEnd_237366 : Nat := 72226873502354689264225

theorem tailTrace_237366 : CollatzResearch.WordTrace tailWord_237366 prefixEnd_237366 72226873502354689264225 := by
  unfold tailWord_237366
  simp only [CollatzResearch.WordTrace]
  refine ⟨541090578629437233152747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5771632838713997153629301 541090578629437233152747)
  ·
    refine ⟨811635867944155849729121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541090578629437233152747 811635867944155849729121)
    ·
      refine ⟨608726900958116887296841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 811635867944155849729121 608726900958116887296841)
      ·
        refine ⟨456545175718587665472631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608726900958116887296841 456545175718587665472631)
        ·
          refine ⟨684817763577881498208947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456545175718587665472631 684817763577881498208947)
          ·
            refine ⟨1027226645366822247313421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684817763577881498208947 1027226645366822247313421)
            ·
              refine ⟨385209992012558342742533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1027226645366822247313421 385209992012558342742533)
              ·
                refine ⟨72226873502354689264225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385209992012558342742533 72226873502354689264225)
                ·
                  rfl

theorem cell19_237366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_237366 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237366 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237366 prefixEnd_237366 := by exact prefixLift 237366
  have htrace : WordTrace (prefixWord ++ tailWord_237366) baseStart_237366 baseEnd_237366 := by
    simpa [prefixWord, tailWord_237366, baseEnd_237366] using wordTrace_append hprefix tailTrace_237366
  have hstable : (prefixWord ++ tailWord_237366).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237366).length < 2 ^ (prefixWord ++ tailWord_237366).sum := by decide
  have hdescent : baseEnd_237366 < baseStart_237366 := by decide
  rcases family_descends (prefixWord ++ tailWord_237366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237368 : List Nat := [2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_237368 : Nat := 118140960795 + 237368 * 2 ^ 59
def prefixEnd_237368 : Nat := 4983230072969 + 3 ^ 40 * 237368 * 2
def baseEnd_237368 : Nat := 72227482072019277219775

theorem tailTrace_237368 : CollatzResearch.WordTrace tailWord_237368 prefixEnd_237368 72227482072019277219775 := by
  unfold tailWord_237368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328761102031875036008379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5771681469375833381344505 4328761102031875036008379)
  ·
    refine ⟨6493141653047812554012569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328761102031875036008379 6493141653047812554012569)
    ·
      refine ⟨4869856239785859415509427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6493141653047812554012569 4869856239785859415509427)
      ·
        refine ⟨7304784359678789123264141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869856239785859415509427 7304784359678789123264141)
        ·
          refine ⟨2739294134879545921224053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7304784359678789123264141 2739294134879545921224053)
          ·
            refine ⟨256808825144957430114755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2739294134879545921224053 256808825144957430114755)
            ·
              refine ⟨385213237717436145172133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256808825144957430114755 385213237717436145172133)
              ·
                refine ⟨72227482072019277219775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385213237717436145172133 72227482072019277219775)
                ·
                  rfl

theorem cell19_237368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_237368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237368 prefixEnd_237368 := by exact prefixLift 237368
  have htrace : WordTrace (prefixWord ++ tailWord_237368) baseStart_237368 baseEnd_237368 := by
    simpa [prefixWord, tailWord_237368, baseEnd_237368] using wordTrace_append hprefix tailTrace_237368
  have hstable : (prefixWord ++ tailWord_237368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237368).length < 2 ^ (prefixWord ++ tailWord_237368).sum := by decide
  have hdescent : baseEnd_237368 < baseStart_237368 := by decide
  rcases family_descends (prefixWord ++ tailWord_237368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237408 : List Nat := [2, 1, 1, 3, 3, 3, 6]
def baseStart_237408 : Nat := 118140960795 + 237408 * 2 ^ 59
def prefixEnd_237408 : Nat := 4983230072969 + 3 ^ 40 * 237408 * 2
def baseEnd_237408 : Nat := 24079884488437012110259

theorem tailTrace_237408 : CollatzResearch.WordTrace tailWord_237408 prefixEnd_237408 24079884488437012110259 := by
  unfold tailWord_237408
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329490561959418451736439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5772654082612557935648585 4329490561959418451736439)
  ·
    refine ⟨6494235842939127677604659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4329490561959418451736439 6494235842939127677604659)
    ·
      refine ⟨9741353764408691516406989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494235842939127677604659 9741353764408691516406989)
      ·
        refine ⟨3653007661653259318652621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9741353764408691516406989 3653007661653259318652621)
        ·
          refine ⟨1369877873119972244494733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3653007661653259318652621 1369877873119972244494733)
          ·
            refine ⟨513704202419989591685525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1369877873119972244494733 513704202419989591685525)
            ·
              refine ⟨24079884488437012110259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 513704202419989591685525 24079884488437012110259)
              ·
                rfl

theorem cell19_237408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_237408 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237408 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237408 prefixEnd_237408 := by exact prefixLift 237408
  have htrace : WordTrace (prefixWord ++ tailWord_237408) baseStart_237408 baseEnd_237408 := by
    simpa [prefixWord, tailWord_237408, baseEnd_237408] using wordTrace_append hprefix tailTrace_237408
  have hstable : (prefixWord ++ tailWord_237408).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237408).length < 2 ^ (prefixWord ++ tailWord_237408).sum := by decide
  have hdescent : baseEnd_237408 < baseStart_237408 := by decide
  rcases family_descends (prefixWord ++ tailWord_237408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237444 : List Nat := [2, 3, 2, 1, 1, 1, 6, 3]
def baseStart_237444 : Nat := 118140960795 + 237444 * 2 ^ 59
def prefixEnd_237444 : Nat := 4983230072969 + 3 ^ 40 * 237444 * 2
def baseEnd_237444 : Nat := 72250607719273619530679

theorem tailTrace_237444 : CollatzResearch.WordTrace tailWord_237444 prefixEnd_237444 72250607719273619530679 := by
  unfold tailWord_237444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330147075894207525891693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5773529434525610034522257 4330147075894207525891693)
  ·
    refine ⟨1623805153460327822209385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4330147075894207525891693 1623805153460327822209385)
    ·
      refine ⟨1217853865095245866657039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1623805153460327822209385 1217853865095245866657039)
      ·
        refine ⟨1826780797642868799985559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217853865095245866657039 1826780797642868799985559)
        ·
          refine ⟨2740171196464303199978339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826780797642868799985559 2740171196464303199978339)
          ·
            refine ⟨4110256794696454799967509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740171196464303199978339 4110256794696454799967509)
            ·
              refine ⟨192668287251396318748477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4110256794696454799967509 192668287251396318748477)
              ·
                refine ⟨72250607719273619530679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192668287251396318748477 72250607719273619530679)
                ·
                  rfl

theorem cell19_237444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_237444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237444 prefixEnd_237444 := by exact prefixLift 237444
  have htrace : WordTrace (prefixWord ++ tailWord_237444) baseStart_237444 baseEnd_237444 := by
    simpa [prefixWord, tailWord_237444, baseEnd_237444] using wordTrace_append hprefix tailTrace_237444
  have hstable : (prefixWord ++ tailWord_237444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237444).length < 2 ^ (prefixWord ++ tailWord_237444).sum := by decide
  have hdescent : baseEnd_237444 < baseStart_237444 := by decide
  rcases family_descends (prefixWord ++ tailWord_237444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237522 : List Nat := [3, 2, 2, 3, 9]
def baseStart_237522 : Nat := 118140960795 + 237522 * 2 ^ 59
def prefixEnd_237522 : Nat := 4983230072969 + 3 ^ 40 * 237522 * 2
def baseEnd_237522 : Nat := 2676827479118242585079

theorem tailTrace_237522 : CollatzResearch.WordTrace tailWord_237522 prefixEnd_237522 2676827479118242585079 := by
  unfold tailWord_237522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2165784761376458593280705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5775426030337222915415213 2165784761376458593280705)
  ·
    refine ⟨1624338571032343944960529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2165784761376458593280705 1624338571032343944960529)
    ·
      refine ⟨1218253928274257958720397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1624338571032343944960529 1218253928274257958720397)
      ·
        refine ⟨456845223102846734520149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1218253928274257958720397 456845223102846734520149)
        ·
          refine ⟨2676827479118242585079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 456845223102846734520149 2676827479118242585079)
          ·
            rfl

theorem cell19_237522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 9].length) (baseStart_237522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237522 prefixEnd_237522 := by exact prefixLift 237522
  have htrace : WordTrace (prefixWord ++ tailWord_237522) baseStart_237522 baseEnd_237522 := by
    simpa [prefixWord, tailWord_237522, baseEnd_237522] using wordTrace_append hprefix tailTrace_237522
  have hstable : (prefixWord ++ tailWord_237522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237522).length < 2 ^ (prefixWord ++ tailWord_237522).sum := by decide
  have hdescent : baseEnd_237522 < baseStart_237522 := by decide
  rcases family_descends (prefixWord ++ tailWord_237522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237539 : List Nat := [1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_237539 : Nat := 118140960795 + 237539 * 2 ^ 59
def prefixEnd_237539 : Nat := 4983230072969 + 3 ^ 40 * 237539 * 2
def baseEnd_237539 : Nat := 72279514778341547419309

theorem tailTrace_237539 : CollatzResearch.WordTrace tailWord_237539 prefixEnd_237539 72279514778341547419309 := by
  unfold tailWord_237539
  simp only [CollatzResearch.WordTrace]
  refine ⟨8663759086444246276491671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5775839390962830850994447 8663759086444246276491671)
  ·
    refine ⟨12995638629666369414737507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8663759086444246276491671 12995638629666369414737507)
    ·
      refine ⟨19493457944499554122106261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12995638629666369414737507 19493457944499554122106261)
      ·
        refine ⟨913755841148416599473731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19493457944499554122106261 913755841148416599473731)
        ·
          refine ⟨1370633761722624899210597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913755841148416599473731 1370633761722624899210597)
          ·
            refine ⟨256993830322992168601987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1370633761722624899210597 256993830322992168601987)
            ·
              refine ⟨385490745484488252902981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256993830322992168601987 385490745484488252902981)
              ·
                refine ⟨72279514778341547419309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385490745484488252902981 72279514778341547419309)
                ·
                  rfl

theorem cell19_237539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_237539 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237539 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237539 prefixEnd_237539 := by exact prefixLift 237539
  have htrace : WordTrace (prefixWord ++ tailWord_237539) baseStart_237539 baseEnd_237539 := by
    simpa [prefixWord, tailWord_237539, baseEnd_237539] using wordTrace_append hprefix tailTrace_237539
  have hstable : (prefixWord ++ tailWord_237539).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237539).length < 2 ^ (prefixWord ++ tailWord_237539).sum := by decide
  have hdescent : baseEnd_237539 < baseStart_237539 := by decide
  rcases family_descends (prefixWord ++ tailWord_237539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237617 : List Nat := [1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_237617 : Nat := 118140960795 + 237617 * 2 ^ 59
def prefixEnd_237617 : Nat := 4983230072969 + 3 ^ 40 * 237617 * 2
def baseEnd_237617 : Nat := 72303248995260477685763

theorem tailTrace_237617 : CollatzResearch.WordTrace tailWord_237617 prefixEnd_237617 72303248995260477685763 := by
  unfold tailWord_237617
  simp only [CollatzResearch.WordTrace]
  refine ⟨8666603980161665597831105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5777735986774443731887403 8666603980161665597831105)
  ·
    refine ⟨6499952985121249198373329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8666603980161665597831105 6499952985121249198373329)
    ·
      refine ⟨4874964738840936898779997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6499952985121249198373329 4874964738840936898779997)
      ·
        refine ⟨1828111777065351337042499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4874964738840936898779997 1828111777065351337042499)
        ·
          refine ⟨2742167665598027005563749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828111777065351337042499 2742167665598027005563749)
          ·
            refine ⟨514156437299630063543203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2742167665598027005563749 514156437299630063543203)
            ·
              refine ⟨771234655949445095314805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514156437299630063543203 771234655949445095314805)
              ·
                refine ⟨72303248995260477685763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 771234655949445095314805 72303248995260477685763)
                ·
                  rfl

theorem cell19_237617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_237617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237617 prefixEnd_237617 := by exact prefixLift 237617
  have htrace : WordTrace (prefixWord ++ tailWord_237617) baseStart_237617 baseEnd_237617 := by
    simpa [prefixWord, tailWord_237617, baseEnd_237617] using wordTrace_append hprefix tailTrace_237617
  have hstable : (prefixWord ++ tailWord_237617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237617).length < 2 ^ (prefixWord ++ tailWord_237617).sum := by decide
  have hdescent : baseEnd_237617 < baseStart_237617 := by decide
  rcases family_descends (prefixWord ++ tailWord_237617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237729 : List Nat := [1, 2, 3, 3, 1, 3, 3, 3]
def baseStart_237729 : Nat := 118140960795 + 237729 * 2 ^ 59
def prefixEnd_237729 : Nat := 4983230072969 + 3 ^ 40 * 237729 * 2
def baseEnd_237729 : Nat := 72337328896477403196569

theorem tailTrace_237729 : CollatzResearch.WordTrace tailWord_237729 prefixEnd_237729 72337328896477403196569 := by
  unfold tailWord_237729
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670688955755908725908241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5780459303837272483938827 8670688955755908725908241)
  ·
    refine ⟨6503016716816931544431181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8670688955755908725908241 6503016716816931544431181)
    ·
      refine ⟨2438631268806349329161693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6503016716816931544431181 2438631268806349329161693)
      ·
        refine ⟨914486725802380998435635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2438631268806349329161693 914486725802380998435635)
        ·
          refine ⟨1371730088703571497653453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914486725802380998435635 1371730088703571497653453)
          ·
            refine ⟨514398783263839311620045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1371730088703571497653453 514398783263839311620045)
            ·
              refine ⟨192899543723939741857517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514398783263839311620045 192899543723939741857517)
              ·
                refine ⟨72337328896477403196569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192899543723939741857517 72337328896477403196569)
                ·
                  rfl

theorem cell19_237729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_237729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237729 prefixEnd_237729 := by exact prefixLift 237729
  have htrace : WordTrace (prefixWord ++ tailWord_237729) baseStart_237729 baseEnd_237729 := by
    simpa [prefixWord, tailWord_237729, baseEnd_237729] using wordTrace_append hprefix tailTrace_237729
  have hstable : (prefixWord ++ tailWord_237729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237729).length < 2 ^ (prefixWord ++ tailWord_237729).sum := by decide
  have hdescent : baseEnd_237729 < baseStart_237729 := by decide
  rcases family_descends (prefixWord ++ tailWord_237729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237752 : List Nat := [2, 1, 2, 1, 2, 1, 10]
def baseStart_237752 : Nat := 118140960795 + 237752 * 2 ^ 59
def prefixEnd_237752 : Nat := 4983230072969 + 3 ^ 40 * 237752 * 2
def baseEnd_237752 : Nat := 24114775815873388228465

theorem tailTrace_237752 : CollatzResearch.WordTrace tailWord_237752 prefixEnd_237752 24114775815873388228465 := by
  unfold tailWord_237752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4335763917336291826997755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5781018556448389102663673 4335763917336291826997755)
  ·
    refine ⟨6503645876004437740496633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4335763917336291826997755 6503645876004437740496633)
    ·
      refine ⟨4877734407003328305372475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6503645876004437740496633 4877734407003328305372475)
      ·
        refine ⟨7316601610504992458058713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4877734407003328305372475 7316601610504992458058713)
        ·
          refine ⟨5487451207878744343544035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7316601610504992458058713 5487451207878744343544035)
          ·
            refine ⟨8231176811818116515316053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5487451207878744343544035 8231176811818116515316053)
            ·
              refine ⟨24114775815873388228465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8231176811818116515316053 24114775815873388228465)
              ·
                rfl

theorem cell19_237752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_237752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237752 prefixEnd_237752 := by exact prefixLift 237752
  have htrace : WordTrace (prefixWord ++ tailWord_237752) baseStart_237752 baseEnd_237752 := by
    simpa [prefixWord, tailWord_237752, baseEnd_237752] using wordTrace_append hprefix tailTrace_237752
  have hstable : (prefixWord ++ tailWord_237752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237752).length < 2 ^ (prefixWord ++ tailWord_237752).sum := by decide
  have hdescent : baseEnd_237752 < baseStart_237752 := by decide
  rcases family_descends (prefixWord ++ tailWord_237752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237771 : List Nat := [1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_237771 : Nat := 118140960795 + 237771 * 2 ^ 59
def prefixEnd_237771 : Nat := 4983230072969 + 3 ^ 40 * 237771 * 2
def baseEnd_237771 : Nat := 72350108859433750263121

theorem tailTrace_237771 : CollatzResearch.WordTrace tailWord_237771 prefixEnd_237771 72350108859433750263121 := by
  unfold tailWord_237771
  simp only [CollatzResearch.WordTrace]
  refine ⟨8672220821603749898937167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5781480547735833265958111 8672220821603749898937167)
  ·
    refine ⟨13008331232405624848405751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8672220821603749898937167 13008331232405624848405751)
    ·
      refine ⟨19512496848608437272608627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13008331232405624848405751 19512496848608437272608627)
      ·
        refine ⟨29268745272912655908912941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19512496848608437272608627 29268745272912655908912941)
        ·
          refine ⟨10975779477342245965842353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29268745272912655908912941 10975779477342245965842353)
          ·
            refine ⟨8231834608006684474381765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10975779477342245965842353 8231834608006684474381765)
            ·
              refine ⟨1543468989001253338946581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8231834608006684474381765 1543468989001253338946581)
              ·
                refine ⟨72350108859433750263121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1543468989001253338946581 72350108859433750263121)
                ·
                  rfl

theorem cell19_237771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_237771 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237771 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237771 prefixEnd_237771 := by exact prefixLift 237771
  have htrace : WordTrace (prefixWord ++ tailWord_237771) baseStart_237771 baseEnd_237771 := by
    simpa [prefixWord, tailWord_237771, baseEnd_237771] using wordTrace_append hprefix tailTrace_237771
  have hstable : (prefixWord ++ tailWord_237771).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237771).length < 2 ^ (prefixWord ++ tailWord_237771).sum := by decide
  have hdescent : baseEnd_237771 < baseStart_237771 := by decide
  rcases family_descends (prefixWord ++ tailWord_237771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237782 : List Nat := [5, 2, 1, 2, 1, 3, 2, 3]
def baseStart_237782 : Nat := 118140960795 + 237782 * 2 ^ 59
def prefixEnd_237782 : Nat := 4983230072969 + 3 ^ 40 * 237782 * 2
def baseEnd_237782 : Nat := 72353455992588984018647

theorem tailTrace_237782 : CollatzResearch.WordTrace tailWord_237782 prefixEnd_237782 72353455992588984018647 := by
  unfold tailWord_237782
  simp only [CollatzResearch.WordTrace]
  refine ⟨542038876535243673599225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5781748016375932518391733 542038876535243673599225)
  ·
    refine ⟨406529157401432755199419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 542038876535243673599225 406529157401432755199419)
    ·
      refine ⟨609793736102149132799129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406529157401432755199419 609793736102149132799129)
      ·
        refine ⟨457345302076611849599347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609793736102149132799129 457345302076611849599347)
        ·
          refine ⟨686017953114917774399021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457345302076611849599347 686017953114917774399021)
          ·
            refine ⟨257256732418094165399633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686017953114917774399021 257256732418094165399633)
            ·
              refine ⟨192942549313570624049725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257256732418094165399633 192942549313570624049725)
              ·
                refine ⟨72353455992588984018647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192942549313570624049725 72353455992588984018647)
                ·
                  rfl

theorem cell19_237782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_237782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237782 prefixEnd_237782 := by exact prefixLift 237782
  have htrace : WordTrace (prefixWord ++ tailWord_237782) baseStart_237782 baseEnd_237782 := by
    simpa [prefixWord, tailWord_237782, baseEnd_237782] using wordTrace_append hprefix tailTrace_237782
  have hstable : (prefixWord ++ tailWord_237782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237782).length < 2 ^ (prefixWord ++ tailWord_237782).sum := by decide
  have hdescent : baseEnd_237782 < baseStart_237782 := by decide
  rcases family_descends (prefixWord ++ tailWord_237782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237805 : List Nat := [1, 5, 1, 2, 3, 2, 5]
def baseStart_237805 : Nat := 118140960795 + 237805 * 2 ^ 59
def prefixEnd_237805 : Nat := 4983230072969 + 3 ^ 40 * 237805 * 2
def baseEnd_237805 : Nat := 24120151514577248502491

theorem tailTrace_237805 : CollatzResearch.WordTrace tailWord_237805 prefixEnd_237805 24120151514577248502491 := by
  unfold tailWord_237805
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673460903480573705674869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5782307268987049137116579 8673460903480573705674869)
  ·
    refine ⟨813136959701303784907019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8673460903480573705674869 813136959701303784907019)
    ·
      refine ⟨1219705439551955677360529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813136959701303784907019 1219705439551955677360529)
      ·
        refine ⟨914779079663966758020397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1219705439551955677360529 914779079663966758020397)
        ·
          refine ⟨343042154873987534257649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 914779079663966758020397 343042154873987534257649)
          ·
            refine ⟨257281616155490650693237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343042154873987534257649 257281616155490650693237)
            ·
              refine ⟨24120151514577248502491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257281616155490650693237 24120151514577248502491)
              ·
                rfl

theorem cell19_237805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_237805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237805 prefixEnd_237805 := by exact prefixLift 237805
  have htrace : WordTrace (prefixWord ++ tailWord_237805) baseStart_237805 baseEnd_237805 := by
    simpa [prefixWord, tailWord_237805, baseEnd_237805] using wordTrace_append hprefix tailTrace_237805
  have hstable : (prefixWord ++ tailWord_237805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237805).length < 2 ^ (prefixWord ++ tailWord_237805).sum := by decide
  have hdescent : baseEnd_237805 < baseStart_237805 := by decide
  rcases family_descends (prefixWord ++ tailWord_237805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237807 : List Nat := [1, 1, 2, 1, 6, 3, 5]
def baseStart_237807 : Nat := 118140960795 + 237807 * 2 ^ 59
def prefixEnd_237807 : Nat := 4983230072969 + 3 ^ 40 * 237807 * 2
def baseEnd_237807 : Nat := 24120354371132111154341

theorem tailTrace_237807 : CollatzResearch.WordTrace tailWord_237807 prefixEnd_237807 24120354371132111154341 := by
  unfold tailWord_237807
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673533849473328047247675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5782355899648885364831783 8673533849473328047247675)
  ·
    refine ⟨13010300774209992070871513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8673533849473328047247675 13010300774209992070871513)
    ·
      refine ⟨9757725580657494053153635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13010300774209992070871513 9757725580657494053153635)
      ·
        refine ⟨14636588370986241079730453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9757725580657494053153635 14636588370986241079730453)
        ·
          refine ⟨686090079889980050612365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14636588370986241079730453 686090079889980050612365)
          ·
            refine ⟨257283779958742518979637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686090079889980050612365 257283779958742518979637)
            ·
              refine ⟨24120354371132111154341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257283779958742518979637 24120354371132111154341)
              ·
                rfl

theorem cell19_237807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_237807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237807 prefixEnd_237807 := by exact prefixLift 237807
  have htrace : WordTrace (prefixWord ++ tailWord_237807) baseStart_237807 baseEnd_237807 := by
    simpa [prefixWord, tailWord_237807, baseEnd_237807] using wordTrace_append hprefix tailTrace_237807
  have hstable : (prefixWord ++ tailWord_237807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237807).length < 2 ^ (prefixWord ++ tailWord_237807).sum := by decide
  have hdescent : baseEnd_237807 < baseStart_237807 := by decide
  rcases family_descends (prefixWord ++ tailWord_237807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237809 : List Nat := [1, 2, 2, 2, 2, 1, 9]
def baseStart_237809 : Nat := 118140960795 + 237809 * 2 ^ 59
def prefixEnd_237809 : Nat := 4983230072969 + 3 ^ 40 * 237809 * 2
def baseEnd_237809 : Nat := 24120557227686973806191

theorem tailTrace_237809 : CollatzResearch.WordTrace tailWord_237809 prefixEnd_237809 24120557227686973806191 := by
  unfold tailWord_237809
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673606795466082388820481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5782404530310721592546987 8673606795466082388820481)
  ·
    refine ⟨6505205096599561791615361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8673606795466082388820481 6505205096599561791615361)
    ·
      refine ⟨4878903822449671343711521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6505205096599561791615361 4878903822449671343711521)
      ·
        refine ⟨3659177866837253507783641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4878903822449671343711521 3659177866837253507783641)
        ·
          refine ⟨2744383400127940130837731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3659177866837253507783641 2744383400127940130837731)
          ·
            refine ⟨4116575100191910196256597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744383400127940130837731 4116575100191910196256597)
            ·
              refine ⟨24120557227686973806191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4116575100191910196256597 24120557227686973806191)
              ·
                rfl

theorem cell19_237809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_237809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237809 prefixEnd_237809 := by exact prefixLift 237809
  have htrace : WordTrace (prefixWord ++ tailWord_237809) baseStart_237809 baseEnd_237809 := by
    simpa [prefixWord, tailWord_237809, baseEnd_237809] using wordTrace_append hprefix tailTrace_237809
  have hstable : (prefixWord ++ tailWord_237809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237809).length < 2 ^ (prefixWord ++ tailWord_237809).sum := by decide
  have hdescent : baseEnd_237809 < baseStart_237809 := by decide
  rcases family_descends (prefixWord ++ tailWord_237809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237864 : List Nat := [2, 1, 5, 1, 3, 7]
def baseStart_237864 : Nat := 118140960795 + 237864 * 2 ^ 59
def prefixEnd_237864 : Nat := 4983230072969 + 3 ^ 40 * 237864 * 2
def baseEnd_237864 : Nat := 8042045260981898910689

theorem tailTrace_237864 : CollatzResearch.WordTrace tailWord_237864 prefixEnd_237864 8042045260981898910689 := by
  unfold tailWord_237864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337806405133413391036323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5783741873511217854715097 4337806405133413391036323)
  ·
    refine ⟨6506709607700120086554485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4337806405133413391036323 6506709607700120086554485)
    ·
      refine ⟨610004025721886258114483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6506709607700120086554485 610004025721886258114483)
      ·
        refine ⟨915006038582829387171725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610004025721886258114483 915006038582829387171725)
        ·
          refine ⟨343127264468561020189397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 915006038582829387171725 343127264468561020189397)
          ·
            refine ⟨8042045260981898910689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 343127264468561020189397 8042045260981898910689)
            ·
              rfl

theorem cell19_237864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_237864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237864 prefixEnd_237864 := by exact prefixLift 237864
  have htrace : WordTrace (prefixWord ++ tailWord_237864) baseStart_237864 baseEnd_237864 := by
    simpa [prefixWord, tailWord_237864, baseEnd_237864] using wordTrace_append hprefix tailTrace_237864
  have hstable : (prefixWord ++ tailWord_237864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237864).length < 2 ^ (prefixWord ++ tailWord_237864).sum := by decide
  have hdescent : baseEnd_237864 < baseStart_237864 := by decide
  rcases family_descends (prefixWord ++ tailWord_237864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237881 : List Nat := [1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_237881 : Nat := 118140960795 + 237881 * 2 ^ 59
def prefixEnd_237881 : Nat := 4983230072969 + 3 ^ 40 * 237881 * 2
def baseEnd_237881 : Nat := 72383580190986087818377

theorem tailTrace_237881 : CollatzResearch.WordTrace tailWord_237881 prefixEnd_237881 72383580190986087818377 := by
  unfold tailWord_237881
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676232851205238685441497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5784155234136825790294331 8676232851205238685441497)
  ·
    refine ⟨6507174638403929014081123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8676232851205238685441497 6507174638403929014081123)
    ·
      refine ⟨9760761957605893521121685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6507174638403929014081123 9760761957605893521121685)
      ·
        refine ⟨457535716762776258802579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9760761957605893521121685 457535716762776258802579)
        ·
          refine ⟨686303575144164388203869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457535716762776258802579 686303575144164388203869)
          ·
            refine ⟨257363840679061645576451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686303575144164388203869 257363840679061645576451)
            ·
              refine ⟨386045761018592468364677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257363840679061645576451 386045761018592468364677)
              ·
                refine ⟨72383580190986087818377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386045761018592468364677 72383580190986087818377)
                ·
                  rfl

theorem cell19_237881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_237881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237881 prefixEnd_237881 := by exact prefixLift 237881
  have htrace : WordTrace (prefixWord ++ tailWord_237881) baseStart_237881 baseEnd_237881 := by
    simpa [prefixWord, tailWord_237881, baseEnd_237881] using wordTrace_append hprefix tailTrace_237881
  have hstable : (prefixWord ++ tailWord_237881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237881).length < 2 ^ (prefixWord ++ tailWord_237881).sum := by decide
  have hdescent : baseEnd_237881 < baseStart_237881 := by decide
  rcases family_descends (prefixWord ++ tailWord_237881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237923 : List Nat := [1, 1, 1, 5, 2, 1, 8]
def baseStart_237923 : Nat := 118140960795 + 237923 * 2 ^ 59
def prefixEnd_237923 : Nat := 4983230072969 + 3 ^ 40 * 237923 * 2
def baseEnd_237923 : Nat := 24132120051314144961643

theorem tailTrace_237923 : CollatzResearch.WordTrace tailWord_237923 prefixEnd_237923 24132120051314144961643 := by
  unfold tailWord_237923
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677764717053079858470423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5785176478035386572313615 8677764717053079858470423)
  ·
    refine ⟨13016647075579619787705635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677764717053079858470423 13016647075579619787705635)
    ·
      refine ⟨19524970613369429681558453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016647075579619787705635 19524970613369429681558453)
      ·
        refine ⟨1830465995003384032646105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19524970613369429681558453 1830465995003384032646105)
        ·
          refine ⟨1372849496252538024484579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1830465995003384032646105 1372849496252538024484579)
          ·
            refine ⟨2059274244378807036726869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372849496252538024484579 2059274244378807036726869)
            ·
              refine ⟨24132120051314144961643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2059274244378807036726869 24132120051314144961643)
              ·
                rfl

theorem cell19_237923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_237923 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237923 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237923 prefixEnd_237923 := by exact prefixLift 237923
  have htrace : WordTrace (prefixWord ++ tailWord_237923) baseStart_237923 baseEnd_237923 := by
    simpa [prefixWord, tailWord_237923, baseEnd_237923] using wordTrace_append hprefix tailTrace_237923
  have hstable : (prefixWord ++ tailWord_237923).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237923).length < 2 ^ (prefixWord ++ tailWord_237923).sum := by decide
  have hdescent : baseEnd_237923 < baseStart_237923 := by decide
  rcases family_descends (prefixWord ++ tailWord_237923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237955 : List Nat := [1, 1, 1, 3, 7, 1, 2, 3]
def baseStart_237955 : Nat := 118140960795 + 237955 * 2 ^ 59
def prefixEnd_237955 : Nat := 4983230072969 + 3 ^ 40 * 237955 * 2
def baseEnd_237955 : Nat := 72406097268575842173731

theorem tailTrace_237955 : CollatzResearch.WordTrace tailWord_237955 prefixEnd_237955 72406097268575842173731 := by
  unfold tailWord_237955
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678931852937149323635319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5785954568624766215756879 8678931852937149323635319)
  ·
    refine ⟨13018397779405723985452979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8678931852937149323635319 13018397779405723985452979)
    ·
      refine ⟨19527596669108585978179469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13018397779405723985452979 19527596669108585978179469)
      ·
        refine ⟨7322848750915719741817301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19527596669108585978179469 7322848750915719741817301)
        ·
          refine ⟨171629267599587181448843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7322848750915719741817301 171629267599587181448843)
          ·
            refine ⟨257443901399380772173265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171629267599587181448843 257443901399380772173265)
            ·
              refine ⟨193082926049535579129949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257443901399380772173265 193082926049535579129949)
              ·
                refine ⟨72406097268575842173731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193082926049535579129949 72406097268575842173731)
                ·
                  rfl

theorem cell19_237955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_237955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237955 prefixEnd_237955 := by exact prefixLift 237955
  have htrace : WordTrace (prefixWord ++ tailWord_237955) baseStart_237955 baseEnd_237955 := by
    simpa [prefixWord, tailWord_237955, baseEnd_237955] using wordTrace_append hprefix tailTrace_237955
  have hstable : (prefixWord ++ tailWord_237955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237955).length < 2 ^ (prefixWord ++ tailWord_237955).sum := by decide
  have hdescent : baseEnd_237955 < baseStart_237955 := by decide
  rcases family_descends (prefixWord ++ tailWord_237955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237978 : List Nat := [3, 1, 1, 4, 1, 4, 5]
def baseStart_237978 : Nat := 118140960795 + 237978 * 2 ^ 59
def prefixEnd_237978 : Nat := 4983230072969 + 3 ^ 40 * 237978 * 2
def baseEnd_237978 : Nat := 24137698606572867887519

theorem tailTrace_237978 : CollatzResearch.WordTrace tailWord_237978 prefixEnd_237978 24137698606572867887519 := by
  unfold tailWord_237978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169942682963456062930647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5786513821235882834481725 2169942682963456062930647)
  ·
    refine ⟨3254914024445184094395971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2169942682963456062930647 3254914024445184094395971)
    ·
      refine ⟨4882371036667776141593957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254914024445184094395971 4882371036667776141593957)
      ·
        refine ⟨915444569375208026548867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4882371036667776141593957 915444569375208026548867)
        ·
          refine ⟨1373166854062812039823301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915444569375208026548867 1373166854062812039823301)
          ·
            refine ⟨257468785136777257466869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1373166854062812039823301 257468785136777257466869)
            ·
              refine ⟨24137698606572867887519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257468785136777257466869 24137698606572867887519)
              ·
                rfl

theorem cell19_237978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_237978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_237978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_237978 prefixEnd_237978 := by exact prefixLift 237978
  have htrace : WordTrace (prefixWord ++ tailWord_237978) baseStart_237978 baseEnd_237978 := by
    simpa [prefixWord, tailWord_237978, baseEnd_237978] using wordTrace_append hprefix tailTrace_237978
  have hstable : (prefixWord ++ tailWord_237978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237978).length < 2 ^ (prefixWord ++ tailWord_237978).sum := by decide
  have hdescent : baseEnd_237978 < baseStart_237978 := by decide
  rcases family_descends (prefixWord ++ tailWord_237978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238037 : List Nat := [1, 3, 2, 3, 1, 9]
def baseStart_238037 : Nat := 118140960795 + 238037 * 2 ^ 59
def prefixEnd_238037 : Nat := 4983230072969 + 3 ^ 40 * 238037 * 2
def baseEnd_238037 : Nat := 8047894291647105372365

theorem tailTrace_238037 : CollatzResearch.WordTrace tailWord_238037 prefixEnd_238037 8047894291647105372365 := by
  unfold tailWord_238037
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681922638640077328120365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5787948425760051552080243 8681922638640077328120365)
  ·
    refine ⟨3255720989490028998045137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8681922638640077328120365 3255720989490028998045137)
    ·
      refine ⟨2441790742117521748533853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3255720989490028998045137 2441790742117521748533853)
      ·
        refine ⟨915671528294070655700195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2441790742117521748533853 915671528294070655700195)
        ·
          refine ⟨1373507292441105983550293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915671528294070655700195 1373507292441105983550293)
          ·
            refine ⟨8047894291647105372365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1373507292441105983550293 8047894291647105372365)
            ·
              rfl

theorem cell19_238037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_238037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238037 prefixEnd_238037 := by exact prefixLift 238037
  have htrace : WordTrace (prefixWord ++ tailWord_238037) baseStart_238037 baseEnd_238037 := by
    simpa [prefixWord, tailWord_238037, baseEnd_238037] using wordTrace_append hprefix tailTrace_238037
  have hstable : (prefixWord ++ tailWord_238037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238037).length < 2 ^ (prefixWord ++ tailWord_238037).sum := by decide
  have hdescent : baseEnd_238037 < baseStart_238037 := by decide
  rcases family_descends (prefixWord ++ tailWord_238037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238069 : List Nat := [1, 3, 5, 1, 2, 1, 3, 3]
def baseStart_238069 : Nat := 118140960795 + 238069 * 2 ^ 59
def prefixEnd_238069 : Nat := 4983230072969 + 3 ^ 40 * 238069 * 2
def baseEnd_238069 : Nat := 72440785739457355640087

theorem tailTrace_238069 : CollatzResearch.WordTrace tailWord_238069 prefixEnd_238069 72440785739457355640087 := by
  unfold tailWord_238069
  simp only [CollatzResearch.WordTrace]
  refine ⟨8683089774524146793285261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5788726516349431195523507 8683089774524146793285261)
  ·
    refine ⟨3256158665446555047481973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8683089774524146793285261 3256158665446555047481973)
    ·
      refine ⟨305264874885614535701435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3256158665446555047481973 305264874885614535701435)
      ·
        refine ⟨457897312328421803552153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305264874885614535701435 457897312328421803552153)
        ·
          refine ⟨343422984246316352664115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457897312328421803552153 343422984246316352664115)
          ·
            refine ⟨515134476369474528996173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343422984246316352664115 515134476369474528996173)
            ·
              refine ⟨193175428638552948373565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 515134476369474528996173 193175428638552948373565)
              ·
                refine ⟨72440785739457355640087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193175428638552948373565 72440785739457355640087)
                ·
                  rfl

theorem cell19_238069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_238069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238069 prefixEnd_238069 := by exact prefixLift 238069
  have htrace : WordTrace (prefixWord ++ tailWord_238069) baseStart_238069 baseEnd_238069 := by
    simpa [prefixWord, tailWord_238069, baseEnd_238069] using wordTrace_append hprefix tailTrace_238069
  have hstable : (prefixWord ++ tailWord_238069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238069).length < 2 ^ (prefixWord ++ tailWord_238069).sum := by decide
  have hdescent : baseEnd_238069 < baseStart_238069 := by decide
  rcases family_descends (prefixWord ++ tailWord_238069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238113 : List Nat := [1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_238113 : Nat := 118140960795 + 238113 * 2 ^ 59
def prefixEnd_238113 : Nat := 4983230072969 + 3 ^ 40 * 238113 * 2
def baseEnd_238113 : Nat := 72454174272078290662189

theorem tailTrace_238113 : CollatzResearch.WordTrace tailWord_238113 prefixEnd_238113 72454174272078290662189 := by
  unfold tailWord_238113
  simp only [CollatzResearch.WordTrace]
  refine ⟨8684694586364742307886993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5789796390909828205257995 8684694586364742307886993)
  ·
    refine ⟨6513520939773556730915245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8684694586364742307886993 6513520939773556730915245)
    ·
      refine ⟨2442570352415083774093217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6513520939773556730915245 2442570352415083774093217)
      ·
        refine ⟨1831927764311312830569913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2442570352415083774093217 1831927764311312830569913)
        ·
          refine ⟨1373945823233484622927435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831927764311312830569913 1373945823233484622927435)
          ·
            refine ⟨2060918734850226934391153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373945823233484622927435 2060918734850226934391153)
            ·
              refine ⟨1545689051137670200793365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060918734850226934391153 1545689051137670200793365)
              ·
                refine ⟨72454174272078290662189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1545689051137670200793365 72454174272078290662189)
                ·
                  rfl

theorem cell19_238113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_238113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238113 prefixEnd_238113 := by exact prefixLift 238113
  have htrace : WordTrace (prefixWord ++ tailWord_238113) baseStart_238113 baseEnd_238113 := by
    simpa [prefixWord, tailWord_238113, baseEnd_238113] using wordTrace_append hprefix tailTrace_238113
  have hstable : (prefixWord ++ tailWord_238113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238113).length < 2 ^ (prefixWord ++ tailWord_238113).sum := by decide
  have hdescent : baseEnd_238113 < baseStart_238113 := by decide
  rcases family_descends (prefixWord ++ tailWord_238113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238126 : List Nat := [4, 1, 3, 1, 3, 2, 2, 3]
def baseStart_238126 : Nat := 118140960795 + 238126 * 2 ^ 59
def prefixEnd_238126 : Nat := 4983230072969 + 3 ^ 40 * 238126 * 2
def baseEnd_238126 : Nat := 72458129974898112373265

theorem tailTrace_238126 : CollatzResearch.WordTrace tailWord_238126 prefixEnd_238126 72458129974898112373265 := by
  unfold tailWord_238126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085646091914705691013779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5790112490211763685406821 1085646091914705691013779)
  ·
    refine ⟨1628469137872058536520669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1085646091914705691013779 1628469137872058536520669)
    ·
      refine ⟨610675926702021951195251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1628469137872058536520669 610675926702021951195251)
      ·
        refine ⟨916013890053032926792877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610675926702021951195251 916013890053032926792877)
        ·
          refine ⟨343505208769887347547329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 916013890053032926792877 343505208769887347547329)
          ·
            refine ⟨257628906577415510660497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343505208769887347547329 257628906577415510660497)
            ·
              refine ⟨193221679933061632995373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257628906577415510660497 193221679933061632995373)
              ·
                refine ⟨72458129974898112373265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193221679933061632995373 72458129974898112373265)
                ·
                  rfl

theorem cell19_238126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_238126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238126 prefixEnd_238126 := by exact prefixLift 238126
  have htrace : WordTrace (prefixWord ++ tailWord_238126) baseStart_238126 baseEnd_238126 := by
    simpa [prefixWord, tailWord_238126, baseEnd_238126] using wordTrace_append hprefix tailTrace_238126
  have hstable : (prefixWord ++ tailWord_238126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238126).length < 2 ^ (prefixWord ++ tailWord_238126).sum := by decide
  have hdescent : baseEnd_238126 < baseStart_238126 := by decide
  rcases family_descends (prefixWord ++ tailWord_238126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238130 : List Nat := [3, 2, 1, 1, 2, 1, 6, 3]
def baseStart_238130 : Nat := 118140960795 + 238130 * 2 ^ 59
def prefixEnd_238130 : Nat := 4983230072969 + 3 ^ 40 * 238130 * 2
def baseEnd_238130 : Nat := 72459347114227288284365

theorem tailTrace_238130 : CollatzResearch.WordTrace tailWord_238130 prefixEnd_238130 72459347114227288284365 := by
  unfold tailWord_238130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171328656825788552813961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5790209751535436140837229 2171328656825788552813961)
  ·
    refine ⟨1628496492619341414610471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2171328656825788552813961 1628496492619341414610471)
    ·
      refine ⟨2442744738929012121915707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628496492619341414610471 2442744738929012121915707)
      ·
        refine ⟨3664117108393518182873561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442744738929012121915707 3664117108393518182873561)
        ·
          refine ⟨2748087831295138637155171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664117108393518182873561 2748087831295138637155171)
          ·
            refine ⟨4122131746942707955732757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748087831295138637155171 4122131746942707955732757)
            ·
              refine ⟨193224925637939435424973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4122131746942707955732757 193224925637939435424973)
              ·
                refine ⟨72459347114227288284365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193224925637939435424973 72459347114227288284365)
                ·
                  rfl

theorem cell19_238130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_238130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238130 prefixEnd_238130 := by exact prefixLift 238130
  have htrace : WordTrace (prefixWord ++ tailWord_238130) baseStart_238130 baseEnd_238130 := by
    simpa [prefixWord, tailWord_238130, baseEnd_238130] using wordTrace_append hprefix tailTrace_238130
  have hstable : (prefixWord ++ tailWord_238130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238130).length < 2 ^ (prefixWord ++ tailWord_238130).sum := by decide
  have hdescent : baseEnd_238130 < baseStart_238130 := by decide
  rcases family_descends (prefixWord ++ tailWord_238130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238151 : List Nat := [1, 1, 4, 1, 4, 1, 7]
def baseStart_238151 : Nat := 118140960795 + 238151 * 2 ^ 59
def prefixEnd_238151 : Nat := 4983230072969 + 3 ^ 40 * 238151 * 2
def baseEnd_238151 : Nat := 24155245698568487272547

theorem tailTrace_238151 : CollatzResearch.WordTrace tailWord_238151 prefixEnd_238151 24155245698568487272547 := by
  unfold tailWord_238151
  simp only [CollatzResearch.WordTrace]
  refine ⟨8686080560227074797770307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5790720373484716531846871 8686080560227074797770307)
  ·
    refine ⟨13029120840340612196655461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8686080560227074797770307 13029120840340612196655461)
    ·
      refine ⟨2442960157563864786872899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13029120840340612196655461 2442960157563864786872899)
      ·
        refine ⟨3664440236345797180309349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442960157563864786872899 3664440236345797180309349)
        ·
          refine ⟨687082544314836971308003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3664440236345797180309349 687082544314836971308003)
          ·
            refine ⟨1030623816472255456962005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687082544314836971308003 1030623816472255456962005)
            ·
              refine ⟨24155245698568487272547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1030623816472255456962005 24155245698568487272547)
              ·
                rfl

theorem cell19_238151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_238151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238151 prefixEnd_238151 := by exact prefixLift 238151
  have htrace : WordTrace (prefixWord ++ tailWord_238151) baseStart_238151 baseEnd_238151 := by
    simpa [prefixWord, tailWord_238151, baseEnd_238151] using wordTrace_append hprefix tailTrace_238151
  have hstable : (prefixWord ++ tailWord_238151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238151).length < 2 ^ (prefixWord ++ tailWord_238151).sum := by decide
  have hdescent : baseEnd_238151 < baseStart_238151 := by decide
  rcases family_descends (prefixWord ++ tailWord_238151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238244 : List Nat := [2, 3, 1, 2, 2, 1, 5, 3]
def baseStart_238244 : Nat := 118140960795 + 238244 * 2 ^ 59
def prefixEnd_238244 : Nat := 4983230072969 + 3 ^ 40 * 238244 * 2
def baseEnd_238244 : Nat := 72494035585108801750721

theorem tailTrace_238244 : CollatzResearch.WordTrace tailWord_238244 prefixEnd_238244 72494035585108801750721 := by
  unfold tailWord_238244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344736274445075840452893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5792981699260101120603857 4344736274445075840452893)
  ·
    refine ⟨1629276102916903440169835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4344736274445075840452893 1629276102916903440169835)
    ·
      refine ⟨2443914154375355160254753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629276102916903440169835 2443914154375355160254753)
      ·
        refine ⟨1832935615781516370191065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2443914154375355160254753 1832935615781516370191065)
        ·
          refine ⟨1374701711836137277643299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1832935615781516370191065 1374701711836137277643299)
          ·
            refine ⟨2062052567754205916464949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374701711836137277643299 2062052567754205916464949)
            ·
              refine ⟨193317428226956804668589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2062052567754205916464949 193317428226956804668589)
              ·
                refine ⟨72494035585108801750721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193317428226956804668589 72494035585108801750721)
                ·
                  rfl

theorem cell19_238244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_238244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238244 prefixEnd_238244 := by exact prefixLift 238244
  have htrace : WordTrace (prefixWord ++ tailWord_238244) baseStart_238244 baseEnd_238244 := by
    simpa [prefixWord, tailWord_238244, baseEnd_238244] using wordTrace_append hprefix tailTrace_238244
  have hstable : (prefixWord ++ tailWord_238244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238244).length < 2 ^ (prefixWord ++ tailWord_238244).sum := by decide
  have hdescent : baseEnd_238244 < baseStart_238244 := by decide
  rcases family_descends (prefixWord ++ tailWord_238244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238303 : List Nat := [1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_238303 : Nat := 118140960795 + 238303 * 2 ^ 59
def prefixEnd_238303 : Nat := 4983230072969 + 3 ^ 40 * 238303 * 2
def baseEnd_238303 : Nat := 72511988390214146439449

theorem tailTrace_238303 : CollatzResearch.WordTrace tailWord_238303 prefixEnd_238303 72511988390214146439449 := by
  unfold tailWord_238303
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691624455676404757303563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5794416303784269838202375 8691624455676404757303563)
  ·
    refine ⟨13037436683514607135955345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8691624455676404757303563 13037436683514607135955345)
    ·
      refine ⟨9778077512635955351966509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13037436683514607135955345 9778077512635955351966509)
      ·
        refine ⟨3666779067238483256987441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9778077512635955351966509 3666779067238483256987441)
        ·
          refine ⟨2750084300428862442740581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3666779067238483256987441 2750084300428862442740581)
          ·
            refine ⟨515640806330411708013859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2750084300428862442740581 515640806330411708013859)
            ·
              refine ⟨773461209495617562020789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515640806330411708013859 773461209495617562020789)
              ·
                refine ⟨72511988390214146439449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 773461209495617562020789 72511988390214146439449)
                ·
                  rfl

theorem cell19_238303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_238303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238303 prefixEnd_238303 := by exact prefixLift 238303
  have htrace : WordTrace (prefixWord ++ tailWord_238303) baseStart_238303 baseEnd_238303 := by
    simpa [prefixWord, tailWord_238303, baseEnd_238303] using wordTrace_append hprefix tailTrace_238303
  have hstable : (prefixWord ++ tailWord_238303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238303).length < 2 ^ (prefixWord ++ tailWord_238303).sum := by decide
  have hdescent : baseEnd_238303 < baseStart_238303 := by decide
  rcases family_descends (prefixWord ++ tailWord_238303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238322 : List Nat := [3, 2, 1, 3, 1, 2, 7]
def baseStart_238322 : Nat := 118140960795 + 238322 * 2 ^ 59
def prefixEnd_238322 : Nat := 4983230072969 + 3 ^ 40 * 238322 * 2
def baseEnd_238322 : Nat := 24172589934009244005725

theorem tailTrace_238322 : CollatzResearch.WordTrace tailWord_238322 prefixEnd_238322 24172589934009244005725 := by
  unfold tailWord_238322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173079360651892750561305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5794878295071714001496813 2173079360651892750561305)
  ·
    refine ⟨1629809520488919562920979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2173079360651892750561305 1629809520488919562920979)
    ·
      refine ⟨2444714280733379344381469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629809520488919562920979 2444714280733379344381469)
      ·
        refine ⟨916767855275017254143051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2444714280733379344381469 916767855275017254143051)
        ·
          refine ⟨1375151782912525881214577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916767855275017254143051 1375151782912525881214577)
          ·
            refine ⟨1031363837184394410910933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1375151782912525881214577 1031363837184394410910933)
            ·
              refine ⟨24172589934009244005725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1031363837184394410910933 24172589934009244005725)
              ·
                rfl

theorem cell19_238322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_238322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238322 prefixEnd_238322 := by exact prefixLift 238322
  have htrace : WordTrace (prefixWord ++ tailWord_238322) baseStart_238322 baseEnd_238322 := by
    simpa [prefixWord, tailWord_238322, baseEnd_238322] using wordTrace_append hprefix tailTrace_238322
  have hstable : (prefixWord ++ tailWord_238322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238322).length < 2 ^ (prefixWord ++ tailWord_238322).sum := by decide
  have hdescent : baseEnd_238322 < baseStart_238322 := by decide
  rcases family_descends (prefixWord ++ tailWord_238322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238394 : List Nat := [3, 1, 1, 1, 7, 1, 1, 4]
def baseStart_238394 : Nat := 118140960795 + 238394 * 2 ^ 59
def prefixEnd_238394 : Nat := 4983230072969 + 3 ^ 40 * 238394 * 2
def baseEnd_238394 : Nat := 72539678309952898416979

theorem tailTrace_238394 : CollatzResearch.WordTrace tailWord_238394 prefixEnd_238394 72539678309952898416979 := by
  unfold tailWord_238394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173735874586681824716559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5796628998897818199244157 2173735874586681824716559)
  ·
    refine ⟨3260603811880022737074839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2173735874586681824716559 3260603811880022737074839)
    ·
      refine ⟨4890905717820034105612259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3260603811880022737074839 4890905717820034105612259)
      ·
        refine ⟨7336358576730051158418389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890905717820034105612259 7336358576730051158418389)
        ·
          refine ⟨171945904142110574025431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7336358576730051158418389 171945904142110574025431)
          ·
            refine ⟨257918856213165861038147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171945904142110574025431 257918856213165861038147)
            ·
              refine ⟨386878284319748791557221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257918856213165861038147 386878284319748791557221)
              ·
                refine ⟨72539678309952898416979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386878284319748791557221 72539678309952898416979)
                ·
                  rfl

theorem cell19_238394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_238394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238394 prefixEnd_238394 := by exact prefixLift 238394
  have htrace : WordTrace (prefixWord ++ tailWord_238394) baseStart_238394 baseEnd_238394 := by
    simpa [prefixWord, tailWord_238394, baseEnd_238394] using wordTrace_append hprefix tailTrace_238394
  have hstable : (prefixWord ++ tailWord_238394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238394).length < 2 ^ (prefixWord ++ tailWord_238394).sum := by decide
  have hdescent : baseEnd_238394 < baseStart_238394 := by decide
  rcases family_descends (prefixWord ++ tailWord_238394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238419 : List Nat := [1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_238419 : Nat := 118140960795 + 238419 * 2 ^ 59
def prefixEnd_238419 : Nat := 4983230072969 + 3 ^ 40 * 238419 * 2
def baseEnd_238419 : Nat := 72547285430760247861355

theorem tailTrace_238419 : CollatzResearch.WordTrace tailWord_238419 prefixEnd_238419 72547285430760247861355 := by
  unfold tailWord_238419
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695855323256156568526311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5797236882170771045684207 8695855323256156568526311)
  ·
    refine ⟨13043782984884234852789467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8695855323256156568526311 13043782984884234852789467)
    ·
      refine ⟨19565674477326352279184201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13043782984884234852789467 19565674477326352279184201)
      ·
        refine ⟨14674255857994764209388151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19565674477326352279184201 14674255857994764209388151)
        ·
          refine ⟨22011383786992146314082227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14674255857994764209388151 22011383786992146314082227)
          ·
            refine ⟨33017075680488219471123341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22011383786992146314082227 33017075680488219471123341)
            ·
              refine ⟨12381403380183082301671253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33017075680488219471123341 12381403380183082301671253)
              ·
                refine ⟨72547285430760247861355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12381403380183082301671253 72547285430760247861355)
                ·
                  rfl

theorem cell19_238419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_238419 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238419 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238419 prefixEnd_238419 := by exact prefixLift 238419
  have htrace : WordTrace (prefixWord ++ tailWord_238419) baseStart_238419 baseEnd_238419 := by
    simpa [prefixWord, tailWord_238419, baseEnd_238419] using wordTrace_append hprefix tailTrace_238419
  have hstable : (prefixWord ++ tailWord_238419).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238419).length < 2 ^ (prefixWord ++ tailWord_238419).sum := by decide
  have hdescent : baseEnd_238419 < baseStart_238419 := by decide
  rcases family_descends (prefixWord ++ tailWord_238419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238434 : List Nat := [3, 3, 2, 1, 3, 1, 6]
def baseStart_238434 : Nat := 118140960795 + 238434 * 2 ^ 59
def prefixEnd_238434 : Nat := 4983230072969 + 3 ^ 40 * 238434 * 2
def baseEnd_238434 : Nat := 24183949901081552509327

theorem tailTrace_238434 : CollatzResearch.WordTrace tailWord_238434 prefixEnd_238434 24183949901081552509327 := by
  unfold tailWord_238434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174100604550453532580589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5797601612134542753548237 2174100604550453532580589)
  ·
    refine ⟨815287726706420074717721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2174100604550453532580589 815287726706420074717721)
    ·
      refine ⟨611465795029815056038291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 815287726706420074717721 611465795029815056038291)
      ·
        refine ⟨917198692544722584057437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611465795029815056038291 917198692544722584057437)
        ·
          refine ⟨343949509704270969021539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 917198692544722584057437 343949509704270969021539)
          ·
            refine ⟨515924264556406453532309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343949509704270969021539 515924264556406453532309)
            ·
              refine ⟨24183949901081552509327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 515924264556406453532309 24183949901081552509327)
              ·
                rfl

theorem cell19_238434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_238434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238434 prefixEnd_238434 := by exact prefixLift 238434
  have htrace : WordTrace (prefixWord ++ tailWord_238434) baseStart_238434 baseEnd_238434 := by
    simpa [prefixWord, tailWord_238434, baseEnd_238434] using wordTrace_append hprefix tailTrace_238434
  have hstable : (prefixWord ++ tailWord_238434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238434).length < 2 ^ (prefixWord ++ tailWord_238434).sum := by decide
  have hdescent : baseEnd_238434 < baseStart_238434 := by decide
  rcases family_descends (prefixWord ++ tailWord_238434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238436 : List Nat := [2, 3, 1, 1, 4, 2, 6]
def baseStart_238436 : Nat := 118140960795 + 238436 * 2 ^ 59
def prefixEnd_238436 : Nat := 4983230072969 + 3 ^ 40 * 238436 * 2
def baseEnd_238436 : Nat := 24184152757636415161177

theorem tailTrace_238436 : CollatzResearch.WordTrace tailWord_238436 prefixEnd_238436 24184152757636415161177 := by
  unfold tailWord_238436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348237682097284235947581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5797650242796378981263441 4348237682097284235947581)
  ·
    refine ⟨1630589130786481588480343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4348237682097284235947581 1630589130786481588480343)
    ·
      refine ⟨2445883696179722382720515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1630589130786481588480343 2445883696179722382720515)
      ·
        refine ⟨3668825544269583574080773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2445883696179722382720515 3668825544269583574080773)
        ·
          refine ⟨687904789550546920140145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3668825544269583574080773 687904789550546920140145)
          ·
            refine ⟨515928592162910190105109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687904789550546920140145 515928592162910190105109)
            ·
              refine ⟨24184152757636415161177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 515928592162910190105109 24184152757636415161177)
              ·
                rfl

theorem cell19_238436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_238436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238436 prefixEnd_238436 := by exact prefixLift 238436
  have htrace : WordTrace (prefixWord ++ tailWord_238436) baseStart_238436 baseEnd_238436 := by
    simpa [prefixWord, tailWord_238436, baseEnd_238436] using wordTrace_append hprefix tailTrace_238436
  have hstable : (prefixWord ++ tailWord_238436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238436).length < 2 ^ (prefixWord ++ tailWord_238436).sum := by decide
  have hdescent : baseEnd_238436 < baseStart_238436 := by decide
  rcases family_descends (prefixWord ++ tailWord_238436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238466 : List Nat := [3, 4, 2, 2, 1, 2, 2, 3]
def baseStart_238466 : Nat := 118140960795 + 238466 * 2 ^ 59
def prefixEnd_238466 : Nat := 4983230072969 + 3 ^ 40 * 238466 * 2
def baseEnd_238466 : Nat := 72561586817878064816783

theorem tailTrace_238466 : CollatzResearch.WordTrace tailWord_238466 prefixEnd_238466 72561586817878064816783 := by
  unfold tailWord_238466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174392388521470898871813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5798379702723922396991501 2174392388521470898871813)
  ·
    refine ⟨407698572847775793538465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2174392388521470898871813 407698572847775793538465)
    ·
      refine ⟨305773929635831845153849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407698572847775793538465 305773929635831845153849)
      ·
        refine ⟨229330447226873883865387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305773929635831845153849 229330447226873883865387)
        ·
          refine ⟨343995670840310825798081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229330447226873883865387 343995670840310825798081)
          ·
            refine ⟨257996753130233119348561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343995670840310825798081 257996753130233119348561)
            ·
              refine ⟨193497564847674839511421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257996753130233119348561 193497564847674839511421)
              ·
                refine ⟨72561586817878064816783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193497564847674839511421 72561586817878064816783)
                ·
                  rfl

theorem cell19_238466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_238466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238466 prefixEnd_238466 := by exact prefixLift 238466
  have htrace : WordTrace (prefixWord ++ tailWord_238466) baseStart_238466 baseEnd_238466 := by
    simpa [prefixWord, tailWord_238466, baseEnd_238466] using wordTrace_append hprefix tailTrace_238466
  have hstable : (prefixWord ++ tailWord_238466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238466).length < 2 ^ (prefixWord ++ tailWord_238466).sum := by decide
  have hdescent : baseEnd_238466 < baseStart_238466 := by decide
  rcases family_descends (prefixWord ++ tailWord_238466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238472 : List Nat := [2, 1, 3, 3, 2, 1, 4, 3]
def baseStart_238472 : Nat := 118140960795 + 238472 * 2 ^ 59
def prefixEnd_238472 : Nat := 4983230072969 + 3 ^ 40 * 238472 * 2
def baseEnd_238472 : Nat := 72563412526871828683433

theorem tailTrace_238472 : CollatzResearch.WordTrace tailWord_238472 prefixEnd_238472 72563412526871828683433 := by
  unfold tailWord_238472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348894196032073310102835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5798525594709431080137113 4348894196032073310102835)
  ·
    refine ⟨6523341294048109965154253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4348894196032073310102835 6523341294048109965154253)
    ·
      refine ⟨2446252985268041236932845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6523341294048109965154253 2446252985268041236932845)
      ·
        refine ⟨917344869475515463849817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2446252985268041236932845 917344869475515463849817)
        ·
          refine ⟨688008652106636597887363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917344869475515463849817 688008652106636597887363)
          ·
            refine ⟨1032012978159954896831045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688008652106636597887363 1032012978159954896831045)
            ·
              refine ⟨193502433404991543155821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1032012978159954896831045 193502433404991543155821)
              ·
                refine ⟨72563412526871828683433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193502433404991543155821 72563412526871828683433)
                ·
                  rfl

theorem cell19_238472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_238472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238472 prefixEnd_238472 := by exact prefixLift 238472
  have htrace : WordTrace (prefixWord ++ tailWord_238472) baseStart_238472 baseEnd_238472 := by
    simpa [prefixWord, tailWord_238472, baseEnd_238472] using wordTrace_append hprefix tailTrace_238472
  have hstable : (prefixWord ++ tailWord_238472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238472).length < 2 ^ (prefixWord ++ tailWord_238472).sum := by decide
  have hdescent : baseEnd_238472 < baseStart_238472 := by decide
  rcases family_descends (prefixWord ++ tailWord_238472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238552 : List Nat := [2, 1, 2, 2, 2, 10]
def baseStart_238552 : Nat := 118140960795 + 238552 * 2 ^ 59
def prefixEnd_238552 : Nat := 4983230072969 + 3 ^ 40 * 238552 * 2
def baseEnd_238552 : Nat := 8065306145939482989493

theorem tailTrace_238552 : CollatzResearch.WordTrace tailWord_238552 prefixEnd_238552 8065306145939482989493 := by
  unfold tailWord_238552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350353115887160141558955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5800470821182880188745273 4350353115887160141558955)
  ·
    refine ⟨6525529673830740212338433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4350353115887160141558955 6525529673830740212338433)
    ·
      refine ⟨4894147255373055159253825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6525529673830740212338433 4894147255373055159253825)
      ·
        refine ⟨3670610441529791369440369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4894147255373055159253825 3670610441529791369440369)
        ·
          refine ⟨2752957831147343527080277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3670610441529791369440369 2752957831147343527080277)
          ·
            refine ⟨8065306145939482989493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2752957831147343527080277 8065306145939482989493)
            ·
              rfl

theorem cell19_238552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_238552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238552 prefixEnd_238552 := by exact prefixLift 238552
  have htrace : WordTrace (prefixWord ++ tailWord_238552) baseStart_238552 baseEnd_238552 := by
    simpa [prefixWord, tailWord_238552, baseEnd_238552] using wordTrace_append hprefix tailTrace_238552
  have hstable : (prefixWord ++ tailWord_238552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238552).length < 2 ^ (prefixWord ++ tailWord_238552).sum := by decide
  have hdescent : baseEnd_238552 < baseStart_238552 := by decide
  rcases family_descends (prefixWord ++ tailWord_238552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238565 : List Nat := [1, 3, 1, 6, 1, 2, 1, 4]
def baseStart_238565 : Nat := 118140960795 + 238565 * 2 ^ 59
def prefixEnd_238565 : Nat := 4983230072969 + 3 ^ 40 * 238565 * 2
def baseEnd_238565 : Nat := 72591711016275168616513

theorem tailTrace_238565 : CollatzResearch.WordTrace tailWord_238565 prefixEnd_238565 72591711016275168616513 := by
  unfold tailWord_238565
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701180380727223503341149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5800786920484815668894099 8701180380727223503341149)
  ·
    refine ⟨3262942642772708813752931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8701180380727223503341149 3262942642772708813752931)
    ·
      refine ⟨4894413964159063220629397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262942642772708813752931 4894413964159063220629397)
      ·
        refine ⟨229425654569956088467003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4894413964159063220629397 229425654569956088467003)
        ·
          refine ⟨344138481854934132700505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229425654569956088467003 344138481854934132700505)
          ·
            refine ⟨258103861391200599525379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344138481854934132700505 258103861391200599525379)
            ·
              refine ⟨387155792086800899288069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258103861391200599525379 387155792086800899288069)
              ·
                refine ⟨72591711016275168616513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387155792086800899288069 72591711016275168616513)
                ·
                  rfl

theorem cell19_238565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_238565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238565 prefixEnd_238565 := by exact prefixLift 238565
  have htrace : WordTrace (prefixWord ++ tailWord_238565) baseStart_238565 baseEnd_238565 := by
    simpa [prefixWord, tailWord_238565, baseEnd_238565] using wordTrace_append hprefix tailTrace_238565
  have hstable : (prefixWord ++ tailWord_238565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238565).length < 2 ^ (prefixWord ++ tailWord_238565).sum := by decide
  have hdescent : baseEnd_238565 < baseStart_238565 := by decide
  rcases family_descends (prefixWord ++ tailWord_238565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238567 : List Nat := [1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_238567 : Nat := 118140960795 + 238567 * 2 ^ 59
def prefixEnd_238567 : Nat := 4983230072969 + 3 ^ 40 * 238567 * 2
def baseEnd_238567 : Nat := 72592319585939756572063

theorem tailTrace_238567 : CollatzResearch.WordTrace tailWord_238567 prefixEnd_238567 72592319585939756572063 := by
  unfold tailWord_238567
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701253326719977844913955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5800835551146651896609303 8701253326719977844913955)
  ·
    refine ⟨13051879990079966767370933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8701253326719977844913955 13051879990079966767370933)
    ·
      refine ⟨1223613749069996884441025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13051879990079966767370933 1223613749069996884441025)
      ·
        refine ⟨917710311802497663330769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1223613749069996884441025 917710311802497663330769)
        ·
          refine ⟨688282733851873247498077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917710311802497663330769 688282733851873247498077)
          ·
            refine ⟨258106025194452467811779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 688282733851873247498077 258106025194452467811779)
            ·
              refine ⟨387159037791678701717669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258106025194452467811779 387159037791678701717669)
              ·
                refine ⟨72592319585939756572063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387159037791678701717669 72592319585939756572063)
                ·
                  rfl

theorem cell19_238567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_238567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238567 prefixEnd_238567 := by exact prefixLift 238567
  have htrace : WordTrace (prefixWord ++ tailWord_238567) baseStart_238567 baseEnd_238567 := by
    simpa [prefixWord, tailWord_238567, baseEnd_238567] using wordTrace_append hprefix tailTrace_238567
  have hstable : (prefixWord ++ tailWord_238567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238567).length < 2 ^ (prefixWord ++ tailWord_238567).sum := by decide
  have hdescent : baseEnd_238567 < baseStart_238567 := by decide
  rcases family_descends (prefixWord ++ tailWord_238567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238662 : List Nat := [6, 1, 1, 1, 1, 2, 7]
def baseStart_238662 : Nat := 118140960795 + 238662 * 2 ^ 59
def prefixEnd_238662 : Nat := 4983230072969 + 3 ^ 40 * 238662 * 2
def baseEnd_238662 : Nat := 24207075548335894820231

theorem tailTrace_238662 : CollatzResearch.WordTrace tailWord_238662 prefixEnd_238662 24207075548335894820231 := by
  unfold tailWord_238662
  simp only [CollatzResearch.WordTrace]
  refine ⟨272022445667994033425695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5803145507583872713081493 272022445667994033425695)
  ·
    refine ⟨408033668501991050138543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272022445667994033425695 408033668501991050138543)
    ·
      refine ⟨612050502752986575207815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408033668501991050138543 612050502752986575207815)
      ·
        refine ⟨918075754129479862811723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612050502752986575207815 918075754129479862811723)
        ·
          refine ⟨1377113631194219794217585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918075754129479862811723 1377113631194219794217585)
          ·
            refine ⟨1032835223395664845663189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377113631194219794217585 1032835223395664845663189)
            ·
              refine ⟨24207075548335894820231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1032835223395664845663189 24207075548335894820231)
              ·
                rfl

theorem cell19_238662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_238662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238662 prefixEnd_238662 := by exact prefixLift 238662
  have htrace : WordTrace (prefixWord ++ tailWord_238662) baseStart_238662 baseEnd_238662 := by
    simpa [prefixWord, tailWord_238662, baseEnd_238662] using wordTrace_append hprefix tailTrace_238662
  have hstable : (prefixWord ++ tailWord_238662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238662).length < 2 ^ (prefixWord ++ tailWord_238662).sum := by decide
  have hdescent : baseEnd_238662 < baseStart_238662 := by decide
  rcases family_descends (prefixWord ++ tailWord_238662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238666 : List Nat := [3, 1, 2, 1, 1, 2, 9]
def baseStart_238666 : Nat := 118140960795 + 238666 * 2 ^ 59
def prefixEnd_238666 : Nat := 4983230072969 + 3 ^ 40 * 238666 * 2
def baseEnd_238666 : Nat := 24207481261445620123931

theorem tailTrace_238666 : CollatzResearch.WordTrace tailWord_238666 prefixEnd_238666 24207481261445620123931 := by
  unfold tailWord_238666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176216038340329438191963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5803242768907545168511901 2176216038340329438191963)
  ·
    refine ⟨3264324057510494157287945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176216038340329438191963 3264324057510494157287945)
    ·
      refine ⟨2448243043132870617965959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3264324057510494157287945 2448243043132870617965959)
      ·
        refine ⟨3672364564699305926948939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448243043132870617965959 3672364564699305926948939)
        ·
          refine ⟨5508546847048958890423409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672364564699305926948939 5508546847048958890423409)
          ·
            refine ⟨4131410135286719167817557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508546847048958890423409 4131410135286719167817557)
            ·
              refine ⟨24207481261445620123931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4131410135286719167817557 24207481261445620123931)
              ·
                rfl

theorem cell19_238666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_238666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238666 prefixEnd_238666 := by exact prefixLift 238666
  have htrace : WordTrace (prefixWord ++ tailWord_238666) baseStart_238666 baseEnd_238666 := by
    simpa [prefixWord, tailWord_238666, baseEnd_238666] using wordTrace_append hprefix tailTrace_238666
  have hstable : (prefixWord ++ tailWord_238666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238666).length < 2 ^ (prefixWord ++ tailWord_238666).sum := by decide
  have hdescent : baseEnd_238666 < baseStart_238666 := by decide
  rcases family_descends (prefixWord ++ tailWord_238666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238702 : List Nat := [4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_238702 : Nat := 118140960795 + 238702 * 2 ^ 59
def prefixEnd_238702 : Nat := 4983230072969 + 3 ^ 40 * 238702 * 2
def baseEnd_238702 : Nat := 72633398038299443571695

theorem tailTrace_238702 : CollatzResearch.WordTrace tailWord_238702 prefixEnd_238702 72633398038299443571695 := by
  unfold tailWord_238702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088272147653861987634795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5804118120820597267385573 1088272147653861987634795)
  ·
    refine ⟨1632408221480792981452193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1088272147653861987634795 1632408221480792981452193)
    ·
      refine ⟨1224306166110594736089145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1632408221480792981452193 1224306166110594736089145)
      ·
        refine ⟨918229624582946052066859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1224306166110594736089145 918229624582946052066859)
        ·
          refine ⟨1377344436874419078100289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918229624582946052066859 1377344436874419078100289)
          ·
            refine ⟨1033008327655814308575217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377344436874419078100289 1033008327655814308575217)
            ·
              refine ⟨774756245741860731431413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033008327655814308575217 774756245741860731431413)
              ·
                refine ⟨72633398038299443571695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 774756245741860731431413 72633398038299443571695)
                ·
                  rfl

theorem cell19_238702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_238702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238702 prefixEnd_238702 := by exact prefixLift 238702
  have htrace : WordTrace (prefixWord ++ tailWord_238702) baseStart_238702 baseEnd_238702 := by
    simpa [prefixWord, tailWord_238702, baseEnd_238702] using wordTrace_append hprefix tailTrace_238702
  have hstable : (prefixWord ++ tailWord_238702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238702).length < 2 ^ (prefixWord ++ tailWord_238702).sum := by decide
  have hdescent : baseEnd_238702 < baseStart_238702 := by decide
  rcases family_descends (prefixWord ++ tailWord_238702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238704 : List Nat := [2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_238704 : Nat := 118140960795 + 238704 * 2 ^ 59
def prefixEnd_238704 : Nat := 4983230072969 + 3 ^ 40 * 238704 * 2
def baseEnd_238704 : Nat := 72634006607964031527245

theorem tailTrace_238704 : CollatzResearch.WordTrace tailWord_238704 prefixEnd_238704 72634006607964031527245 := by
  unfold tailWord_238704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353125063611825121325583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5804166751482433495100777 4353125063611825121325583)
  ·
    refine ⟨6529687595417737681988375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4353125063611825121325583 6529687595417737681988375)
    ·
      refine ⟨9794531393126606522982563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6529687595417737681988375 9794531393126606522982563)
      ·
        refine ⟨14691797089689909784473845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794531393126606522982563 14691797089689909784473845)
        ·
          refine ⟨1377355977158429042294423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14691797089689909784473845 1377355977158429042294423)
          ·
            refine ⟨2066033965737643563441635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377355977158429042294423 2066033965737643563441635)
            ·
              refine ⟨3099050948606465345162453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066033965737643563441635 3099050948606465345162453)
              ·
                refine ⟨72634006607964031527245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3099050948606465345162453 72634006607964031527245)
                ·
                  rfl

theorem cell19_238704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_238704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238704 prefixEnd_238704 := by exact prefixLift 238704
  have htrace : WordTrace (prefixWord ++ tailWord_238704) baseStart_238704 baseEnd_238704 := by
    simpa [prefixWord, tailWord_238704, baseEnd_238704] using wordTrace_append hprefix tailTrace_238704
  have hstable : (prefixWord ++ tailWord_238704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238704).length < 2 ^ (prefixWord ++ tailWord_238704).sum := by decide
  have hdescent : baseEnd_238704 < baseStart_238704 := by decide
  rcases family_descends (prefixWord ++ tailWord_238704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238738 : List Nat := [3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_238738 : Nat := 118140960795 + 238738 * 2 ^ 59
def prefixEnd_238738 : Nat := 4983230072969 + 3 ^ 40 * 238738 * 2
def baseEnd_238738 : Nat := 72644352292262026771597

theorem tailTrace_238738 : CollatzResearch.WordTrace tailWord_238738 prefixEnd_238738 72644352292262026771597 := by
  unfold tailWord_238738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176872552275118512347217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5804993472733649366259245 2176872552275118512347217)
  ·
    refine ⟨1632654414206338884260413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2176872552275118512347217 1632654414206338884260413)
    ·
      refine ⟨612245405327377081597655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1632654414206338884260413 612245405327377081597655)
      ·
        refine ⟨918368107991065622396483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612245405327377081597655 918368107991065622396483)
        ·
          refine ⟨1377552161986598433594725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918368107991065622396483 1377552161986598433594725)
          ·
            refine ⟨258291030372487206299011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1377552161986598433594725 258291030372487206299011)
            ·
              refine ⟨387436545558730809448517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258291030372487206299011 387436545558730809448517)
              ·
                refine ⟨72644352292262026771597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387436545558730809448517 72644352292262026771597)
                ·
                  rfl

theorem cell19_238738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_238738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238738 prefixEnd_238738 := by exact prefixLift 238738
  have htrace : WordTrace (prefixWord ++ tailWord_238738) baseStart_238738 baseEnd_238738 := by
    simpa [prefixWord, tailWord_238738, baseEnd_238738] using wordTrace_append hprefix tailTrace_238738
  have hstable : (prefixWord ++ tailWord_238738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238738).length < 2 ^ (prefixWord ++ tailWord_238738).sum := by decide
  have hdescent : baseEnd_238738 < baseStart_238738 := by decide
  rcases family_descends (prefixWord ++ tailWord_238738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238774 : List Nat := [5, 1, 3, 2, 1, 1, 6]
def baseStart_238774 : Nat := 118140960795 + 238774 * 2 ^ 59
def prefixEnd_238774 : Nat := 4983230072969 + 3 ^ 40 * 238774 * 2
def baseEnd_238774 : Nat := 24218435515408203323833

theorem tailTrace_238774 : CollatzResearch.WordTrace tailWord_238774 prefixEnd_238774 24218435515408203323833 := by
  unfold tailWord_238774
  simp only [CollatzResearch.WordTrace]
  refine ⟨544300202310628262356211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5805868824646701465132917 544300202310628262356211)
  ·
    refine ⟨816450303465942393534317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 544300202310628262356211 816450303465942393534317)
    ·
      refine ⟨306168863799728397575369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 816450303465942393534317 306168863799728397575369)
      ·
        refine ⟨229626647849796298181527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306168863799728397575369 229626647849796298181527)
        ·
          refine ⟨344439971774694447272291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229626647849796298181527 344439971774694447272291)
          ·
            refine ⟨516659957662041670908437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344439971774694447272291 516659957662041670908437)
            ·
              refine ⟨24218435515408203323833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 516659957662041670908437 24218435515408203323833)
              ·
                rfl

theorem cell19_238774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_238774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238774 prefixEnd_238774 := by exact prefixLift 238774
  have htrace : WordTrace (prefixWord ++ tailWord_238774) baseStart_238774 baseEnd_238774 := by
    simpa [prefixWord, tailWord_238774, baseEnd_238774] using wordTrace_append hprefix tailTrace_238774
  have hstable : (prefixWord ++ tailWord_238774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238774).length < 2 ^ (prefixWord ++ tailWord_238774).sum := by decide
  have hdescent : baseEnd_238774 < baseStart_238774 := by decide
  rcases family_descends (prefixWord ++ tailWord_238774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238816 : List Nat := [2, 1, 1, 3, 1, 4, 4, 3]
def baseStart_238816 : Nat := 118140960795 + 238816 * 2 ^ 59
def prefixEnd_238816 : Nat := 4983230072969 + 3 ^ 40 * 238816 * 2
def baseEnd_238816 : Nat := 72668086509180957038051

theorem tailTrace_238816 : CollatzResearch.WordTrace tailWord_238816 prefixEnd_238816 72668086509180957038051 := by
  unfold tailWord_238816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355167551408946685364151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5806890068545262247152201 4355167551408946685364151)
  ·
    refine ⟨6532751327113420028046227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4355167551408946685364151 6532751327113420028046227)
    ·
      refine ⟨9799126990670130042069341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532751327113420028046227 9799126990670130042069341)
      ·
        refine ⟨3674672621501298765776003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9799126990670130042069341 3674672621501298765776003)
        ·
          refine ⟨5512008932251948148664005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674672621501298765776003 5512008932251948148664005)
          ·
            refine ⟨1033501674797240277874501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5512008932251948148664005 1033501674797240277874501)
            ·
              refine ⟨193781564024482552101469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1033501674797240277874501 193781564024482552101469)
              ·
                refine ⟨72668086509180957038051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193781564024482552101469 72668086509180957038051)
                ·
                  rfl

theorem cell19_238816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_238816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238816 prefixEnd_238816 := by exact prefixLift 238816
  have htrace : WordTrace (prefixWord ++ tailWord_238816) baseStart_238816 baseEnd_238816 := by
    simpa [prefixWord, tailWord_238816, baseEnd_238816] using wordTrace_append hprefix tailTrace_238816
  have hstable : (prefixWord ++ tailWord_238816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238816).length < 2 ^ (prefixWord ++ tailWord_238816).sum := by decide
  have hdescent : baseEnd_238816 < baseStart_238816 := by decide
  rcases family_descends (prefixWord ++ tailWord_238816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238894 : List Nat := [4, 1, 3, 11]
def baseStart_238894 : Nat := 118140960795 + 238894 * 2 ^ 59
def prefixEnd_238894 : Nat := 4983230072969 + 3 ^ 40 * 238894 * 2
def baseEnd_238894 : Nat := 897429885507406016105

theorem tailTrace_238894 : CollatzResearch.WordTrace tailWord_238894 prefixEnd_238894 897429885507406016105 := by
  unfold tailWord_238894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089147499566914086508467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5808786664356875128045157 1089147499566914086508467)
  ·
    refine ⟨1633721249350371129762701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089147499566914086508467 1633721249350371129762701)
    ·
      refine ⟨612645468506389173661013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1633721249350371129762701 612645468506389173661013)
      ·
        refine ⟨897429885507406016105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 612645468506389173661013 897429885507406016105)
        ·
          rfl

theorem cell19_238894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 11].length) (baseStart_238894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238894 prefixEnd_238894 := by exact prefixLift 238894
  have htrace : WordTrace (prefixWord ++ tailWord_238894) baseStart_238894 baseEnd_238894 := by
    simpa [prefixWord, tailWord_238894, baseEnd_238894] using wordTrace_append hprefix tailTrace_238894
  have hstable : (prefixWord ++ tailWord_238894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238894).length < 2 ^ (prefixWord ++ tailWord_238894).sum := by decide
  have hdescent : baseEnd_238894 < baseStart_238894 := by decide
  rcases family_descends (prefixWord ++ tailWord_238894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238911 : List Nat := [1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_238911 : Nat := 118140960795 + 238911 * 2 ^ 59
def prefixEnd_238911 : Nat := 4983230072969 + 3 ^ 40 * 238911 * 2
def baseEnd_238911 : Nat := 72696993568248884926681

theorem tailTrace_238911 : CollatzResearch.WordTrace tailWord_238911 prefixEnd_238911 72696993568248884926681 := by
  unfold tailWord_238911
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713800037473724595436587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5809200024982483063624391 8713800037473724595436587)
  ·
    refine ⟨13070700056210586893154881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8713800037473724595436587 13070700056210586893154881)
    ·
      refine ⟨9803025042157940169866161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13070700056210586893154881 9803025042157940169866161)
      ·
        refine ⟨7352268781618455127399621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9803025042157940169866161 7352268781618455127399621)
        ·
          refine ⟨1378550396553460336387429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7352268781618455127399621 1378550396553460336387429)
          ·
            refine ⟨258478199353773813072643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1378550396553460336387429 258478199353773813072643)
            ·
              refine ⟨387717299030660719608965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258478199353773813072643 387717299030660719608965)
              ·
                refine ⟨72696993568248884926681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387717299030660719608965 72696993568248884926681)
                ·
                  rfl

theorem cell19_238911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_238911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238911 prefixEnd_238911 := by exact prefixLift 238911
  have htrace : WordTrace (prefixWord ++ tailWord_238911) baseStart_238911 baseEnd_238911 := by
    simpa [prefixWord, tailWord_238911, baseEnd_238911] using wordTrace_append hprefix tailTrace_238911
  have hstable : (prefixWord ++ tailWord_238911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238911).length < 2 ^ (prefixWord ++ tailWord_238911).sum := by decide
  have hdescent : baseEnd_238911 < baseStart_238911 := by decide
  rcases family_descends (prefixWord ++ tailWord_238911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238985 : List Nat := [1, 2, 1, 1, 7, 2, 2, 3]
def baseStart_238985 : Nat := 118140960795 + 238985 * 2 ^ 59
def prefixEnd_238985 : Nat := 4983230072969 + 3 ^ 40 * 238985 * 2
def baseEnd_238985 : Nat := 72719510645838639282035

theorem tailTrace_238985 : CollatzResearch.WordTrace tailWord_238985 prefixEnd_238985 72719510645838639282035 := by
  unfold tailWord_238985
  simp only [CollatzResearch.WordTrace]
  refine ⟨8716499039205635233630409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5810999359470423489086939 8716499039205635233630409)
  ·
    refine ⟨6537374279404226425222807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8716499039205635233630409 6537374279404226425222807)
    ·
      refine ⟨9806061419106339637834211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6537374279404226425222807 9806061419106339637834211)
      ·
        refine ⟨14709092128659509456751317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9806061419106339637834211 14709092128659509456751317)
        ·
          refine ⟨344744346765457252892609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14709092128659509456751317 344744346765457252892609)
          ·
            refine ⟨258558260074092939669457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344744346765457252892609 258558260074092939669457)
            ·
              refine ⟨193918695055569704752093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258558260074092939669457 193918695055569704752093)
              ·
                refine ⟨72719510645838639282035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193918695055569704752093 72719510645838639282035)
                ·
                  rfl

theorem cell19_238985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_238985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_238985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_238985 prefixEnd_238985 := by exact prefixLift 238985
  have htrace : WordTrace (prefixWord ++ tailWord_238985) baseStart_238985 baseEnd_238985 := by
    simpa [prefixWord, tailWord_238985, baseEnd_238985] using wordTrace_append hprefix tailTrace_238985
  have hstable : (prefixWord ++ tailWord_238985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238985).length < 2 ^ (prefixWord ++ tailWord_238985).sum := by decide
  have hdescent : baseEnd_238985 < baseStart_238985 := by decide
  rcases family_descends (prefixWord ++ tailWord_238985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239004 : List Nat := [2, 2, 3, 4, 1, 2, 5]
def baseStart_239004 : Nat := 118140960795 + 239004 * 2 ^ 59
def prefixEnd_239004 : Nat := 4983230072969 + 3 ^ 40 * 239004 * 2
def baseEnd_239004 : Nat := 24241764019217408286587

theorem tailTrace_239004 : CollatzResearch.WordTrace tailWord_239004 prefixEnd_239004 24241764019217408286587 := by
  unfold tailWord_239004
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358596013068400739286033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5811461350757867652381377 4358596013068400739286033)
  ·
    refine ⟨3268947009801300554464525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4358596013068400739286033 3268947009801300554464525)
    ·
      refine ⟨1225855128675487707924197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3268947009801300554464525 1225855128675487707924197)
      ·
        refine ⟨229847836626653945235787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1225855128675487707924197 229847836626653945235787)
        ·
          refine ⟨344771754939980917853681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229847836626653945235787 344771754939980917853681)
          ·
            refine ⟨258578816204985688390261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344771754939980917853681 258578816204985688390261)
            ·
              refine ⟨24241764019217408286587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258578816204985688390261 24241764019217408286587)
              ·
                rfl

theorem cell19_239004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_239004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239004 prefixEnd_239004 := by exact prefixLift 239004
  have htrace : WordTrace (prefixWord ++ tailWord_239004) baseStart_239004 baseEnd_239004 := by
    simpa [prefixWord, tailWord_239004, baseEnd_239004] using wordTrace_append hprefix tailTrace_239004
  have hstable : (prefixWord ++ tailWord_239004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239004).length < 2 ^ (prefixWord ++ tailWord_239004).sum := by decide
  have hdescent : baseEnd_239004 < baseStart_239004 := by decide
  rcases family_descends (prefixWord ++ tailWord_239004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239044 : List Nat := [2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_239044 : Nat := 118140960795 + 239044 * 2 ^ 59
def prefixEnd_239044 : Nat := 4983230072969 + 3 ^ 40 * 239044 * 2
def baseEnd_239044 : Nat := 72737463450943983970763

theorem tailTrace_239044 : CollatzResearch.WordTrace tailWord_239044 prefixEnd_239044 72737463450943983970763 := by
  unfold tailWord_239044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4359325472995944155014093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5812433963994592206685457 4359325472995944155014093)
  ·
    refine ⟨1634747052373479058130285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4359325472995944155014093 1634747052373479058130285)
    ·
      refine ⟨613030144640054646798857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1634747052373479058130285 613030144640054646798857)
      ·
        refine ⟨459772608480040985099143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613030144640054646798857 459772608480040985099143)
        ·
          refine ⟨689658912720061477648715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459772608480040985099143 689658912720061477648715)
          ·
            refine ⟨1034488369080092216473073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689658912720061477648715 1034488369080092216473073)
            ·
              refine ⟨775866276810069162354805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034488369080092216473073 775866276810069162354805)
              ·
                refine ⟨72737463450943983970763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 775866276810069162354805 72737463450943983970763)
                ·
                  rfl

theorem cell19_239044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_239044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239044 prefixEnd_239044 := by exact prefixLift 239044
  have htrace : WordTrace (prefixWord ++ tailWord_239044) baseStart_239044 baseEnd_239044 := by
    simpa [prefixWord, tailWord_239044, baseEnd_239044] using wordTrace_append hprefix tailTrace_239044
  have hstable : (prefixWord ++ tailWord_239044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239044).length < 2 ^ (prefixWord ++ tailWord_239044).sum := by decide
  have hdescent : baseEnd_239044 < baseStart_239044 := by decide
  rcases family_descends (prefixWord ++ tailWord_239044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239101 : List Nat := [1, 4, 1, 1, 1, 5, 3, 3]
def baseStart_239101 : Nat := 118140960795 + 239101 * 2 ^ 59
def prefixEnd_239101 : Nat := 4983230072969 + 3 ^ 40 * 239101 * 2
def baseEnd_239101 : Nat := 72754807686384740703941

theorem tailTrace_239101 : CollatzResearch.WordTrace tailWord_239101 prefixEnd_239101 72754807686384740703941 := by
  unfold tailWord_239101
  simp only [CollatzResearch.WordTrace]
  refine ⟨8720729906785387044853157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5813819937856924696568771 8720729906785387044853157)
  ·
    refine ⟨1635136857522260070909967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8720729906785387044853157 1635136857522260070909967)
    ·
      refine ⟨2452705286283390106364951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635136857522260070909967 2452705286283390106364951)
      ·
        refine ⟨3679057929425085159547427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452705286283390106364951 3679057929425085159547427)
        ·
          refine ⟨5518586894137627739321141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679057929425085159547427 5518586894137627739321141)
          ·
            refine ⟨517367521325402600561357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5518586894137627739321141 517367521325402600561357)
            ·
              refine ⟨194012820497025975210509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517367521325402600561357 194012820497025975210509)
              ·
                refine ⟨72754807686384740703941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194012820497025975210509 72754807686384740703941)
                ·
                  rfl

theorem cell19_239101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_239101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239101 prefixEnd_239101 := by exact prefixLift 239101
  have htrace : WordTrace (prefixWord ++ tailWord_239101) baseStart_239101 baseEnd_239101 := by
    simpa [prefixWord, tailWord_239101, baseEnd_239101] using wordTrace_append hprefix tailTrace_239101
  have hstable : (prefixWord ++ tailWord_239101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239101).length < 2 ^ (prefixWord ++ tailWord_239101).sum := by decide
  have hdescent : baseEnd_239101 < baseStart_239101 := by decide
  rcases family_descends (prefixWord ++ tailWord_239101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239160 : List Nat := [2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_239160 : Nat := 118140960795 + 239160 * 2 ^ 59
def prefixEnd_239160 : Nat := 4983230072969 + 3 ^ 40 * 239160 * 2
def baseEnd_239160 : Nat := 72772760491490085392669

theorem tailTrace_239160 : CollatzResearch.WordTrace tailWord_239160 prefixEnd_239160 72772760491490085392669 := by
  unfold tailWord_239160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361440906785820060625467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5815254542381093414167289 4361440906785820060625467)
  ·
    refine ⟨6542161360178730090938201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361440906785820060625467 6542161360178730090938201)
    ·
      refine ⟨4906621020134047568203651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6542161360178730090938201 4906621020134047568203651)
      ·
        refine ⟨7359931530201071352305477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906621020134047568203651 7359931530201071352305477)
        ·
          refine ⟨1379987161912700878557277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7359931530201071352305477 1379987161912700878557277)
          ·
            refine ⟨517495185717262829458979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1379987161912700878557277 517495185717262829458979)
            ·
              refine ⟨776242778575894244188469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517495185717262829458979 776242778575894244188469)
              ·
                refine ⟨72772760491490085392669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 776242778575894244188469 72772760491490085392669)
                ·
                  rfl

theorem cell19_239160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_239160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239160 prefixEnd_239160 := by exact prefixLift 239160
  have htrace : WordTrace (prefixWord ++ tailWord_239160) baseStart_239160 baseEnd_239160 := by
    simpa [prefixWord, tailWord_239160, baseEnd_239160] using wordTrace_append hprefix tailTrace_239160
  have hstable : (prefixWord ++ tailWord_239160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239160).length < 2 ^ (prefixWord ++ tailWord_239160).sum := by decide
  have hdescent : baseEnd_239160 < baseStart_239160 := by decide
  rcases family_descends (prefixWord ++ tailWord_239160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239196 : List Nat := [2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_239196 : Nat := 118140960795 + 239196 * 2 ^ 59
def prefixEnd_239196 : Nat := 4983230072969 + 3 ^ 40 * 239196 * 2
def baseEnd_239196 : Nat := 72783714745452668592571

theorem tailTrace_239196 : CollatzResearch.WordTrace tailWord_239196 prefixEnd_239196 72783714745452668592571 := by
  unfold tailWord_239196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362097420720609134780721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5816129894294145513040961 4362097420720609134780721)
  ·
    refine ⟨3271573065540456851085541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4362097420720609134780721 3271573065540456851085541)
    ·
      refine ⟨613419949788835659578539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3271573065540456851085541 613419949788835659578539)
      ·
        refine ⟨920129924683253489367809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613419949788835659578539 920129924683253489367809)
        ·
          refine ⟨690097443512440117025857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920129924683253489367809 690097443512440117025857)
          ·
            refine ⟨517573082634330087769393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690097443512440117025857 517573082634330087769393)
            ·
              refine ⟨388179811975747565827045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517573082634330087769393 388179811975747565827045)
              ·
                refine ⟨72783714745452668592571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388179811975747565827045 72783714745452668592571)
                ·
                  rfl

theorem cell19_239196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_239196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239196 prefixEnd_239196 := by exact prefixLift 239196
  have htrace : WordTrace (prefixWord ++ tailWord_239196) baseStart_239196 baseEnd_239196 := by
    simpa [prefixWord, tailWord_239196, baseEnd_239196] using wordTrace_append hprefix tailTrace_239196
  have hstable : (prefixWord ++ tailWord_239196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239196).length < 2 ^ (prefixWord ++ tailWord_239196).sum := by decide
  have hdescent : baseEnd_239196 < baseStart_239196 := by decide
  rcases family_descends (prefixWord ++ tailWord_239196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239234 : List Nat := [3, 4, 3, 9]
def baseStart_239234 : Nat := 118140960795 + 239234 * 2 ^ 59
def prefixEnd_239234 : Nat := 4983230072969 + 3 ^ 40 * 239234 * 2
def baseEnd_239234 : Nat := 898707130482467157383

theorem tailTrace_239234 : CollatzResearch.WordTrace tailWord_239234 prefixEnd_239234 898707130482467157383 := by
  unfold tailWord_239234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181395203825887689861189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5817053876869033839629837 2181395203825887689861189)
  ·
    refine ⟨409011600717353941848973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2181395203825887689861189 409011600717353941848973)
    ·
      refine ⟨153379350269007728193365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409011600717353941848973 153379350269007728193365)
      ·
        refine ⟨898707130482467157383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 153379350269007728193365 898707130482467157383)
        ·
          rfl

theorem cell19_239234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 9].length) (baseStart_239234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239234 prefixEnd_239234 := by exact prefixLift 239234
  have htrace : WordTrace (prefixWord ++ tailWord_239234) baseStart_239234 baseEnd_239234 := by
    simpa [prefixWord, tailWord_239234, baseEnd_239234] using wordTrace_append hprefix tailTrace_239234
  have hstable : (prefixWord ++ tailWord_239234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239234).length < 2 ^ (prefixWord ++ tailWord_239234).sum := by decide
  have hdescent : baseEnd_239234 < baseStart_239234 := by decide
  rcases family_descends (prefixWord ++ tailWord_239234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239236 : List Nat := [2, 3, 2, 1, 4, 7]
def baseStart_239236 : Nat := 118140960795 + 239236 * 2 ^ 59
def prefixEnd_239236 : Nat := 4983230072969 + 3 ^ 40 * 239236 * 2
def baseEnd_239236 : Nat := 8088431793193825300397

theorem tailTrace_239236 : CollatzResearch.WordTrace tailWord_239236 prefixEnd_239236 8088431793193825300397 := by
  unfold tailWord_239236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362826880648152550508781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5817102507530870067345041 4362826880648152550508781)
  ·
    refine ⟨1636060080243057206440793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4362826880648152550508781 1636060080243057206440793)
    ·
      refine ⟨1227045060182292904830595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1636060080243057206440793 1227045060182292904830595)
      ·
        refine ⟨1840567590273439357245893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227045060182292904830595 1840567590273439357245893)
        ·
          refine ⟨345106423176269879483605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1840567590273439357245893 345106423176269879483605)
          ·
            refine ⟨8088431793193825300397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 345106423176269879483605 8088431793193825300397)
            ·
              rfl

theorem cell19_239236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_239236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239236 prefixEnd_239236 := by exact prefixLift 239236
  have htrace : WordTrace (prefixWord ++ tailWord_239236) baseStart_239236 baseEnd_239236 := by
    simpa [prefixWord, tailWord_239236, baseEnd_239236] using wordTrace_append hprefix tailTrace_239236
  have hstable : (prefixWord ++ tailWord_239236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239236).length < 2 ^ (prefixWord ++ tailWord_239236).sum := by decide
  have hdescent : baseEnd_239236 < baseStart_239236 := by decide
  rcases family_descends (prefixWord ++ tailWord_239236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239255 : List Nat := [1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_239255 : Nat := 118140960795 + 239255 * 2 ^ 59
def prefixEnd_239255 : Nat := 4983230072969 + 3 ^ 40 * 239255 * 2
def baseEnd_239255 : Nat := 72801667550558013281299

theorem tailTrace_239255 : CollatzResearch.WordTrace tailWord_239255 prefixEnd_239255 72801667550558013281299 := by
  unfold tailWord_239255
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726346748227471345959219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5817564498818314230639479 8726346748227471345959219)
  ·
    refine ⟨13089520122341207018938829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8726346748227471345959219 13089520122341207018938829)
    ·
      refine ⟨4908570045877952632102061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13089520122341207018938829 4908570045877952632102061)
      ·
        refine ⟨1840713767204232237038273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4908570045877952632102061 1840713767204232237038273)
        ·
          refine ⟨1380535325403174177778705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840713767204232237038273 1380535325403174177778705)
          ·
            refine ⟨1035401494052380633334029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380535325403174177778705 1035401494052380633334029)
            ·
              refine ⟨388275560269642737500261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1035401494052380633334029 388275560269642737500261)
              ·
                refine ⟨72801667550558013281299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388275560269642737500261 72801667550558013281299)
                ·
                  rfl

theorem cell19_239255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_239255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239255 prefixEnd_239255 := by exact prefixLift 239255
  have htrace : WordTrace (prefixWord ++ tailWord_239255) baseStart_239255 baseEnd_239255 := by
    simpa [prefixWord, tailWord_239255, baseEnd_239255] using wordTrace_append hprefix tailTrace_239255
  have hstable : (prefixWord ++ tailWord_239255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239255).length < 2 ^ (prefixWord ++ tailWord_239255).sum := by decide
  have hdescent : baseEnd_239255 < baseStart_239255 := by decide
  rcases family_descends (prefixWord ++ tailWord_239255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239257 : List Nat := [1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_239257 : Nat := 118140960795 + 239257 * 2 ^ 59
def prefixEnd_239257 : Nat := 4983230072969 + 3 ^ 40 * 239257 * 2
def baseEnd_239257 : Nat := 72802276120222601236849

theorem tailTrace_239257 : CollatzResearch.WordTrace tailWord_239257 prefixEnd_239257 72802276120222601236849 := by
  unfold tailWord_239257
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726419694220225687532025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5817613129480150458354683 8726419694220225687532025)
  ·
    refine ⟨6544814770665169265649019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8726419694220225687532025 6544814770665169265649019)
    ·
      refine ⟨9817222155997753898473529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6544814770665169265649019 9817222155997753898473529)
      ·
        refine ⟨7362916616998315423855147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9817222155997753898473529 7362916616998315423855147)
        ·
          refine ⟨11044374925497473135782721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362916616998315423855147 11044374925497473135782721)
          ·
            refine ⟨8283281194123104851837041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11044374925497473135782721 8283281194123104851837041)
            ·
              refine ⟨6212460895592328638877781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8283281194123104851837041 6212460895592328638877781)
              ·
                refine ⟨72802276120222601236849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6212460895592328638877781 72802276120222601236849)
                ·
                  rfl

theorem cell19_239257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_239257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239257 prefixEnd_239257 := by exact prefixLift 239257
  have htrace : WordTrace (prefixWord ++ tailWord_239257) baseStart_239257 baseEnd_239257 := by
    simpa [prefixWord, tailWord_239257, baseEnd_239257] using wordTrace_append hprefix tailTrace_239257
  have hstable : (prefixWord ++ tailWord_239257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239257).length < 2 ^ (prefixWord ++ tailWord_239257).sum := by decide
  have hdescent : baseEnd_239257 < baseStart_239257 := by decide
  rcases family_descends (prefixWord ++ tailWord_239257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239295 : List Nat := [1, 1, 2, 2, 2, 3, 8]
def baseStart_239295 : Nat := 118140960795 + 239295 * 2 ^ 59
def prefixEnd_239295 : Nat := 4983230072969 + 3 ^ 40 * 239295 * 2
def baseEnd_239295 : Nat := 24271279647949924130767

theorem tailTrace_239295 : CollatzResearch.WordTrace tailWord_239295 prefixEnd_239295 24271279647949924130767 := by
  unfold tailWord_239295
  simp only [CollatzResearch.WordTrace]
  refine ⟨8727805668082558177415339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5818537112055038784943559 8727805668082558177415339)
  ·
    refine ⟨13091708502123837266123009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8727805668082558177415339 13091708502123837266123009)
    ·
      refine ⟨9818781376592877949592257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13091708502123837266123009 9818781376592877949592257)
      ·
        refine ⟨7364086032444658462194193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9818781376592877949592257 7364086032444658462194193)
        ·
          refine ⟨5523064524333493846645645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7364086032444658462194193 5523064524333493846645645)
          ·
            refine ⟨2071149196625060192492117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5523064524333493846645645 2071149196625060192492117)
            ·
              refine ⟨24271279647949924130767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2071149196625060192492117 24271279647949924130767)
              ·
                rfl

theorem cell19_239295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_239295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239295 prefixEnd_239295 := by exact prefixLift 239295
  have htrace : WordTrace (prefixWord ++ tailWord_239295) baseStart_239295 baseEnd_239295 := by
    simpa [prefixWord, tailWord_239295, baseEnd_239295] using wordTrace_append hprefix tailTrace_239295
  have hstable : (prefixWord ++ tailWord_239295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239295).length < 2 ^ (prefixWord ++ tailWord_239295).sum := by decide
  have hdescent : baseEnd_239295 < baseStart_239295 := by decide
  rcases family_descends (prefixWord ++ tailWord_239295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239325 : List Nat := [1, 4, 3, 3, 1, 2, 2, 3]
def baseStart_239325 : Nat := 118140960795 + 239325 * 2 ^ 59
def prefixEnd_239325 : Nat := 4983230072969 + 3 ^ 40 * 239325 * 2
def baseEnd_239325 : Nat := 72822967488818591725553

theorem tailTrace_239325 : CollatzResearch.WordTrace tailWord_239325 prefixEnd_239325 72822967488818591725553 := by
  unfold tailWord_239325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8728899857973873301007429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5819266571982582200671619 8728899857973873301007429)
  ·
    refine ⟨1636668723370101243938893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8728899857973873301007429 1636668723370101243938893)
    ·
      refine ⟨613750771263787966477085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1636668723370101243938893 613750771263787966477085)
      ·
        refine ⟨230156539223920487428907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613750771263787966477085 230156539223920487428907)
        ·
          refine ⟨345234808835880731143361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230156539223920487428907 345234808835880731143361)
          ·
            refine ⟨258926106626910548357521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345234808835880731143361 258926106626910548357521)
            ·
              refine ⟨194194579970182911268141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258926106626910548357521 194194579970182911268141)
              ·
                refine ⟨72822967488818591725553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194194579970182911268141 72822967488818591725553)
                ·
                  rfl

theorem cell19_239325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_239325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239325 prefixEnd_239325 := by exact prefixLift 239325
  have htrace : WordTrace (prefixWord ++ tailWord_239325) baseStart_239325 baseEnd_239325 := by
    simpa [prefixWord, tailWord_239325, baseEnd_239325] using wordTrace_append hprefix tailTrace_239325
  have hstable : (prefixWord ++ tailWord_239325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239325).length < 2 ^ (prefixWord ++ tailWord_239325).sum := by decide
  have hdescent : baseEnd_239325 < baseStart_239325 := by decide
  rcases family_descends (prefixWord ++ tailWord_239325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239350 : List Nat := [5, 1, 1, 1, 1, 3, 7]
def baseStart_239350 : Nat := 118140960795 + 239350 * 2 ^ 59
def prefixEnd_239350 : Nat := 4983230072969 + 3 ^ 40 * 239350 * 2
def baseEnd_239350 : Nat := 24276858203208647056643

theorem tailTrace_239350 : CollatzResearch.WordTrace tailWord_239350 prefixEnd_239350 24276858203208647056643 := by
  unfold tailWord_239350
  simp only [CollatzResearch.WordTrace]
  refine ⟨545613230180206410666719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5819874455255535047111669 545613230180206410666719)
  ·
    refine ⟨818419845270309616000079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545613230180206410666719 818419845270309616000079)
    ·
      refine ⟨1227629767905464424000119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818419845270309616000079 1227629767905464424000119)
      ·
        refine ⟨1841444651858196636000179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227629767905464424000119 1841444651858196636000179)
        ·
          refine ⟨2762166977787294954000269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841444651858196636000179 2762166977787294954000269)
          ·
            refine ⟨1035812616670235607750101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2762166977787294954000269 1035812616670235607750101)
            ·
              refine ⟨24276858203208647056643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1035812616670235607750101 24276858203208647056643)
              ·
                rfl

theorem cell19_239350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_239350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239350 prefixEnd_239350 := by exact prefixLift 239350
  have htrace : WordTrace (prefixWord ++ tailWord_239350) baseStart_239350 baseEnd_239350 := by
    simpa [prefixWord, tailWord_239350, baseEnd_239350] using wordTrace_append hprefix tailTrace_239350
  have hstable : (prefixWord ++ tailWord_239350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239350).length < 2 ^ (prefixWord ++ tailWord_239350).sum := by decide
  have hdescent : baseEnd_239350 < baseStart_239350 := by decide
  rcases family_descends (prefixWord ++ tailWord_239350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239367 : List Nat := [1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_239367 : Nat := 118140960795 + 239367 * 2 ^ 59
def prefixEnd_239367 : Nat := 4983230072969 + 3 ^ 40 * 239367 * 2
def baseEnd_239367 : Nat := 72835747451774938792105

theorem tailTrace_239367 : CollatzResearch.WordTrace tailWord_239367 prefixEnd_239367 72835747451774938792105 := by
  unfold tailWord_239367
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730431723821714474036355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5820287815881142982690903 8730431723821714474036355)
  ·
    refine ⟨13095647585732571711054533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8730431723821714474036355 13095647585732571711054533)
    ·
      refine ⟨2455433922324857195822725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13095647585732571711054533 2455433922324857195822725)
      ·
        refine ⟨460393860435910724216761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2455433922324857195822725 460393860435910724216761)
        ·
          refine ⟨345295395326933043162571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460393860435910724216761 345295395326933043162571)
          ·
            refine ⟨517943092990399564743857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345295395326933043162571 517943092990399564743857)
            ·
              refine ⟨388457319742799673557893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517943092990399564743857 388457319742799673557893)
              ·
                refine ⟨72835747451774938792105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388457319742799673557893 72835747451774938792105)
                ·
                  rfl

theorem cell19_239367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_239367 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239367 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239367 prefixEnd_239367 := by exact prefixLift 239367
  have htrace : WordTrace (prefixWord ++ tailWord_239367) baseStart_239367 baseEnd_239367 := by
    simpa [prefixWord, tailWord_239367, baseEnd_239367] using wordTrace_append hprefix tailTrace_239367
  have hstable : (prefixWord ++ tailWord_239367).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239367).length < 2 ^ (prefixWord ++ tailWord_239367).sum := by decide
  have hdescent : baseEnd_239367 < baseStart_239367 := by decide
  rcases family_descends (prefixWord ++ tailWord_239367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239371 : List Nat := [1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_239371 : Nat := 118140960795 + 239371 * 2 ^ 59
def prefixEnd_239371 : Nat := 4983230072969 + 3 ^ 40 * 239371 * 2
def baseEnd_239371 : Nat := 72836964591104114703205

theorem tailTrace_239371 : CollatzResearch.WordTrace tailWord_239371 prefixEnd_239371 72836964591104114703205 := by
  unfold tailWord_239371
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730577615807223157181967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5820385077204815438121311 8730577615807223157181967)
  ·
    refine ⟨13095866423710834735772951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8730577615807223157181967 13095866423710834735772951)
    ·
      refine ⟨19643799635566252103659427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095866423710834735772951 19643799635566252103659427)
      ·
        refine ⟨29465699453349378155489141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19643799635566252103659427 29465699453349378155489141)
        ·
          refine ⟨2762409323751504202077107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29465699453349378155489141 2762409323751504202077107)
          ·
            refine ⟨4143613985627256303115661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762409323751504202077107 4143613985627256303115661)
            ·
              refine ⟨1553855244610221113668373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4143613985627256303115661 1553855244610221113668373)
              ·
                refine ⟨72836964591104114703205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1553855244610221113668373 72836964591104114703205)
                ·
                  rfl

theorem cell19_239371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_239371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239371 prefixEnd_239371 := by exact prefixLift 239371
  have htrace : WordTrace (prefixWord ++ tailWord_239371) baseStart_239371 baseEnd_239371 := by
    simpa [prefixWord, tailWord_239371, baseEnd_239371] using wordTrace_append hprefix tailTrace_239371
  have hstable : (prefixWord ++ tailWord_239371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239371).length < 2 ^ (prefixWord ++ tailWord_239371).sum := by decide
  have hdescent : baseEnd_239371 < baseStart_239371 := by decide
  rcases family_descends (prefixWord ++ tailWord_239371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239409 : List Nat := [1, 2, 2, 3, 2, 9]
def baseStart_239409 : Nat := 118140960795 + 239409 * 2 ^ 59
def prefixEnd_239409 : Nat := 4983230072969 + 3 ^ 40 * 239409 * 2
def baseEnd_239409 : Nat := 8094280823859031762073

theorem tailTrace_239409 : CollatzResearch.WordTrace tailWord_239409 prefixEnd_239409 8094280823859031762073 := by
  unfold tailWord_239409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731963589669555647065281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5821309059779703764710187 8731963589669555647065281)
  ·
    refine ⟨6548972692252166735298961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8731963589669555647065281 6548972692252166735298961)
    ·
      refine ⟨4911729519189125051474221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6548972692252166735298961 4911729519189125051474221)
      ·
        refine ⟨1841898569695921894302833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4911729519189125051474221 1841898569695921894302833)
        ·
          refine ⟨1381423927271941420727125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841898569695921894302833 1381423927271941420727125)
          ·
            refine ⟨8094280823859031762073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1381423927271941420727125 8094280823859031762073)
            ·
              rfl

theorem cell19_239409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_239409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239409 prefixEnd_239409 := by exact prefixLift 239409
  have htrace : WordTrace (prefixWord ++ tailWord_239409) baseStart_239409 baseEnd_239409 := by
    simpa [prefixWord, tailWord_239409, baseEnd_239409] using wordTrace_append hprefix tailTrace_239409
  have hstable : (prefixWord ++ tailWord_239409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239409).length < 2 ^ (prefixWord ++ tailWord_239409).sum := by decide
  have hdescent : baseEnd_239409 < baseStart_239409 := by decide
  rcases family_descends (prefixWord ++ tailWord_239409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239485 : List Nat := [1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_239485 : Nat := 118140960795 + 239485 * 2 ^ 59
def prefixEnd_239485 : Nat := 4983230072969 + 3 ^ 40 * 239485 * 2
def baseEnd_239485 : Nat := 72871653061985628169561

theorem tailTrace_239485 : CollatzResearch.WordTrace tailWord_239485 prefixEnd_239485 72871653061985628169561 := by
  unfold tailWord_239485
  simp only [CollatzResearch.WordTrace]
  refine ⟨8734735537394220626831909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5823157024929480417887939 8734735537394220626831909)
  ·
    refine ⟨1637762913261416367530983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8734735537394220626831909 1637762913261416367530983)
    ·
      refine ⟨2456644369892124551296475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637762913261416367530983 2456644369892124551296475)
      ·
        refine ⟨3684966554838186826944713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456644369892124551296475 3684966554838186826944713)
        ·
          refine ⟨2763724916128640120208535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3684966554838186826944713 2763724916128640120208535)
          ·
            refine ⟨4145587374192960180312803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763724916128640120208535 4145587374192960180312803)
            ·
              refine ⟨6218381061289440270469205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145587374192960180312803 6218381061289440270469205)
              ·
                refine ⟨72871653061985628169561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6218381061289440270469205 72871653061985628169561)
                ·
                  rfl

theorem cell19_239485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_239485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239485 prefixEnd_239485 := by exact prefixLift 239485
  have htrace : WordTrace (prefixWord ++ tailWord_239485) baseStart_239485 baseEnd_239485 := by
    simpa [prefixWord, tailWord_239485, baseEnd_239485] using wordTrace_append hprefix tailTrace_239485
  have hstable : (prefixWord ++ tailWord_239485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239485).length < 2 ^ (prefixWord ++ tailWord_239485).sum := by decide
  have hdescent : baseEnd_239485 < baseStart_239485 := by decide
  rcases family_descends (prefixWord ++ tailWord_239485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239498 : List Nat := [3, 1, 2, 4, 2, 2, 2, 3]
def baseStart_239498 : Nat := 118140960795 + 239498 * 2 ^ 59
def prefixEnd_239498 : Nat := 4983230072969 + 3 ^ 40 * 239498 * 2
def baseEnd_239498 : Nat := 72875608764805449880637

theorem tailTrace_239498 : CollatzResearch.WordTrace tailWord_239498 prefixEnd_239498 72875608764805449880637 := by
  unfold tailWord_239498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183802421586780961763787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5823473124231415898036765 2183802421586780961763787)
  ·
    refine ⟨3275703632380171442645681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183802421586780961763787 3275703632380171442645681)
    ·
      refine ⟨2456777724285128581984261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3275703632380171442645681 2456777724285128581984261)
      ·
        refine ⟨460645823303461609122049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2456777724285128581984261 460645823303461609122049)
        ·
          refine ⟨345484367477596206841537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460645823303461609122049 345484367477596206841537)
          ·
            refine ⟨259113275608197155131153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345484367477596206841537 259113275608197155131153)
            ·
              refine ⟨194334956706147866348365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259113275608197155131153 194334956706147866348365)
              ·
                refine ⟨72875608764805449880637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194334956706147866348365 72875608764805449880637)
                ·
                  rfl

theorem cell19_239498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_239498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239498 prefixEnd_239498 := by exact prefixLift 239498
  have htrace : WordTrace (prefixWord ++ tailWord_239498) baseStart_239498 baseEnd_239498 := by
    simpa [prefixWord, tailWord_239498, baseEnd_239498] using wordTrace_append hprefix tailTrace_239498
  have hstable : (prefixWord ++ tailWord_239498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239498).length < 2 ^ (prefixWord ++ tailWord_239498).sum := by decide
  have hdescent : baseEnd_239498 < baseStart_239498 := by decide
  rcases family_descends (prefixWord ++ tailWord_239498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239519 : List Nat := [1, 1, 2, 5, 4, 1, 5]
def baseStart_239519 : Nat := 118140960795 + 239519 * 2 ^ 59
def prefixEnd_239519 : Nat := 4983230072969 + 3 ^ 40 * 239519 * 2
def baseEnd_239519 : Nat := 24293999582094541137971

theorem tailTrace_239519 : CollatzResearch.WordTrace tailWord_239519 prefixEnd_239519 24293999582094541137971 := by
  unfold tailWord_239519
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735975619271044433569611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5823983746180696289046407 8735975619271044433569611)
  ·
    refine ⟨13103963428906566650354417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8735975619271044433569611 13103963428906566650354417)
    ·
      refine ⟨9827972571679924987765813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13103963428906566650354417 9827972571679924987765813)
      ·
        refine ⟨921372428594992967603045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9827972571679924987765813 921372428594992967603045)
        ·
          refine ⟨172757330361561181425571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 921372428594992967603045 172757330361561181425571)
          ·
            refine ⟨259135995542341772138357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172757330361561181425571 259135995542341772138357)
            ·
              refine ⟨24293999582094541137971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259135995542341772138357 24293999582094541137971)
              ·
                rfl

theorem cell19_239519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_239519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239519 prefixEnd_239519 := by exact prefixLift 239519
  have htrace : WordTrace (prefixWord ++ tailWord_239519) baseStart_239519 baseEnd_239519 := by
    simpa [prefixWord, tailWord_239519, baseEnd_239519] using wordTrace_append hprefix tailTrace_239519
  have hstable : (prefixWord ++ tailWord_239519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239519).length < 2 ^ (prefixWord ++ tailWord_239519).sum := by decide
  have hdescent : baseEnd_239519 < baseStart_239519 := by decide
  rcases family_descends (prefixWord ++ tailWord_239519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239534 : List Nat := [4, 1, 5, 1, 1, 1, 2, 4]
def baseStart_239534 : Nat := 118140960795 + 239534 * 2 ^ 59
def prefixEnd_239534 : Nat := 4983230072969 + 3 ^ 40 * 239534 * 2
def baseEnd_239534 : Nat := 72886563018768033080539

theorem tailTrace_239534 : CollatzResearch.WordTrace tailWord_239534 prefixEnd_239534 72886563018768033080539 := by
  unfold tailWord_239534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092065339277087749420707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5824348476144467996910437 1092065339277087749420707)
  ·
    refine ⟨1638098008915631624131061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1092065339277087749420707 1638098008915631624131061)
    ·
      refine ⟨153571688335840464762287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1638098008915631624131061 153571688335840464762287)
      ·
        refine ⟨230357532503760697143431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153571688335840464762287 230357532503760697143431)
        ·
          refine ⟨345536298755641045715147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230357532503760697143431 345536298755641045715147)
          ·
            refine ⟨518304448133461568572721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345536298755641045715147 518304448133461568572721)
            ·
              refine ⟨388728336100096176429541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518304448133461568572721 388728336100096176429541)
              ·
                refine ⟨72886563018768033080539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388728336100096176429541 72886563018768033080539)
                ·
                  rfl

theorem cell19_239534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_239534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239534 prefixEnd_239534 := by exact prefixLift 239534
  have htrace : WordTrace (prefixWord ++ tailWord_239534) baseStart_239534 baseEnd_239534 := by
    simpa [prefixWord, tailWord_239534, baseEnd_239534] using wordTrace_append hprefix tailTrace_239534
  have hstable : (prefixWord ++ tailWord_239534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239534).length < 2 ^ (prefixWord ++ tailWord_239534).sum := by decide
  have hdescent : baseEnd_239534 < baseStart_239534 := by decide
  rcases family_descends (prefixWord ++ tailWord_239534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239578 : List Nat := [3, 1, 1, 2, 6, 6]
def baseStart_239578 : Nat := 118140960795 + 239578 * 2 ^ 59
def prefixEnd_239578 : Nat := 4983230072969 + 3 ^ 40 * 239578 * 2
def baseEnd_239578 : Nat := 8099994616820996455849

theorem tailTrace_239578 : CollatzResearch.WordTrace tailWord_239578 prefixEnd_239578 8099994616820996455849 := by
  unfold tailWord_239578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2184531881514324377491847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5825418350704865006644925 2184531881514324377491847)
  ·
    refine ⟨3276797822271486566237771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2184531881514324377491847 3276797822271486566237771)
    ·
      refine ⟨4915196733407229849356657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3276797822271486566237771 4915196733407229849356657)
      ·
        refine ⟨3686397550055422387017493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4915196733407229849356657 3686397550055422387017493)
        ·
          refine ⟨172799885158847924391445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3686397550055422387017493 172799885158847924391445)
          ·
            refine ⟨8099994616820996455849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172799885158847924391445 8099994616820996455849)
            ·
              rfl

theorem cell19_239578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 6].length) (baseStart_239578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239578 prefixEnd_239578 := by exact prefixLift 239578
  have htrace : WordTrace (prefixWord ++ tailWord_239578) baseStart_239578 baseEnd_239578 := by
    simpa [prefixWord, tailWord_239578, baseEnd_239578] using wordTrace_append hprefix tailTrace_239578
  have hstable : (prefixWord ++ tailWord_239578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239578).length < 2 ^ (prefixWord ++ tailWord_239578).sum := by decide
  have hdescent : baseEnd_239578 < baseStart_239578 := by decide
  rcases family_descends (prefixWord ++ tailWord_239578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239673 : List Nat := [1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_239673 : Nat := 118140960795 + 239673 * 2 ^ 59
def prefixEnd_239673 : Nat := 4983230072969 + 3 ^ 40 * 239673 * 2
def baseEnd_239673 : Nat := 72928858610456895991271

theorem tailTrace_239673 : CollatzResearch.WordTrace tailWord_239673 prefixEnd_239673 72928858610456895991271 := by
  unfold tailWord_239673
  simp only [CollatzResearch.WordTrace]
  refine ⟨8741592460713128734675673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5827728307142085823117115 8741592460713128734675673)
  ·
    refine ⟨6556194345534846551006755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8741592460713128734675673 6556194345534846551006755)
    ·
      refine ⟨9834291518302269826510133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6556194345534846551006755 9834291518302269826510133)
      ·
        refine ⟨921964829840837796235325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9834291518302269826510133 921964829840837796235325)
        ·
          refine ⟨345736811190314173588247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 921964829840837796235325 345736811190314173588247)
          ·
            refine ⟨518605216785471260382371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345736811190314173588247 518605216785471260382371)
            ·
              refine ⟨777907825178206890573557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518605216785471260382371 777907825178206890573557)
              ·
                refine ⟨72928858610456895991271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777907825178206890573557 72928858610456895991271)
                ·
                  rfl

theorem cell19_239673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_239673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239673 prefixEnd_239673 := by exact prefixLift 239673
  have htrace : WordTrace (prefixWord ++ tailWord_239673) baseStart_239673 baseEnd_239673 := by
    simpa [prefixWord, tailWord_239673, baseEnd_239673] using wordTrace_append hprefix tailTrace_239673
  have hstable : (prefixWord ++ tailWord_239673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239673).length < 2 ^ (prefixWord ++ tailWord_239673).sum := by decide
  have hdescent : baseEnd_239673 < baseStart_239673 := by decide
  rcases family_descends (prefixWord ++ tailWord_239673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239694 : List Nat := [4, 1, 1, 1, 1, 4, 7]
def baseStart_239694 : Nat := 118140960795 + 239694 * 2 ^ 59
def prefixEnd_239694 : Nat := 4983230072969 + 3 ^ 40 * 239694 * 2
def baseEnd_239694 : Nat := 24311749530645023174849

theorem tailTrace_239694 : CollatzResearch.WordTrace tailWord_239694 prefixEnd_239694 24311749530645023174849 := by
  unfold tailWord_239694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092794799204631165148767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5828238929091366214126757 1092794799204631165148767)
  ·
    refine ⟨1639192198806946747723151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1092794799204631165148767 1639192198806946747723151)
    ·
      refine ⟨2458788298210420121584727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639192198806946747723151 2458788298210420121584727)
      ·
        refine ⟨3688182447315630182377091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458788298210420121584727 3688182447315630182377091)
        ·
          refine ⟨5532273670973445273565637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688182447315630182377091 5532273670973445273565637)
          ·
            refine ⟨1037301313307520988793557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5532273670973445273565637 1037301313307520988793557)
            ·
              refine ⟨24311749530645023174849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1037301313307520988793557 24311749530645023174849)
              ·
                rfl

theorem cell19_239694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_239694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239694 prefixEnd_239694 := by exact prefixLift 239694
  have htrace : WordTrace (prefixWord ++ tailWord_239694) baseStart_239694 baseEnd_239694 := by
    simpa [prefixWord, tailWord_239694, baseEnd_239694] using wordTrace_append hprefix tailTrace_239694
  have hstable : (prefixWord ++ tailWord_239694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239694).length < 2 ^ (prefixWord ++ tailWord_239694).sum := by decide
  have hdescent : baseEnd_239694 < baseStart_239694 := by decide
  rcases family_descends (prefixWord ++ tailWord_239694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239709 : List Nat := [1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_239709 : Nat := 118140960795 + 239709 * 2 ^ 59
def prefixEnd_239709 : Nat := 4983230072969 + 3 ^ 40 * 239709 * 2
def baseEnd_239709 : Nat := 72939812864419479191173

theorem tailTrace_239709 : CollatzResearch.WordTrace tailWord_239709 prefixEnd_239709 72939812864419479191173 := by
  unfold tailWord_239709
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742905488582706882986181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5828603659055137921990787 8742905488582706882986181)
  ·
    refine ⟨1639294779109257540559909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8742905488582706882986181 1639294779109257540559909)
    ·
      refine ⟨307367771082985788854983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1639294779109257540559909 307367771082985788854983)
      ·
        refine ⟨461051656624478683282475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307367771082985788854983 461051656624478683282475)
        ·
          refine ⟨691577484936718024923713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461051656624478683282475 691577484936718024923713)
          ·
            refine ⟨518683113702538518692785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691577484936718024923713 518683113702538518692785)
            ·
              refine ⟨389012335276903889019589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518683113702538518692785 389012335276903889019589)
              ·
                refine ⟨72939812864419479191173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389012335276903889019589 72939812864419479191173)
                ·
                  rfl

theorem cell19_239709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_239709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239709 prefixEnd_239709 := by exact prefixLift 239709
  have htrace : WordTrace (prefixWord ++ tailWord_239709) baseStart_239709 baseEnd_239709 := by
    simpa [prefixWord, tailWord_239709, baseEnd_239709] using wordTrace_append hprefix tailTrace_239709
  have hstable : (prefixWord ++ tailWord_239709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239709).length < 2 ^ (prefixWord ++ tailWord_239709).sum := by decide
  have hdescent : baseEnd_239709 < baseStart_239709 := by decide
  rcases family_descends (prefixWord ++ tailWord_239709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239764 : List Nat := [2, 4, 2, 3, 1, 2, 1, 4]
def baseStart_239764 : Nat := 118140960795 + 239764 * 2 ^ 59
def prefixEnd_239764 : Nat := 4983230072969 + 3 ^ 40 * 239764 * 2
def baseEnd_239764 : Nat := 72956548530195647968801

theorem tailTrace_239764 : CollatzResearch.WordTrace tailWord_239764 prefixEnd_239764 72956548530195647968801 := by
  unfold tailWord_239764
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372455751691725638119173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5829941002255634184158897 4372455751691725638119173)
  ·
    refine ⟨819835453442198557147345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4372455751691725638119173 819835453442198557147345)
    ·
      refine ⟨614876590081648917860509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 819835453442198557147345 614876590081648917860509)
      ·
        refine ⟨230578721280618344197691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614876590081648917860509 230578721280618344197691)
        ·
          refine ⟨345868081920927516296537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230578721280618344197691 345868081920927516296537)
          ·
            refine ⟨259401061440695637222403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345868081920927516296537 259401061440695637222403)
            ·
              refine ⟨389101592161043455833605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259401061440695637222403 389101592161043455833605)
              ·
                refine ⟨72956548530195647968801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389101592161043455833605 72956548530195647968801)
                ·
                  rfl

theorem cell19_239764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_239764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239764 prefixEnd_239764 := by exact prefixLift 239764
  have htrace : WordTrace (prefixWord ++ tailWord_239764) baseStart_239764 baseEnd_239764 := by
    simpa [prefixWord, tailWord_239764, baseEnd_239764] using wordTrace_append hprefix tailTrace_239764
  have hstable : (prefixWord ++ tailWord_239764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239764).length < 2 ^ (prefixWord ++ tailWord_239764).sum := by decide
  have hdescent : baseEnd_239764 < baseStart_239764 := by decide
  rcases family_descends (prefixWord ++ tailWord_239764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239806 : List Nat := [4, 2, 1, 1, 4, 1, 6]
def baseStart_239806 : Nat := 118140960795 + 239806 * 2 ^ 59
def prefixEnd_239806 : Nat := 4983230072969 + 3 ^ 40 * 239806 * 2
def baseEnd_239806 : Nat := 24323109497717331678451

theorem tailTrace_239806 : CollatzResearch.WordTrace tailWord_239806 prefixEnd_239806 24323109497717331678451 := by
  unfold tailWord_239806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093305421153911556158409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5830962246154194966178181 1093305421153911556158409)
  ·
    refine ⟨819979065865433667118807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1093305421153911556158409 819979065865433667118807)
    ·
      refine ⟨1229968598798150500678211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819979065865433667118807 1229968598798150500678211)
      ·
        refine ⟨1844952898197225751017317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229968598798150500678211 1844952898197225751017317)
        ·
          refine ⟨345928668411979828315747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1844952898197225751017317 345928668411979828315747)
          ·
            refine ⟨518893002617969742473621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345928668411979828315747 518893002617969742473621)
            ·
              refine ⟨24323109497717331678451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 518893002617969742473621 24323109497717331678451)
              ·
                rfl

theorem cell19_239806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_239806 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239806 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239806 prefixEnd_239806 := by exact prefixLift 239806
  have htrace : WordTrace (prefixWord ++ tailWord_239806) baseStart_239806 baseEnd_239806 := by
    simpa [prefixWord, tailWord_239806, baseEnd_239806] using wordTrace_append hprefix tailTrace_239806
  have hstable : (prefixWord ++ tailWord_239806).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239806).length < 2 ^ (prefixWord ++ tailWord_239806).sum := by decide
  have hdescent : baseEnd_239806 < baseStart_239806 := by decide
  rcases family_descends (prefixWord ++ tailWord_239806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239808 : List Nat := [2, 1, 1, 2, 5, 2, 6]
def baseStart_239808 : Nat := 118140960795 + 239808 * 2 ^ 59
def prefixEnd_239808 : Nat := 4983230072969 + 3 ^ 40 * 239808 * 2
def baseEnd_239808 : Nat := 24323312354272194330301

theorem tailTrace_239808 : CollatzResearch.WordTrace tailWord_239808 prefixEnd_239808 24323312354272194330301 := by
  unfold tailWord_239808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373258157612023395420039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5831010876816031193893385 4373258157612023395420039)
  ·
    refine ⟨6559887236418035093130059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373258157612023395420039 6559887236418035093130059)
    ·
      refine ⟨9839830854627052639695089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6559887236418035093130059 9839830854627052639695089)
      ·
        refine ⟨7379873140970289479771317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9839830854627052639695089 7379873140970289479771317)
        ·
          refine ⟨691863106965964638728561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7379873140970289479771317 691863106965964638728561)
          ·
            refine ⟨518897330224473479046421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691863106965964638728561 518897330224473479046421)
            ·
              refine ⟨24323312354272194330301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 518897330224473479046421 24323312354272194330301)
              ·
                rfl

theorem cell19_239808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_239808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239808 prefixEnd_239808 := by exact prefixLift 239808
  have htrace : WordTrace (prefixWord ++ tailWord_239808) baseStart_239808 baseEnd_239808 := by
    simpa [prefixWord, tailWord_239808, baseEnd_239808] using wordTrace_append hprefix tailTrace_239808
  have hstable : (prefixWord ++ tailWord_239808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239808).length < 2 ^ (prefixWord ++ tailWord_239808).sum := by decide
  have hdescent : baseEnd_239808 < baseStart_239808 := by decide
  rcases family_descends (prefixWord ++ tailWord_239808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239884 : List Nat := [2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_239884 : Nat := 118140960795 + 239884 * 2 ^ 59
def prefixEnd_239884 : Nat := 4983230072969 + 3 ^ 40 * 239884 * 2
def baseEnd_239884 : Nat := 72993062710070925301807

theorem tailTrace_239884 : CollatzResearch.WordTrace tailWord_239884 prefixEnd_239884 72993062710070925301807 := by
  unfold tailWord_239884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374644131474355885303353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5832858841965807847071137 4374644131474355885303353)
  ·
    refine ⟨3280983098605766913977515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4374644131474355885303353 3280983098605766913977515)
    ·
      refine ⟨4921474647908650370966273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280983098605766913977515 4921474647908650370966273)
      ·
        refine ⟨3691105985931487778224705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4921474647908650370966273 3691105985931487778224705)
        ·
          refine ⟨2768329489448615833668529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3691105985931487778224705 2768329489448615833668529)
          ·
            refine ⟨2076247117086461875251397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768329489448615833668529 2076247117086461875251397)
            ·
              refine ⟨389296334453711601609637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2076247117086461875251397 389296334453711601609637)
              ·
                refine ⟨72993062710070925301807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389296334453711601609637 72993062710070925301807)
                ·
                  rfl

theorem cell19_239884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_239884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239884 prefixEnd_239884 := by exact prefixLift 239884
  have htrace : WordTrace (prefixWord ++ tailWord_239884) baseStart_239884 baseEnd_239884 := by
    simpa [prefixWord, tailWord_239884, baseEnd_239884] using wordTrace_append hprefix tailTrace_239884
  have hstable : (prefixWord ++ tailWord_239884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239884).length < 2 ^ (prefixWord ++ tailWord_239884).sum := by decide
  have hdescent : baseEnd_239884 < baseStart_239884 := by decide
  rcases family_descends (prefixWord ++ tailWord_239884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239903 : List Nat := [1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_239903 : Nat := 118140960795 + 239903 * 2 ^ 59
def prefixEnd_239903 : Nat := 4983230072969 + 3 ^ 40 * 239903 * 2
def baseEnd_239903 : Nat := 72998844121884510879533

theorem tailTrace_239903 : CollatzResearch.WordTrace tailWord_239903 prefixEnd_239903 72998844121884510879533 := by
  unfold tailWord_239903
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749981249879878015548363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5833320833253252010365575 8749981249879878015548363)
  ·
    refine ⟨13124971874819817023322545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8749981249879878015548363 13124971874819817023322545)
    ·
      refine ⟨9843728906114862767491909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13124971874819817023322545 9843728906114862767491909)
      ·
        refine ⟨1845699169896536768904733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9843728906114862767491909 1845699169896536768904733)
        ·
          refine ⟨692137188711201288339275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1845699169896536768904733 692137188711201288339275)
          ·
            refine ⟨1038205783066801932508913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692137188711201288339275 1038205783066801932508913)
            ·
              refine ⟨778654337300101449381685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038205783066801932508913 778654337300101449381685)
              ·
                refine ⟨72998844121884510879533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778654337300101449381685 72998844121884510879533)
                ·
                  rfl

theorem cell19_239903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_239903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239903 prefixEnd_239903 := by exact prefixLift 239903
  have htrace : WordTrace (prefixWord ++ tailWord_239903) baseStart_239903 baseEnd_239903 := by
    simpa [prefixWord, tailWord_239903, baseEnd_239903] using wordTrace_append hprefix tailTrace_239903
  have hstable : (prefixWord ++ tailWord_239903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239903).length < 2 ^ (prefixWord ++ tailWord_239903).sum := by decide
  have hdescent : baseEnd_239903 < baseStart_239903 := by decide
  rcases family_descends (prefixWord ++ tailWord_239903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239918 : List Nat := [4, 1, 3, 3, 2, 6]
def baseStart_239918 : Nat := 118140960795 + 239918 * 2 ^ 59
def prefixEnd_239918 : Nat := 4983230072969 + 3 ^ 40 * 239918 * 2
def baseEnd_239918 : Nat := 8111489821596546727351

theorem tailTrace_239918 : CollatzResearch.WordTrace tailWord_239918 prefixEnd_239918 8111489821596546727351 := by
  unfold tailWord_239918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093816043103191947168051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5833685563217023718229605 1093816043103191947168051)
  ·
    refine ⟨1640724064654787920752077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1093816043103191947168051 1640724064654787920752077)
    ·
      refine ⟨615271524245545470282029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1640724064654787920752077 615271524245545470282029)
      ·
        refine ⟨230726821592079551355761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615271524245545470282029 230726821592079551355761)
        ·
          refine ⟨173045116194059663516821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230726821592079551355761 173045116194059663516821)
          ·
            refine ⟨8111489821596546727351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173045116194059663516821 8111489821596546727351)
            ·
              rfl

theorem cell19_239918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 6].length) (baseStart_239918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239918 prefixEnd_239918 := by exact prefixLift 239918
  have htrace : WordTrace (prefixWord ++ tailWord_239918) baseStart_239918 baseEnd_239918 := by
    simpa [prefixWord, tailWord_239918, baseEnd_239918] using wordTrace_append hprefix tailTrace_239918
  have hstable : (prefixWord ++ tailWord_239918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239918).length < 2 ^ (prefixWord ++ tailWord_239918).sum := by decide
  have hdescent : baseEnd_239918 < baseStart_239918 := by decide
  rcases family_descends (prefixWord ++ tailWord_239918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239922 : List Nat := [3, 2, 1, 1, 5, 7]
def baseStart_239922 : Nat := 118140960795 + 239922 * 2 ^ 59
def prefixEnd_239922 : Nat := 4983230072969 + 3 ^ 40 * 239922 * 2
def baseEnd_239922 : Nat := 8111625059299788495251

theorem tailTrace_239922 : CollatzResearch.WordTrace tailWord_239922 prefixEnd_239922 8111625059299788495251 := by
  unfold tailWord_239922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187668559202761065122505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5833782824540696173660013 2187668559202761065122505)
  ·
    refine ⟨1640751419402070798841879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2187668559202761065122505 1640751419402070798841879)
    ·
      refine ⟨2461127129103106198262819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640751419402070798841879 2461127129103106198262819)
      ·
        refine ⟨3691690693654659297394229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461127129103106198262819 3691690693654659297394229)
        ·
          refine ⟨346096002530124309130709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3691690693654659297394229 346096002530124309130709)
          ·
            refine ⟨8111625059299788495251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 346096002530124309130709 8111625059299788495251)
            ·
              rfl

theorem cell19_239922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_239922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239922 prefixEnd_239922 := by exact prefixLift 239922
  have htrace : WordTrace (prefixWord ++ tailWord_239922) baseStart_239922 baseEnd_239922 := by
    simpa [prefixWord, tailWord_239922, baseEnd_239922] using wordTrace_append hprefix tailTrace_239922
  have hstable : (prefixWord ++ tailWord_239922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239922).length < 2 ^ (prefixWord ++ tailWord_239922).sum := by decide
  have hdescent : baseEnd_239922 < baseStart_239922 := by decide
  rcases family_descends (prefixWord ++ tailWord_239922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239937 : List Nat := [1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_239937 : Nat := 118140960795 + 239937 * 2 ^ 59
def prefixEnd_239937 : Nat := 4983230072969 + 3 ^ 40 * 239937 * 2
def baseEnd_239937 : Nat := 73009189806182506123885

theorem tailTrace_239937 : CollatzResearch.WordTrace tailWord_239937 prefixEnd_239937 73009189806182506123885 := by
  unfold tailWord_239937
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751221331756701822286065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5834147554504467881524043 8751221331756701822286065)
  ·
    refine ⟨6563415998817526366714549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8751221331756701822286065 6563415998817526366714549)
    ·
      refine ⟨615320249889143096879489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6563415998817526366714549 615320249889143096879489)
      ·
        refine ⟨461490187416857322659617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615320249889143096879489 461490187416857322659617)
        ·
          refine ⟨346117640562642991994713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461490187416857322659617 346117640562642991994713)
          ·
            refine ⟨259588230421982243996035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346117640562642991994713 259588230421982243996035)
            ·
              refine ⟨389382345632973365994053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259588230421982243996035 389382345632973365994053)
              ·
                refine ⟨73009189806182506123885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389382345632973365994053 73009189806182506123885)
                ·
                  rfl

theorem cell19_239937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_239937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_239937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_239937 prefixEnd_239937 := by exact prefixLift 239937
  have htrace : WordTrace (prefixWord ++ tailWord_239937) baseStart_239937 baseEnd_239937 := by
    simpa [prefixWord, tailWord_239937, baseEnd_239937] using wordTrace_append hprefix tailTrace_239937
  have hstable : (prefixWord ++ tailWord_239937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239937).length < 2 ^ (prefixWord ++ tailWord_239937).sum := by decide
  have hdescent : baseEnd_239937 < baseStart_239937 := by decide
  rcases family_descends (prefixWord ++ tailWord_239937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240053 : List Nat := [1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_240053 : Nat := 118140960795 + 240053 * 2 ^ 59
def prefixEnd_240053 : Nat := 4983230072969 + 3 ^ 40 * 240053 * 2
def baseEnd_240053 : Nat := 73044486846728607545791

theorem tailTrace_240053 : CollatzResearch.WordTrace tailWord_240053 prefixEnd_240053 73044486846728607545791 := by
  unfold tailWord_240053
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755452199336453633508813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5836968132890969089005875 8755452199336453633508813)
  ·
    refine ⟨3283294574751170112565805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8755452199336453633508813 3283294574751170112565805)
    ·
      refine ⟨1231235465531688792212177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3283294574751170112565805 1231235465531688792212177)
      ·
        refine ⟨923426599148766594159133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1231235465531688792212177 923426599148766594159133)
        ·
          refine ⟨346284974680787472809675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 923426599148766594159133 346284974680787472809675)
          ·
            refine ⟨519427462021181209214513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346284974680787472809675 519427462021181209214513)
            ·
              refine ⟨389570596515885906910885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519427462021181209214513 389570596515885906910885)
              ·
                refine ⟨73044486846728607545791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389570596515885906910885 73044486846728607545791)
                ·
                  rfl

theorem cell19_240053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_240053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240053 prefixEnd_240053 := by exact prefixLift 240053
  have htrace : WordTrace (prefixWord ++ tailWord_240053) baseStart_240053 baseEnd_240053 := by
    simpa [prefixWord, tailWord_240053, baseEnd_240053] using wordTrace_append hprefix tailTrace_240053
  have hstable : (prefixWord ++ tailWord_240053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240053).length < 2 ^ (prefixWord ++ tailWord_240053).sum := by decide
  have hdescent : baseEnd_240053 < baseStart_240053 := by decide
  rcases family_descends (prefixWord ++ tailWord_240053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240055 : List Nat := [1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_240055 : Nat := 118140960795 + 240055 * 2 ^ 59
def prefixEnd_240055 : Nat := 4983230072969 + 3 ^ 40 * 240055 * 2
def baseEnd_240055 : Nat := 73045095416393195501341

theorem tailTrace_240055 : CollatzResearch.WordTrace tailWord_240055 prefixEnd_240055 73045095416393195501341 := by
  unfold tailWord_240055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755525145329207975081619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5837016763552805316721079 8755525145329207975081619)
  ·
    refine ⟨13133287717993811962622429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8755525145329207975081619 13133287717993811962622429)
    ·
      refine ⟨4924982894247679485983411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13133287717993811962622429 4924982894247679485983411)
      ·
        refine ⟨7387474341371519228975117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924982894247679485983411 7387474341371519228975117)
        ·
          refine ⟨2770302878014319710865669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7387474341371519228975117 2770302878014319710865669)
          ·
            refine ⟨519431789627684945787313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2770302878014319710865669 519431789627684945787313)
            ·
              refine ⟨389573842220763709340485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519431789627684945787313 389573842220763709340485)
              ·
                refine ⟨73045095416393195501341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389573842220763709340485 73045095416393195501341)
                ·
                  rfl

theorem cell19_240055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_240055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240055 prefixEnd_240055 := by exact prefixLift 240055
  have htrace : WordTrace (prefixWord ++ tailWord_240055) baseStart_240055 baseEnd_240055 := by
    simpa [prefixWord, tailWord_240055, baseEnd_240055] using wordTrace_append hprefix tailTrace_240055
  have hstable : (prefixWord ++ tailWord_240055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240055).length < 2 ^ (prefixWord ++ tailWord_240055).sum := by decide
  have hdescent : baseEnd_240055 < baseStart_240055 := by decide
  rcases family_descends (prefixWord ++ tailWord_240055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
