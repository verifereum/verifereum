Theory vfmTest0766[no_sig_docs]
Ancestors vfmTestDefs0766
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0766_0.nsv", "result0766_1.nsv", "result0766_2.nsv", "result0766_3.nsv", "result0766_4.nsv", "result0766_5.nsv"];
val thyn = "vfmTestDefs0766";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
