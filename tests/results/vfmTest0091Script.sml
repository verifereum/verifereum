Theory vfmTest0091[no_sig_docs]
Ancestors vfmTestDefs0091
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0091_0.nsv", "result0091_1.nsv", "result0091_2.nsv", "result0091_3.nsv", "result0091_4.nsv", "result0091_5.nsv"];
val thyn = "vfmTestDefs0091";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
