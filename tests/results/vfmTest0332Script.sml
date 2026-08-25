Theory vfmTest0332[no_sig_docs]
Ancestors vfmTestDefs0332
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0332_0.nsv", "result0332_1.nsv", "result0332_2.nsv", "result0332_3.nsv"];
val thyn = "vfmTestDefs0332";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
