Theory vfmTest0081[no_sig_docs]
Ancestors vfmTestDefs0081
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0081_0.nsv", "result0081_1.nsv"];
val thyn = "vfmTestDefs0081";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
