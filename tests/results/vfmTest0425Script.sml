Theory vfmTest0425[no_sig_docs]
Ancestors vfmTestDefs0425
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0425_0.nsv", "result0425_1.nsv", "result0425_2.nsv", "result0425_3.nsv", "result0425_4.nsv"];
val thyn = "vfmTestDefs0425";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
