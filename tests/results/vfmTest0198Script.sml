Theory vfmTest0198[no_sig_docs]
Ancestors vfmTestDefs0198
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0198_0.nsv", "result0198_1.nsv", "result0198_2.nsv", "result0198_3.nsv", "result0198_4.nsv", "result0198_5.nsv"];
val thyn = "vfmTestDefs0198";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
