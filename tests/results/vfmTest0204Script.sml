Theory vfmTest0204[no_sig_docs]
Ancestors vfmTestDefs0204
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0204_0.nsv", "result0204_1.nsv", "result0204_2.nsv", "result0204_3.nsv", "result0204_4.nsv"];
val thyn = "vfmTestDefs0204";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
