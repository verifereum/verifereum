Theory vfmTest2196[no_sig_docs]
Ancestors vfmTestDefs2196
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2196_0.nsv", "result2196_1.nsv", "result2196_2.nsv", "result2196_3.nsv"];
val thyn = "vfmTestDefs2196";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
