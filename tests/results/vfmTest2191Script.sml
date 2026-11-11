Theory vfmTest2191[no_sig_docs]
Ancestors vfmTestDefs2191
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2191_0.nsv", "result2191_1.nsv", "result2191_2.nsv", "result2191_3.nsv", "result2191_4.nsv", "result2191_5.nsv"];
val thyn = "vfmTestDefs2191";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
