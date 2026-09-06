Theory vfmTest2338[no_sig_docs]
Ancestors vfmTestDefs2338
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2338_0.nsv", "result2338_1.nsv", "result2338_2.nsv", "result2338_3.nsv"];
val thyn = "vfmTestDefs2338";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
