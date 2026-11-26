Theory vfmTest2255[no_sig_docs]
Ancestors vfmTestDefs2255
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2255_0.nsv", "result2255_1.nsv", "result2255_2.nsv"];
val thyn = "vfmTestDefs2255";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
