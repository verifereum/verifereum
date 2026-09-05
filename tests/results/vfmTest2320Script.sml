Theory vfmTest2320[no_sig_docs]
Ancestors vfmTestDefs2320
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2320_0.nsv", "result2320_1.nsv", "result2320_2.nsv", "result2320_3.nsv", "result2320_4.nsv", "result2320_5.nsv", "result2320_6.nsv"];
val thyn = "vfmTestDefs2320";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
