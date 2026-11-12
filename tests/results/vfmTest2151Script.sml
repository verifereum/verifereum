Theory vfmTest2151[no_sig_docs]
Ancestors vfmTestDefs2151
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2151_0.nsv", "result2151_1.nsv", "result2151_2.nsv", "result2151_3.nsv", "result2151_4.nsv", "result2151_5.nsv", "result2151_6.nsv", "result2151_7.nsv"];
val thyn = "vfmTestDefs2151";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
