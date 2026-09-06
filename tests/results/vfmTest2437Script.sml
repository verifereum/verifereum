Theory vfmTest2437[no_sig_docs]
Ancestors vfmTestDefs2437
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2437_0.nsv", "result2437_1.nsv", "result2437_2.nsv", "result2437_3.nsv"];
val thyn = "vfmTestDefs2437";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
