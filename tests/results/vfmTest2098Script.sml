Theory vfmTest2098[no_sig_docs]
Ancestors vfmTestDefs2098
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2098_0.nsv", "result2098_1.nsv", "result2098_2.nsv", "result2098_3.nsv", "result2098_4.nsv", "result2098_5.nsv"];
val thyn = "vfmTestDefs2098";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
