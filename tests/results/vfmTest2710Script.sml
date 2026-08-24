Theory vfmTest2710[no_sig_docs]
Ancestors vfmTestDefs2710
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2710_0.nsv", "result2710_1.nsv", "result2710_2.nsv", "result2710_3.nsv"];
val thyn = "vfmTestDefs2710";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
