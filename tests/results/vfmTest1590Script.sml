Theory vfmTest1590[no_sig_docs]
Ancestors vfmTestDefs1590
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1590_0.nsv", "result1590_1.nsv", "result1590_2.nsv", "result1590_3.nsv", "result1590_4.nsv", "result1590_5.nsv"];
val thyn = "vfmTestDefs1590";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
