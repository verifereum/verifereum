Theory vfmTest2711[no_sig_docs]
Ancestors vfmTestDefs2711
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2711_0.nsv", "result2711_1.nsv", "result2711_2.nsv", "result2711_3.nsv"];
val thyn = "vfmTestDefs2711";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
