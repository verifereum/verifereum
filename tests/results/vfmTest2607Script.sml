Theory vfmTest2607[no_sig_docs]
Ancestors vfmTestDefs2607
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2607_0.nsv", "result2607_1.nsv", "result2607_2.nsv", "result2607_3.nsv"];
val thyn = "vfmTestDefs2607";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
