Theory vfmTest2839[no_sig_docs]
Ancestors vfmTestDefs2839
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2839_0.nsv", "result2839_1.nsv", "result2839_2.nsv", "result2839_3.nsv"];
val thyn = "vfmTestDefs2839";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
