Theory vfmTest2802[no_sig_docs]
Ancestors vfmTestDefs2802
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2802_0.nsv", "result2802_1.nsv", "result2802_2.nsv", "result2802_3.nsv"];
val thyn = "vfmTestDefs2802";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
