Theory vfmTest0963[no_sig_docs]
Ancestors vfmTestDefs0963
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0963_0.nsv", "result0963_1.nsv", "result0963_2.nsv", "result0963_3.nsv"];
val thyn = "vfmTestDefs0963";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
