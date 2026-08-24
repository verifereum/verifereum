Theory vfmTest0477[no_sig_docs]
Ancestors vfmTestDefs0477
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0477_0.nsv", "result0477_1.nsv", "result0477_2.nsv", "result0477_3.nsv", "result0477_4.nsv", "result0477_5.nsv"];
val thyn = "vfmTestDefs0477";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
