Theory vfmTest0182[no_sig_docs]
Ancestors vfmTestDefs0182
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0182_0.nsv", "result0182_1.nsv", "result0182_2.nsv", "result0182_3.nsv", "result0182_4.nsv", "result0182_5.nsv"];
val thyn = "vfmTestDefs0182";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
