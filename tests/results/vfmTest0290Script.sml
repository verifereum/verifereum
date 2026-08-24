Theory vfmTest0290[no_sig_docs]
Ancestors vfmTestDefs0290
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0290_0.nsv", "result0290_1.nsv", "result0290_2.nsv", "result0290_3.nsv", "result0290_4.nsv", "result0290_5.nsv"];
val thyn = "vfmTestDefs0290";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
