Theory vfmTest0385[no_sig_docs]
Ancestors vfmTestDefs0385
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0385_0.nsv", "result0385_1.nsv", "result0385_2.nsv", "result0385_3.nsv", "result0385_4.nsv", "result0385_5.nsv"];
val thyn = "vfmTestDefs0385";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
