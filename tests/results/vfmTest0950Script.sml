Theory vfmTest0950[no_sig_docs]
Ancestors vfmTestDefs0950
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0950_0.nsv", "result0950_1.nsv", "result0950_2.nsv", "result0950_3.nsv", "result0950_4.nsv", "result0950_5.nsv", "result0950_6.nsv", "result0950_7.nsv", "result0950_8.nsv", "result0950_9.nsv"];
val thyn = "vfmTestDefs0950";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
