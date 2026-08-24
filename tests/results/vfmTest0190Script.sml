Theory vfmTest0190[no_sig_docs]
Ancestors vfmTestDefs0190
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0190_0.nsv", "result0190_1.nsv", "result0190_2.nsv", "result0190_3.nsv"];
val thyn = "vfmTestDefs0190";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
