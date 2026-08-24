Theory vfmTest0242[no_sig_docs]
Ancestors vfmTestDefs0242
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0242_0.nsv", "result0242_1.nsv", "result0242_2.nsv", "result0242_3.nsv", "result0242_4.nsv", "result0242_5.nsv", "result0242_6.nsv"];
val thyn = "vfmTestDefs0242";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
