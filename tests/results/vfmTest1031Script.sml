Theory vfmTest1031[no_sig_docs]
Ancestors vfmTestDefs1031
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1031_0.nsv", "result1031_1.nsv", "result1031_2.nsv", "result1031_3.nsv", "result1031_4.nsv", "result1031_5.nsv"];
val thyn = "vfmTestDefs1031";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
