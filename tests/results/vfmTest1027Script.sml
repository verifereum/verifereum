Theory vfmTest1027[no_sig_docs]
Ancestors vfmTestDefs1027
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1027_0.nsv", "result1027_1.nsv", "result1027_2.nsv", "result1027_3.nsv", "result1027_4.nsv", "result1027_5.nsv", "result1027_6.nsv", "result1027_7.nsv", "result1027_8.nsv"];
val thyn = "vfmTestDefs1027";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
