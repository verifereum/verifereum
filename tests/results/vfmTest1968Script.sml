Theory vfmTest1968[no_sig_docs]
Ancestors vfmTestDefs1968
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1968_0.nsv", "result1968_1.nsv", "result1968_2.nsv", "result1968_3.nsv", "result1968_4.nsv", "result1968_5.nsv", "result1968_6.nsv"];
val thyn = "vfmTestDefs1968";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
