Theory vfmTest0417[no_sig_docs]
Ancestors vfmTestDefs0417
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0417_0.nsv", "result0417_1.nsv", "result0417_2.nsv", "result0417_3.nsv", "result0417_4.nsv", "result0417_5.nsv", "result0417_6.nsv", "result0417_7.nsv"];
val thyn = "vfmTestDefs0417";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
