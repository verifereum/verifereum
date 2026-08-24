Theory vfmTest2180[no_sig_docs]
Ancestors vfmTestDefs2180
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2180_0.nsv", "result2180_1.nsv", "result2180_2.nsv", "result2180_3.nsv", "result2180_4.nsv", "result2180_5.nsv", "result2180_6.nsv", "result2180_7.nsv"];
val thyn = "vfmTestDefs2180";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
