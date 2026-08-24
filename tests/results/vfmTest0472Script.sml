Theory vfmTest0472[no_sig_docs]
Ancestors vfmTestDefs0472
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0472_0.nsv", "result0472_1.nsv", "result0472_2.nsv", "result0472_3.nsv", "result0472_4.nsv", "result0472_5.nsv", "result0472_6.nsv", "result0472_7.nsv", "result0472_8.nsv"];
val thyn = "vfmTestDefs0472";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
