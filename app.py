from flask import Flask, render_template, request, jsonify
import json
import csv
import io
import time
import webbrowser
import threading
from typing import List, Dict, Tuple


class DoThi:
    """Lớp đại diện cho đồ thị vô hướng có trọng số (thành phố và khoảng cách)."""

    def __init__(self):
        """Khởi tạo đồ thị rỗng."""
        self.dinh_theo_ten: Dict[str, int] = {}  # Tên thành phố -> chỉ số
        self.ma_tran_ke: List[List[float]] = []  # Ma trận kề lưu trọng số
        self.ten_dinh: List[str] = []  # Danh sách tên thành phố

    def them_dinh(self, ten_thanh_pho: str) -> int:
        """Thêm một đỉnh (thành phố) mới vào đồ thị, trả về index của nó."""
        if ten_thanh_pho not in self.dinh_theo_ten:
            chi_so_moi = len(self.dinh_theo_ten)
            self.dinh_theo_ten[ten_thanh_pho] = chi_so_moi
            self.ten_dinh.append(ten_thanh_pho)

            # Mở rộng ma trận kề cho đỉnh mới
            for hang in self.ma_tran_ke:
                hang.append(float("inf"))
            self.ma_tran_ke.append([float("inf")] * (chi_so_moi + 1))

            # Khoảng cách từ một thành phố đến chính nó là 0
            self.ma_tran_ke[chi_so_moi][chi_so_moi] = 0

            return chi_so_moi

        return self.dinh_theo_ten[ten_thanh_pho]

    def them_canh(self, thanh_pho_a: str, thanh_pho_b: str, khoang_cach: float) -> None:
        """Thêm cạnh (khoảng cách) giữa hai thành phố."""
        chi_so_a = self.them_dinh(thanh_pho_a)
        chi_so_b = self.them_dinh(thanh_pho_b)

        self.ma_tran_ke[chi_so_a][chi_so_b] = khoang_cach
        self.ma_tran_ke[chi_so_b][chi_so_a] = khoang_cach

    def lay_trong_so(self, chi_so_a: int, chi_so_b: int) -> float:
        """Lấy trọng số (khoảng cách) giữa hai đỉnh theo chỉ số."""
        return self.ma_tran_ke[chi_so_a][chi_so_b]

    def so_dinh(self) -> int:
        """Trả về số lượng thành phố trong đồ thị."""
        return len(self.dinh_theo_ten)


class BoGiaiNhanhCanTSP:
    """
    Bộ giải bài toán người du lịch (TSP) bằng thuật toán Nhánh Cận.

    - Đầu vào: đồ thị vô hướng có trọng số (các thành phố và khoảng cách giữa chúng).
    - Đầu ra: lộ trình tối ưu đi qua tất cả các thành phố đúng một lần và quay về điểm xuất phát.
    - Độ phức tạp trong trường hợp xấu nhất: O(n!) về thời gian, O(n^2) về bộ nhớ.
    """

    def __init__(self, do_thi: DoThi):
        self.do_thi = do_thi
        self.so_dinh = do_thi.so_dinh()
        self.chi_phi_tot_nhat: float = float("inf")
        self.lo_trinh_tot_nhat: List[int] = []
        self.so_nut_duoc_duyet: int = 0

    def giai(self, start_city: str = None) -> Dict:
        """Giải bài toán TSP và trả về kết quả ở dạng dễ dùng cho giao diện/Web."""
        thoi_gian_bat_dau = time.time()

        if self.so_dinh < 2:
            lo_trinh = [self.do_thi.ten_dinh[0]] if self.so_dinh == 1 else []
            return {
                "route": lo_trinh,
                "total_distance": 0,
                "execution_time": 0.0,
                "nodes_explored": 0,
                "start_city": start_city or (self.do_thi.ten_dinh[0] if self.so_dinh == 1 else None),
            }

        # Khởi tạo
        self.chi_phi_tot_nhat = float("inf")
        self.lo_trinh_tot_nhat = []
        self.so_nut_duoc_duyet = 0

        # Tạo ma trận chi phí từ đồ thị
        ma_tran_chi_phi = self._tao_ma_tran_chi_phi()

        # Tính cận dưới ban đầu
        can_duoi_ban_dau = self._tinh_can_duoi_ban_dau(ma_tran_chi_phi)

        # Xác định điểm bắt đầu
        if start_city and start_city in self.do_thi.dinh_theo_ten:
            dinh_bat_dau = self.do_thi.dinh_theo_ten[start_city]
        else:
            dinh_bat_dau = 0  # Mặc định bắt đầu từ đỉnh 0
        
        # Bắt đầu từ đỉnh được chọn
        lo_trinh_ban_dau = [dinh_bat_dau]
        chi_phi_hien_tai = 0.0
        da_tham = {dinh_bat_dau}

        # Gọi đệ quy nhánh cận
        self._nhanh_can(
            ma_tran_chi_phi,
            lo_trinh_ban_dau,
            chi_phi_hien_tai,
            da_tham,
            can_duoi_ban_dau,
        )

        # Nếu không tìm được lộ trình hợp lệ thì báo lỗi rõ ràng
        if not self.lo_trinh_tot_nhat or self.chi_phi_tot_nhat == float("inf"):
            raise ValueError(
                "Không tìm được lộ trình hợp lệ. "
                "Vui lòng kiểm tra lại các khoảng cách giữa các thành phố (đồ thị phải liên thông)."
            )

        thoi_gian_thuc_thi = time.time() - thoi_gian_bat_dau

        # Chuyển từ chỉ số sang tên thành phố
        lo_trinh_theo_ten = [self.do_thi.ten_dinh[i] for i in self.lo_trinh_tot_nhat]

        # Tạo danh sách các chặng đi chi tiết (bao gồm chặng quay về điểm xuất phát)
        cac_chang_di = []
        tong_tich_luy = 0.0
        for idx in range(len(self.lo_trinh_tot_nhat)):
            i = self.lo_trinh_tot_nhat[idx]
            j = (
                self.lo_trinh_tot_nhat[(idx + 1) % len(self.lo_trinh_tot_nhat)]
            )  # Quay về điểm đầu ở cuối chu trình
            khoang_cach = self.do_thi.lay_trong_so(i, j)
            tong_tich_luy += khoang_cach
            cac_chang_di.append(
                {
                    "from": self.do_thi.ten_dinh[i],
                    "to": self.do_thi.ten_dinh[j],
                    "distance": khoang_cach,
                    "cumulative": tong_tich_luy,
                }
            )

        return {
            "route": lo_trinh_theo_ten,
            "total_distance": self.chi_phi_tot_nhat,
            "execution_time": thoi_gian_thuc_thi,
            "nodes_explored": self.so_nut_duoc_duyet,
            "steps": cac_chang_di,
            "start_city": self.do_thi.ten_dinh[dinh_bat_dau],
        }

    # ==================== CAC HAM HO TRO NOI BO ====================

    def _tao_ma_tran_chi_phi(self) -> List[List[float]]:
        """Tạo ma trận chi phí từ đồ thị gốc."""
        ma_tran_chi_phi: List[List[float]] = []

        for i in range(self.so_dinh):
            hang: List[float] = []
            for j in range(self.so_dinh):
                if i == j:
                    hang.append(0.0)
                else:
                    trong_so = self.do_thi.lay_trong_so(i, j)
                    if trong_so == float("inf"):
                        hang.append(float("inf"))
                    else:
                        hang.append(trong_so)
            ma_tran_chi_phi.append(hang)

        return ma_tran_chi_phi

    def _tinh_can_duoi_ban_dau(self, ma_tran_chi_phi: List[List[float]]) -> float:
        """
        Tính cận dưới ban đầu.

        Ý tưởng: với mỗi thành phố, lấy cạnh ngắn nhất nối nó với thành phố khác,
        cộng lại và chia 2 (vì mỗi cạnh sẽ được tính 2 lần).
        """
        tong = 0.0

        for i in range(self.so_dinh):
            cac_can = [ma_tran_chi_phi[i][j] for j in range(self.so_dinh) if i != j]
            if cac_can:
                tong += min(cac_can)

        return tong / 2.0

    def _tinh_can_duoi(
        self, ma_tran_chi_phi: List[List[float]], lo_trinh: List[int], da_tham: set
    ) -> float:
        """
        Tính cận dưới cho trạng thái hiện tại.

        - Cộng chi phí của các cạnh đã đi trong lộ trình hiện tại.
        - Với các thành phố chưa thăm, ước lượng chi phí tối thiểu cần thêm vào
          bằng cách lấy trung bình (min_in + min_out) / 2 cho từng đỉnh.
        """
        if len(lo_trinh) == self.so_dinh:
            # Nếu đã thăm hết, chỉ còn cạnh quay về điểm xuất phát
            return ma_tran_chi_phi[lo_trinh[-1]][lo_trinh[0]]

        tong = 0.0

        # Chi phí của các cạnh đã đi trong lộ trình
        for i in range(len(lo_trinh) - 1):
            tong += ma_tran_chi_phi[lo_trinh[i]][lo_trinh[i + 1]]

        # Các đỉnh chưa thăm
        chua_tham = set(range(self.so_dinh)) - da_tham

        for i in chua_tham:
            min_out = float("inf")
            min_in = float("inf")

            # Cạnh đi ra nhỏ nhất từ i
            for j in chua_tham:
                if i != j and ma_tran_chi_phi[i][j] < min_out:
                    min_out = ma_tran_chi_phi[i][j]

            # Cạnh đi vào nhỏ nhất đến i
            for j in chua_tham:
                if i != j and ma_tran_chi_phi[j][i] < min_in:
                    min_in = ma_tran_chi_phi[j][i]

            if min_out != float("inf") and min_in != float("inf"):
                tong += (min_out + min_in) / 2.0

        return tong

    def _nhanh_can(
        self,
        ma_tran_chi_phi: List[List[float]],
        lo_trinh: List[int],
        chi_phi_hien_tai: float,
        da_tham: set,
        can_duoi_hien_tai: float,
    ) -> None:
        """Thuật toán nhánh cận chính (đệ quy)."""
        self.so_nut_duoc_duyet += 1

        # Điều kiện cắt nhánh
        if can_duoi_hien_tai >= self.chi_phi_tot_nhat:
            return

        # Nếu đã đi qua tất cả các thành phố
        if len(lo_trinh) == self.so_dinh:
            # Kiểm tra có đường quay về điểm xuất phát hay không
            chi_phi_quay_ve = ma_tran_chi_phi[lo_trinh[-1]][lo_trinh[0]]
            if chi_phi_quay_ve != float("inf"):
                tong_chi_phi = chi_phi_hien_tai + chi_phi_quay_ve
                if tong_chi_phi < self.chi_phi_tot_nhat:
                    self.chi_phi_tot_nhat = tong_chi_phi
                    self.lo_trinh_tot_nhat = lo_trinh.copy()
            return

        # Tạo các nhánh con từ đỉnh hiện tại
        chua_tham = set(range(self.so_dinh)) - da_tham
        dinh_hien_tai = lo_trinh[-1]

        # Xét các đỉnh chưa thăm theo thứ tự ưu tiên (cận dưới tăng dần)
        ung_cu_vien: List[Tuple[float, float, List[int], set]] = []

        for dinh_tiep_theo in chua_tham:
            if ma_tran_chi_phi[dinh_hien_tai][dinh_tiep_theo] == float("inf"):
                continue

            chi_phi_moi = chi_phi_hien_tai + ma_tran_chi_phi[dinh_hien_tai][dinh_tiep_theo]
            lo_trinh_moi = lo_trinh + [dinh_tiep_theo]
            da_tham_moi = da_tham | {dinh_tiep_theo}
            can_duoi_moi = self._tinh_can_duoi(
                ma_tran_chi_phi, lo_trinh_moi, da_tham_moi
            )

            ung_cu_vien.append((can_duoi_moi, chi_phi_moi, lo_trinh_moi, da_tham_moi))

        # Sắp xếp theo cận dưới tăng dần để ưu tiên nhánh tiềm năng
        ung_cu_vien.sort(key=lambda x: x[0])

        for can_duoi, chi_phi, lo_trinh_moi, da_tham_moi in ung_cu_vien:
            if can_duoi < self.chi_phi_tot_nhat:
                self._nhanh_can(
                    ma_tran_chi_phi,
                    lo_trinh_moi,
                    chi_phi,
                    da_tham_moi,
                    can_duoi,
                )


def tao_du_lieu_mau():
    """
    Tạo dữ liệu mẫu đơn giản với 4 thành phố A, B, C, D.

    Đồ thị vô hướng - hiển thị đầy đủ cả 2 chiều:
    
    Ma trận khoảng cách:
         A   B   C   D
    A [  0  10  15  20 ]
    B [ 10   0  35  25 ]
    C [ 15  35   0  30 ]
    D [ 20  25  30   0 ]
    
    Bảng đầy đủ (12 dòng - để dễ đọc):
    Thành phố | Kết nối đến | Khoảng cách (km)
    -----------------------------------------
    A         | B           | 10
    A         | C           | 15
    A         | D           | 20
    B         | A           | 10
    B         | C           | 35
    B         | D           | 25
    C         | A           | 15
    C         | B           | 35
    C         | D           | 30
    D         | A           | 20
    D         | B           | 25
    D         | C           | 30
    """
    danh_sach_thanh_pho = [
        {"name": "A"},
        {"name": "B"},
        {"name": "C"},
        {"name": "D"},
    ]

    danh_sach_khoang_cach = [
        {"from": "A", "to": "B", "weight": 10},
        {"from": "A", "to": "C", "weight": 15},
        {"from": "A", "to": "D", "weight": 20},
        {"from": "B", "to": "A", "weight": 10},
        {"from": "B", "to": "C", "weight": 35},
        {"from": "B", "to": "D", "weight": 25},
        {"from": "C", "to": "A", "weight": 15},
        {"from": "C", "to": "B", "weight": 35},
        {"from": "C", "to": "D", "weight": 30},
        {"from": "D", "to": "A", "weight": 20},
        {"from": "D", "to": "B", "weight": 25},
        {"from": "D", "to": "C", "weight": 30},
    ]

    return danh_sach_thanh_pho, danh_sach_khoang_cach


app = Flask(__name__)

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/api/solve', methods=['POST'])
def solve_tsp():
    try:
        data = request.get_json()
        
        # Tạo đồ thị từ dữ liệu đầu vào
        do_thi = DoThi()
        
        # Thêm các đỉnh (thành phố)
        danh_sach_thanh_pho = data.get('cities', [])
        for thanh_pho in danh_sach_thanh_pho:
            do_thi.them_dinh(thanh_pho['name'])
        
        # Thêm các cạnh (khoảng cách giữa các thành phố)
        danh_sach_khoang_cach = data.get('distances', [])
        for khoang_cach in danh_sach_khoang_cach:
            do_thi.them_canh(
                khoang_cach['from'],
                khoang_cach['to'],
                khoang_cach['weight'],
            )
        
        # Lấy thành phố xuất phát (nếu có)
        start_city = data.get('start_city', None)
        
        # Giải bài toán TSP bằng thuật toán nhánh cận
        bo_giai = BoGiaiNhanhCanTSP(do_thi)
        ket_qua = bo_giai.giai(start_city=start_city)
        
        return jsonify({
            'success': True,
            'route': ket_qua['route'],
            'total_distance': ket_qua['total_distance'],
            'execution_time': ket_qua['execution_time'],
            'nodes_explored': ket_qua['nodes_explored'],
            'steps': ket_qua['steps'],
            'start_city': ket_qua['start_city'],
        })
    
    except Exception as e:
        return jsonify({
            'success': False,
            'error': str(e)
        }), 400

@app.route('/api/upload', methods=['POST'])
def upload_file():
    try:
        if 'file' not in request.files:
            return jsonify({'error': 'No file uploaded'}), 400
        
        file = request.files['file']
        if file.filename == '':
            return jsonify({'error': 'No file selected'}), 400
        
        if file and file.filename.endswith('.csv'):
            # Hỗ trợ hai định dạng CSV:
            # 1) Hai phần: city ... / from,to,distance ...
            # 2) Ba cột: Thành phố, Kết nối đến, Khoảng cách (km)
            content = file.read().decode('utf-8')
            lines = [line for line in content.splitlines() if line.strip() != '']

            danh_sach_thanh_pho: List[Dict[str, str]] = []
            danh_sach_khoang_cach: List[Dict[str, object]] = []

            if not lines:
                return jsonify({'error': 'File CSV trống'}), 400

            header = lines[0].strip().lower()

            # ---- Trường hợp 2 phần: city / from,to,distance ----
            if header.startswith('city') or header.startswith('thanh pho'):
                # Parse theo định dạng mẫu trong giao diện
                i = 0
                n = len(lines)

                # Đọc phần danh sách thành phố
                if i < n and lines[i].strip().lower().startswith('city'):
                    i += 1
                    while i < n and lines[i].strip() != '':
                        ten_thanh_pho = lines[i].strip()
                        if ten_thanh_pho:
                            danh_sach_thanh_pho.append({'name': ten_thanh_pho})
                        i += 1

                # Bỏ qua dòng trống
                while i < n and lines[i].strip() == '':
                    i += 1

                # Đọc phần khoảng cách
                if i < n and lines[i].strip().lower().startswith('from'):
                    i += 1
                    while i < n:
                        dong = lines[i].strip()
                        i += 1
                        if not dong:
                            continue
                        parts = [p.strip() for p in dong.split(',')]
                        if len(parts) >= 3:
                            try:
                                khoang_cach = float(parts[2])
                            except ValueError:
                                continue
                            danh_sach_khoang_cach.append({
                                'from': parts[0],
                                'to': parts[1],
                                'weight': khoang_cach
                            })

            # ---- Trường hợp 3 cột: thành phố, kết nối đến, khoảng cách ----
            else:
                reader = csv.reader(lines)
                tieu_de = next(reader, None)
                if not tieu_de or len(tieu_de) < 3:
                    return jsonify({'error': 'Định dạng CSV không hợp lệ'}), 400

                # Đọc danh sách cạnh và suy ra danh sách thành phố
                tap_thanh_pho = set()
                for row in reader:
                    if len(row) < 3:
                        continue
                    from_city = row[0].strip()
                    to_city = row[1].strip()
                    try:
                        khoang_cach = float(row[2])
                    except ValueError:
                        continue
                    if from_city and to_city:
                        danh_sach_khoang_cach.append({
                            'from': from_city,
                            'to': to_city,
                            'weight': khoang_cach
                        })
                        tap_thanh_pho.add(from_city)
                        tap_thanh_pho.add(to_city)

                danh_sach_thanh_pho = [{'name': ten} for ten in sorted(tap_thanh_pho)]

            return jsonify({
                'success': True,
                'cities': danh_sach_thanh_pho,
                'distances': danh_sach_khoang_cach
            })
        
        elif file and file.filename.endswith('.json'):
            # Xử lý file JSON
            content = file.read().decode('utf-8')
            data = json.loads(content)
            
            return jsonify({
                'success': True,
                'cities': data.get('cities', []),
                'distances': data.get('distances', [])
            })
        
        else:
            return jsonify({'error': 'Unsupported file format'}), 400
    
    except Exception as e:
        return jsonify({'error': str(e)}), 400

@app.route('/api/sample-data')
def get_sample_data():
    """API endpoint để lấy dữ liệu mẫu"""
    try:
        cities, distances = tao_du_lieu_mau()
        return jsonify({
            'success': True,
            'cities': cities,
            'distances': distances
        })
    except Exception as e:
        return jsonify({
            'success': False,
            'error': str(e)
        }), 400

def open_browser():
    """Tự động mở trình duyệt sau khi Flask khởi động."""
    import socket
    
    # Chờ Flask khởi động hoàn tất (kiểm tra port 5000)
    max_attempts = 30  # Tối đa 15 giây
    for i in range(max_attempts):
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(1)
            result = sock.connect_ex(('localhost', 5000))
            sock.close()
            if result == 0:
                # Flask đã sẵn sàng!
                time.sleep(0.5)  # Chờ thêm chút để chắc chắn
                webbrowser.open('http://localhost:5000')
                break
        except:
            pass
        time.sleep(0.5)  # Chờ 0.5 giây rồi thử lại

if __name__ == '__main__':
    import os
    
    # Chỉ mở browser ở process chính (tránh mở 2 lần do debug mode)
    if os.environ.get('WERKZEUG_RUN_MAIN') != 'true':
        threading.Thread(target=open_browser, daemon=True).start()
        
        print("\n" + "="*60)
        print(" >>> Ung dung dang khoi dong...")
        print(" >>> Trinh duyet se tu dong mo trong giay lat...")
        print(" >>> Dia chi: http://localhost:5000")
        print("="*60 + "\n")
    
    app.run(debug=True, host='0.0.0.0', port=5000)
