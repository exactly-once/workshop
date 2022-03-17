using System.Diagnostics;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.AspNetCore.Mvc;
using Orders.Models;

namespace Orders.Controllers
{
    public class OrdersController : Controller
    {
        readonly ApplicationServices appServices;

        public OrdersController(ApplicationServices appServices)
        {
            this.appServices = appServices;
        }

        [Route("orders/{customerId}")]
        [HttpGet]
        public async Task<IActionResult> Index(string customerId)
        {
            var allOrders = await appServices.GetOrders(customerId);
            return View(allOrders);
        }

        [Route("orders/create/{customerId}")]
        [HttpGet]
        public async Task<IActionResult> Create(string customerId)
        {
            var cartId = OrderIdGenerator.Generate();

            await appServices.CreateCart(customerId, cartId);

            return RedirectToAction("Index", "Cart", new { customerId, cartId });
        }

        [ResponseCache(Duration = 0, Location = ResponseCacheLocation.None, NoStore = true)]
        public IActionResult Error()
        {
            return View(new ErrorViewModel { RequestId = Activity.Current?.Id ?? HttpContext.TraceIdentifier });
        }
    }
}